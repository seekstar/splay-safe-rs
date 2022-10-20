/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

mod tests;

pub use compare::Compare;
use num_traits::{One, Zero};

use core::cmp::Ordering;
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, SubAssign};

pub trait BasicOps {
    #[allow(unused)]
    fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>) {}
    #[allow(unused)]
    fn push_down(&mut self, lc: Option<&mut Self>, rc: Option<&mut Self>) {}
}

pub trait Key<K: Ord> {
    fn key(&self) -> &K;
}

impl<T: Ord> Key<T> for T {
    fn key(&self) -> &T {
        self
    }
}

pub trait Count {
    type CountType;
    fn cnt(&self) -> &Self::CountType;
}

pub trait CountAdd: Count {
    fn cnt_add(&mut self, delta: &Self::CountType);
}

pub trait CountSub: Count {
    fn cnt_sub(&mut self, delta: &Self::CountType);
}

pub trait SubtreeCount: Count {
    type SubtreeCountType;
    fn subtree_count(&self) -> &Self::SubtreeCountType;
}

#[derive(Clone, PartialEq)]
struct Node<T> {
    c: [Option<Box<Node<T>>>; 2],
    // Number of elements in this node
    d: T,
}

impl<T> Node<T> {
    fn new(d: T) -> Node<T> {
        Node { c: [None, None], d }
    }
    // #[inline]
    // fn child_data(&self, side: bool) -> Option<&T> {
    //     self.c[side as usize].as_ref().map(|x| &x.d)
    // }
    // #[inline]
    // fn lc_data(&self) -> Option<&T> {
    //     self.child_data(false)
    // }
    // #[inline]
    // fn rc_data(&self) -> Option<&T> {
    //     self.child_data(true)
    // }
    fn members_mut(
        &mut self,
    ) -> (&mut Option<Box<Node<T>>>, &mut Option<Box<Node<T>>>, &mut T) {
        let (lc, rc) = self.c.split_at_mut(1);
        (&mut lc[0], &mut rc[0], &mut self.d)
    }
}

fn find_smallest_or_largest<T>(
    rt: Option<Box<Node<T>>>,
    is_largest: bool,
    path: &mut Vec<(Box<Node<T>>, bool)>,
) where
    T: BasicOps,
{
    let mut next = rt;
    while let Some(mut cur) = next {
        next = cur.take_child(is_largest);
        path.push((cur, is_largest));
    }
}

impl<T: BasicOps> Node<T> {
    fn push_up(&mut self) {
        // self.d.push_up(self.lc_data(), self.rc_data())
        // We have to access all fields here to make the compiler see partial
        // borrow.
        self.d.push_up(
            self.c[0].as_ref().map(|x| &x.d),
            self.c[1].as_ref().map(|x| &x.d),
        )
    }
    fn push_down(&mut self) {
        let (lc, rc, d) = self.members_mut();
        d.push_down(
            lc.as_mut().map(|x| &mut x.d),
            rc.as_mut().map(|x| &mut x.d),
        );
    }
    fn take_child(&mut self, side: bool) -> Option<Box<Node<T>>> {
        self.push_down();
        self.c[side as usize].take()
    }
    fn set_child(&mut self, side: bool, child: Option<Box<Node<T>>>) {
        self.c[side as usize] = child;
        self.push_up();
    }
    // y is the parent of x
    // Will update y.scnt
    // Dirty: x.scnt, x <-> to
    fn __rotate_up(
        &mut self, // x
        mut y: Box<Node<T>>,
        side_x: bool,
    ) {
        let w = self.c[!side_x as usize].take();
        y.set_child(side_x, w);
        self.c[!side_x as usize] = Some(y);
    }
    // Nodes in path will be updated
    // Dirty: x.scnt, x <-> path[0]
    fn __splay(
        &mut self, // x
        mut path: Vec<(Box<Node<T>>, bool)>,
    ) {
        loop {
            let (mut y, side_x) = match path.pop() {
                Some(elem) => elem,
                None => return,
            };
            let (z, side_y) = match path.pop() {
                Some(elem) => elem,
                None => {
                    self.__rotate_up(y, side_x);
                    return;
                }
            };
            if side_x == side_y {
                y.__rotate_up(z, side_y);
                self.__rotate_up(y, side_x);
            } else {
                self.__rotate_up(y, side_x);
                self.__rotate_up(z, side_y);
            }
        }
    }
    // Nodes from x to path[0] will be updated
    // Dirty: x <-> path[0]
    fn splay(
        &mut self, // x
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        self.__splay(path);
        self.push_up();
    }
    fn find_prev_or_next(
        &mut self,
        is_next: bool,
    ) -> Vec<(Box<Node<T>>, bool)> {
        let mut path = Vec::new();
        let next = self.take_child(is_next);
        find_smallest_or_largest(next, !is_next, &mut path);
        path
    }
}

pub struct Interval<'a, T, S> {
    rt: &'a mut Option<Box<Node<T>>>,
    shared: &'a S,
}

impl<'a, T, S> Interval<'a, T, S> {
    fn new(
        rt: &'a mut Option<Box<Node<T>>>,
        shared: &'a S,
    ) -> Interval<'a, T, S> {
        Interval { rt, shared }
    }
}

impl<'a, T: BasicOps, S> Interval<'a, T, S> {
    fn consume(self) -> &'a mut Option<Box<Node<T>>> {
        self.rt
    }
    // Not tested by OJ
    pub fn delete(&mut self) {
        self.rt.take();
    }
    pub fn root_data(&self) -> Option<&T> {
        self.rt.as_ref().map(|rt| &rt.d)
    }
    // Not tested by OJ
    pub fn collect_data(&self) -> Vec<&T> {
        let mut elems = Vec::new();
        collect_subtree_data(&self.rt, &mut elems);
        elems
    }
    // Return updated or not
    pub fn update_root_data<F>(&mut self, f: F) -> bool
    where
        F: FnOnce(&mut T),
    {
        let root = match self.rt.as_mut() {
            Some(root) => root,
            None => return false,
        };
        f(&mut root.d);
        root.push_up();
        return true;
    }
    fn __rotate_to_root(
        &mut self,
        mut x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        x.splay(path);
        *self.rt = Some(x);
    }
    fn rotate_to_root(
        &mut self,
        mut x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        x.push_down();
        self.__rotate_to_root(x, path);
    }
    /// # Arguments
    /// * ge
    /// 	- false: Find the first node whose value <= key.
    /// 	- true: Find the first node whose value >= key.
    fn path_to_first_le_or_ge<E>(
        &mut self,
        key: &E,
        ge: bool,
    ) -> (Vec<(Box<Node<T>>, bool)>, usize)
    where
        S: Compare<T, E>,
    {
        let mut next = self.rt.take();
        let mut path = Vec::new();
        let mut ans_depth = 0;
        while let Some(mut cur) = next {
            let res = self.shared.compare(&cur.d, key);
            if res == Ordering::Equal {
                path.push((cur, false));
                ans_depth = path.len();
                return (path, ans_depth);
            }
            let side = res == Ordering::Less;
            next = cur.take_child(side);
            path.push((cur, side));
            if side != ge {
                ans_depth = path.len();
            }
        }
        (path, ans_depth)
    }
    fn rotate_ans_to_root(
        &mut self,
        mut path: Vec<(Box<Node<T>>, bool)>,
        ans_depth: usize,
    ) -> bool {
        let (mut prev, _) = match path.pop() {
            Some(prev) => prev,
            None => return false,
        };
        let ans = if ans_depth <= path.len() {
            // prev != ans
            prev.splay(path.split_off(ans_depth));
            let (mut ans, side) = match path.pop() {
                Some(ans) => ans,
                None => {
                    *self.rt = Some(prev);
                    return false;
                }
            };
            ans.c[side as usize] = Some(prev);
            // ans.scnt will be updated by rotate_to_root later.
            ans
        } else {
            // prev is ans
            prev
        };
        self.__rotate_to_root(ans, path);
        return true;
    }
    // If found, then the node will be the root, and return true.
    // Otherwise return false.
    fn find_first_le_or_ge<E>(&mut self, key: &E, ge: bool) -> bool
    where
        S: Compare<T, E>,
    {
        let (path, ans_depth) = self.path_to_first_le_or_ge(key, ge);
        self.rotate_ans_to_root(path, ans_depth)
    }
    fn find_first_le<E>(&mut self, key: &E) -> bool
    where
        S: Compare<T, E>,
    {
        self.find_first_le_or_ge(key, false)
    }
    fn find_first_ge<E>(&mut self, key: &E) -> bool
    where
        S: Compare<T, E>,
    {
        self.find_first_le_or_ge(key, true)
    }

    fn path_to_first_less_or_greater<E, const GT: bool>(
        &mut self,
        key: &E,
    ) -> (Vec<(Box<Node<T>>, bool)>, usize)
    where
        S: Compare<T, E>,
    {
        let mut next = self.rt.take();
        let mut path = Vec::new();
        let mut ans_depth = 0;
        let go_right = if GT { S::compares_le } else { S::compares_lt };
        while let Some(mut cur) = next {
            let side = go_right(self.shared, &cur.d, key);
            next = cur.take_child(side);
            path.push((cur, side));
            if side != GT {
                ans_depth = path.len();
            }
        }
        (path, ans_depth)
    }
    fn find_first_lt_or_gt<E, const GT: bool>(&mut self, key: &E) -> bool
    where
        S: Compare<T, E>,
    {
        let (path, ans_depth) =
            self.path_to_first_less_or_greater::<E, GT>(key);
        self.rotate_ans_to_root(path, ans_depth)
    }
    fn find_first_lt<E>(&mut self, key: &E) -> bool
    where
        S: Compare<T, E>,
    {
        self.find_first_lt_or_gt::<E, false>(key)
    }
    pub fn find_first_gt<E>(&mut self, key: &E) -> bool
    where
        S: Compare<T, E>,
    {
        self.find_first_lt_or_gt::<E, true>(key)
    }

    fn get_interval_lt_or_gt<E>(
        mut self,
        key: &E,
        gt: bool,
    ) -> Interval<'a, T, S>
    where
        S: Compare<T, E>,
    {
        let found = self.find_first_le_or_ge(key, !gt);
        if found {
            let rt = self.rt.as_mut().unwrap();
            Interval::new(&mut rt.c[gt as usize], self.shared)
        } else {
            self
        }
    }
    pub fn get_interval_lt<E>(self, key: &E) -> Interval<'a, T, S>
    where
        S: Compare<T, E>,
    {
        self.get_interval_lt_or_gt(key, false)
    }
    fn get_interval_gt<E>(self, key: &E) -> Interval<'a, T, S>
    where
        S: Compare<T, E>,
    {
        self.get_interval_lt_or_gt(key, true)
    }

    fn get_interval_le_or_ge<E, const GE: bool>(
        mut self,
        key: &E,
    ) -> Interval<'a, T, S>
    where
        S: Compare<T, E>,
    {
        let found = if GE {
            self.find_first_lt(key)
        } else {
            self.find_first_gt(key)
        };
        if found {
            let rt = self.rt.as_mut().unwrap();
            Interval::new(&mut rt.c[GE as usize], self.shared)
        } else {
            self
        }
    }
    fn get_interval_le<E>(self, key: &E) -> Interval<'a, T, S>
    where
        S: Compare<T, E>,
    {
        self.get_interval_le_or_ge::<E, false>(key)
    }
    fn get_interval_ge<E>(self, key: &E) -> Interval<'a, T, S>
    where
        S: Compare<T, E>,
    {
        self.get_interval_le_or_ge::<E, true>(key)
    }
}

impl<'a, T: BasicOps + SubtreeCount, S> Interval<'a, T, S> {
    fn find_kth(&mut self, mut k: T::SubtreeCountType) -> bool
    where
        T::CountType: Copy,
        T::SubtreeCountType: Ord
            + Copy
            + Zero
            + Add<T::CountType, Output = T::SubtreeCountType>
            + SubAssign,
    {
        let mut next = self.rt.take();
        let mut path = Vec::new();
        while let Some(mut cur) = next {
            cur.push_down();
            let lscnt = if let Some(ref lc) = cur.c[0] {
                *lc.d.subtree_count()
            } else {
                T::SubtreeCountType::zero()
            };
            let cur_cnt = *cur.d.cnt();
            if &lscnt < &k && &(lscnt + cur_cnt) >= &k {
                self.__rotate_to_root(cur, path);
                return true;
            }
            let side = lscnt < k;
            if side {
                k -= lscnt + cur_cnt;
            };
            next = cur.c[side as usize].take();
            path.push((cur, side));
        }
        let (x, _) = if let Some(x) = path.pop() {
            x
        } else {
            return false;
        };
        self.__rotate_to_root(x, path);
        return false;
    }
}

pub struct Splay<T, S> {
    root: Option<Box<Node<T>>>,
    shared: S, // Mostly for comparator
}

impl<T, S: Default> Splay<T, S> {
    // use Basic::C as CT;
    pub fn new() -> Splay<T, S> {
        Splay {
            root: None,
            shared: S::default(),
        }
    }
}

impl<T, S> Splay<T, S> {
    pub fn with_shared(shared: S) -> Splay<T, S> {
        Splay { root: None, shared }
    }
}

fn build<T: BasicOps, E, F>(
    v: &mut Vec<E>,
    start: usize,
    constructor: F,
) -> Option<Box<Node<T>>>
where
    F: Copy + Fn(E) -> T,
{
    let len = v.len() - start;
    if len == 0 {
        return None;
    }
    let mid = start + len / 2;
    let rc = build(v, mid + 1, constructor);
    debug_assert_eq!(mid + 1, v.len());
    let e = v.pop().unwrap();
    let lc = build(v, start, constructor);
    let mut node = Box::new(Node {
        d: constructor(e),
        c: [lc, rc],
    });
    node.push_up();
    Some(node)
}

impl<T: BasicOps, S> Splay<T, S> {
    fn from_with_constructor_shared<E, F>(
        mut v: Vec<E>,
        constructor: F,
        s: S,
    ) -> Splay<T, S>
    where
        F: Copy + Fn(E) -> T,
    {
        let root = build(&mut v, 0, constructor);
        debug_assert!(v.is_empty());
        Splay { root, shared: s }
    }
    pub fn from_with_shared<E>(v: Vec<E>, s: S) -> Splay<T, S>
    where
        T: From<E>,
    {
        Self::from_with_constructor_shared(v, T::from, s)
    }
}

impl<T: BasicOps, S: Default> Splay<T, S> {
    pub fn from_with_constructor<E, F>(v: Vec<E>, constructor: F) -> Splay<T, S>
    where
        F: Copy + Fn(E) -> T,
    {
        Self::from_with_constructor_shared(v, constructor, S::default())
    }
}

impl<E, T: BasicOps + From<E>, S: Default> From<Vec<E>> for Splay<T, S> {
    fn from(v: Vec<E>) -> Splay<T, S> {
        Splay::from_with_constructor(v, T::from)
    }
}

fn collect_non_empty_subtree_data<'a, T>(
    rt: &'a Box<Node<T>>,
    elems: &mut Vec<&'a T>,
) {
    collect_subtree_data(&rt.c[0], elems);
    elems.push(&rt.d);
    collect_subtree_data(&rt.c[1], elems);
}
fn collect_subtree_data<'a, T>(
    rt: &'a Option<Box<Node<T>>>,
    elems: &mut Vec<&'a T>,
) {
    if let Some(rt) = rt {
        collect_non_empty_subtree_data(rt, elems);
    }
}

fn take_non_empty_subtree_data<T>(mut rt: Box<Node<T>>, elems: &mut Vec<T>)
where
    T: BasicOps,
{
    rt.push_down();
    take_subtree_data(rt.c[0].take(), elems);
    elems.push(rt.d);
    take_subtree_data(rt.c[1].take(), elems);
}
fn take_subtree_data<T>(rt: Option<Box<Node<T>>>, elems: &mut Vec<T>)
where
    T: BasicOps,
{
    if let Some(rt) = rt {
        take_non_empty_subtree_data(rt, elems);
    }
}

impl<T: BasicOps, S> Splay<T, S> {
    pub fn to_interval(&mut self) -> Interval<T, S> {
        Interval::new(&mut self.root, &self.shared)
    }
    fn __rotate_to_root(
        &mut self,
        x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        self.to_interval().__rotate_to_root(x, path);
    }
    fn rotate_to_root(
        &mut self,
        x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        self.to_interval().rotate_to_root(x, path);
    }

    pub fn root_data(&self) -> Option<&T> {
        self.root.as_ref().map(|root| &root.d)
    }
    // Return updated or not
    pub fn update_root_data<F>(&mut self, f: F) -> bool
    where
        F: FnOnce(&mut T),
    {
        self.to_interval().update_root_data(f)
    }
    fn take_root(&mut self) -> Option<Box<Node<T>>> {
        let mut root = match self.root.take() {
            Some(root) => root,
            None => return None,
        };
        let mut path = root.find_prev_or_next(false);
        let mut x = match path.pop() {
            Some((x, _)) => x,
            None => {
                self.root = root.take_child(true);
                return Some(root);
            }
        };
        x.__splay(path);
        x.set_child(true, root.take_child(true));
        self.root = Some(x);
        return Some(root);
    }
    fn delete_root(&mut self) -> bool {
        self.take_root().is_some()
    }
    fn pop_root(&mut self) -> Option<T> {
        self.take_root().map(|rt| rt.d)
    }
    pub fn deref_root(&mut self) -> bool
    where
        T: CountSub,
        T::CountType: Zero + One,
    {
        let root = match self.root.as_mut() {
            Some(root) => root,
            None => return false,
        };
        root.d.cnt_sub(&T::CountType::one());
        if root.d.cnt().is_zero() {
            self.delete_root()
        } else {
            root.push_up();
            true
        }
    }

    // If the key does not already exist, then return the path to the insert
    // location.
    // If the key already exists, then return None. The existing key will be
    // the root.
    fn find_insert_location<E>(
        &mut self,
        key: &E,
    ) -> Option<Vec<(Box<Node<T>>, bool)>>
    where
        S: Compare<T, E>,
    {
        let mut path = Vec::new();
        let mut cur = match self.root.take() {
            Some(root) => root,
            None => {
                return Some(path);
            }
        };
        loop {
            let res = self.shared.compare(&cur.d, key);
            if res == Ordering::Equal {
                self.rotate_to_root(cur, path);
                return None;
            }
            let side = res == Ordering::Less;
            let next = cur.take_child(side);
            path.push((cur, side));
            if let Some(nex) = next {
                cur = nex
            } else {
                return Some(path);
            }
        }
    }
    // If the key already exists, then make it the root and return false.
    // Otherwise, construct the data with `func`, insert the node, rotate
    // the new node to root, and return true.
    // Return whether the insertion is successful or not.
    pub fn insert_owned_key_with_func<E, F>(&mut self, key: E, func: F) -> bool
    where
        S: Compare<T, E>,
        F: FnOnce(E) -> T,
    {
        let path = match self.find_insert_location(&key) {
            Some(path) => path,
            None => return false,
        };
        let node = Box::new(Node::new(func(key)));
        self.__rotate_to_root(node, path);
        return true;
    }
    pub fn insert_owned_key<E>(&mut self, key: E) -> bool
    where
        S: Compare<T, E>,
        T: From<E>,
    {
        self.insert_owned_key_with_func(key, |key| T::from(key))
    }
    pub fn insert_owned_key_or_inc_cnt<E>(&mut self, key: E)
    where
        S: Compare<T, E>,
        T: From<E> + CountAdd,
        T::CountType: One,
    {
        if self.insert_owned_key(key) == false {
            self.update_root_data(|d| d.cnt_add(&T::CountType::one()));
        }
    }

    pub fn find<E>(&mut self, key: &E) -> bool
    where
        S: Compare<T, E>,
    {
        let mut next = self.root.take();
        let mut path = Vec::new();
        while let Some(mut cur) = next {
            let res = self.shared.compare(&cur.d, key);
            if res == Ordering::Equal {
                self.rotate_to_root(cur, path);
                return true;
            }
            let side = res == Ordering::Less;
            next = cur.take_child(side);
            path.push((cur, side));
        }
        // Not found. Rotate the last accessed node to root to maintain
        // complexity.
        let prev = match path.pop() {
            Some((prev, _)) => prev,
            None => return false,
        };
        self.__rotate_to_root(prev, path);
        return false;
    }
    pub fn delete<E>(&mut self, key: &E) -> bool
    where
        S: Compare<T, E>,
    {
        let ret = self.find(key);
        if ret {
            self.take_root();
        }
        return ret;
    }

    fn find_smallest_or_largest(&mut self, is_largest: bool) {
        let mut path = Vec::new();
        find_smallest_or_largest(self.root.take(), is_largest, &mut path);
        let x = match path.pop() {
            Some((x, _)) => x,
            None => return,
        };
        self.__rotate_to_root(x, path);
    }
    pub fn pop_smallest(&mut self) -> Option<T> {
        self.find_smallest_or_largest(false);
        self.pop_root()
    }
    pub fn pop_largest(&mut self) -> Option<T> {
        self.find_smallest_or_largest(true);
        self.pop_root()
    }
    fn query_smallest_or_largest(&mut self, is_largest: bool) -> Option<&T> {
        self.find_smallest_or_largest(is_largest);
        self.root_data()
    }
    pub fn query_smallest(&mut self) -> Option<&T> {
        self.query_smallest_or_largest(false)
    }

    pub fn find_first_le<E>(&mut self, key: &E) -> bool
    where
        S: Compare<T, E>,
    {
        self.to_interval().find_first_le(key)
    }
    pub fn find_first_ge<E>(&mut self, key: &E) -> bool
    where
        S: Compare<T, E>,
    {
        self.to_interval().find_first_ge(key)
    }

    // The remaining smallest will be the root.
    pub fn del_smaller<E>(&mut self, key: &E)
    where
        S: Compare<T, E>,
    {
        let (mut path, ans_depth) =
            self.to_interval().path_to_first_le_or_ge(key, true);
        path.truncate(ans_depth);
        let mut ans = match path.pop() {
            Some((ans, _)) => ans,
            None => return,
        };
        ans.__splay(path);
        ans.set_child(false, None);
        self.root = Some(ans);
    }

    fn get_open_interval<L, R>(&mut self, left: &L, right: &R) -> Interval<T, S>
    where
        S: Compare<T, L> + Compare<T, R>,
    {
        self.to_interval()
            .get_interval_gt(left)
            .get_interval_lt(right)
    }
    pub fn get_closed_interval<L, R>(
        &mut self,
        left: &L,
        right: &R,
    ) -> Interval<T, S>
    where
        S: Compare<T, L> + Compare<T, R>,
    {
        self.to_interval()
            .get_interval_ge(left)
            .get_interval_le(right)
    }

    pub fn query_in_open_interval<L, R>(
        &mut self,
        left: &L,
        right: &R,
    ) -> Option<&T>
    where
        S: Compare<T, L> + Compare<T, R>,
    {
        let interval = self.get_open_interval(left, right);
        interval.consume().as_ref().map(|x| &x.d)
    }

    /// Warning: This function does not perform push_down.
    pub fn collect_data(&self) -> Vec<&T> {
        let mut elems = Vec::new();
        collect_subtree_data(&self.root, &mut elems);
        elems
    }
    pub fn take_all_data(&mut self) -> Vec<T> {
        let mut elems = Vec::new();
        take_subtree_data(self.root.take(), &mut elems);
        elems
    }
}

impl<T: BasicOps + SubtreeCount, S> Splay<T, S> {
    pub fn size(&self) -> T::SubtreeCountType
    where
        T::SubtreeCountType: Zero + Copy,
    {
        match self.root {
            Some(ref root) => *root.d.subtree_count(),
            None => T::SubtreeCountType::zero(),
        }
    }

    // If found, then the node will be the root, and return true.
    // If not found, then the last accessed node will be the root, and return
    // false.
    pub fn find_kth<'a>(&mut self, k: T::SubtreeCountType) -> bool
    where
        T::CountType: Copy,
        T::SubtreeCountType: Ord
            + Copy
            + Zero
            + Add<T::CountType, Output = T::SubtreeCountType>
            + SubAssign,
    {
        self.to_interval().find_kth(k)
    }

    fn check_sanity_subtree<'a>(&self, rt: &Box<Node<T>>)
    where
        T::CountType: Copy,
        T::SubtreeCountType:
            std::fmt::Debug + From<T::CountType> + AddAssign + Eq + Copy,
    {
        let mut scnt = T::SubtreeCountType::from(*rt.d.cnt());
        if let Some(ref c) = rt.c[0] {
            scnt += *c.d.subtree_count();
            self.check_sanity_subtree(c);
        }
        if let Some(ref c) = rt.c[1] {
            scnt += *c.d.subtree_count();
            self.check_sanity_subtree(c);
        }
        assert_eq!(scnt, *rt.d.subtree_count());
    }
    // Only for DEBUG
    pub fn check_sanity(&self)
    where
        T::CountType: Copy,
        T::SubtreeCountType:
            std::fmt::Debug + From<T::CountType> + AddAssign + Eq + Copy,
    {
        if let Some(ref root) = self.root {
            self.check_sanity_subtree(root);
        }
    }
}

fn __print_subtree_non_empty<T>(rt: &Node<T>, str: &mut String)
where
    T: BasicOps + std::fmt::Display,
{
    let ori_len = str.len();
    let node = format!("{}", rt.d);
    let len = node.len();
    print!("{}", node);
    print!("---");
    // str.push_str(&String::from_iter(std::iter::repeat(' ').take(len)));
    str.push_str(&std::iter::repeat(' ').take(len).collect::<String>());
    str.push_str(" | ");
    __print_subtree(&rt.c[0], str);
    println!("{}", str);
    let len = str.len();
    unsafe {
        str.as_bytes_mut()[len - 1] = b'-';
        str.as_bytes_mut()[len - 2] = b'-';
    }
    print!("{}", str);

    unsafe {
        str.as_bytes_mut()[len - 1] = b' ';
        str.as_bytes_mut()[len - 2] = b' ';
    }
    __print_subtree(&rt.c[1], str);

    str.truncate(ori_len);
}
fn __print_subtree<T>(rt: &Option<Box<Node<T>>>, str: &mut String)
where
    T: BasicOps + std::fmt::Display,
{
    if let Some(node) = rt {
        __print_subtree_non_empty(node, str);
    } else {
        println!("/\\");
    }
}
fn print_subtree<T>(rt: &Option<Box<Node<T>>>)
where
    T: BasicOps + std::fmt::Display,
{
    __print_subtree(rt, &mut String::new());
}

impl<T: BasicOps + std::fmt::Display, S> Splay<T, S> {
    pub fn print_tree(&self) {
        print_subtree(&self.root);
    }
}

pub struct KeyComparator<K>(PhantomData<K>);

impl<T> Default for KeyComparator<T> {
    fn default() -> Self {
        KeyComparator(PhantomData::default())
    }
}

impl<K: Ord, L: Key<K>, R: Key<K>> Compare<L, R> for KeyComparator<K> {
    fn compare(&self, l: &L, r: &R) -> Ordering {
        l.key().cmp(r.key())
    }
}

pub type SplayWithKey<K, T> = Splay<T, KeyComparator<K>>;

// Example
struct RankTreeData<T: Ord> {
    key: T,
    cnt: u32,
    scnt: u32,
}

impl<T: Ord> BasicOps for RankTreeData<T> {
    fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>) {
        self.scnt = self.cnt;
        if let Some(d) = lc {
            self.scnt += d.scnt;
        }
        if let Some(d) = rc {
            self.scnt += d.scnt;
        }
    }
}

impl<T: Ord> Key<T> for RankTreeData<T> {
    fn key(&self) -> &T {
        &self.key
    }
}

impl<T: Ord> From<T> for RankTreeData<T> {
    fn from(key: T) -> Self {
        RankTreeData {
            key,
            cnt: 1,
            scnt: 1,
        }
    }
}

impl<T: Ord> Count for RankTreeData<T> {
    type CountType = u32;
    fn cnt(&self) -> &Self::CountType {
        &self.cnt
    }
}

impl<T: Ord> CountAdd for RankTreeData<T> {
    fn cnt_add(&mut self, delta: &Self::CountType) {
        self.cnt += delta;
    }
}

impl<T: Ord> SubtreeCount for RankTreeData<T> {
    type SubtreeCountType = u32;
    fn subtree_count(&self) -> &Self::SubtreeCountType {
        &self.scnt
    }
}

impl<T: Ord + std::fmt::Display> std::fmt::Display for RankTreeData<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}*{}", self.key, self.cnt)
    }
}

pub struct RankTree<T: Ord> {
    rep: SplayWithKey<T, RankTreeData<T>>,
}

impl<T: Ord> RankTree<T> {
    pub fn new() -> RankTree<T> {
        RankTree { rep: Splay::new() }
    }
}

impl<T: Ord + Key<T>> RankTree<T> {
    pub fn size(&self) -> u32 {
        self.rep.size()
    }
    pub fn root_key(&self) -> Option<&T> {
        self.rep.root_data().map(|d| &d.key)
    }
    pub fn insert(&mut self, key: T) {
        self.rep.insert_owned_key_or_inc_cnt(key);
    }
    pub fn find(&mut self, key: &T) -> bool {
        self.rep.find(key)
    }
    pub fn delete(&mut self, key: &T) -> bool {
        self.rep.delete(key)
    }
    pub fn find_first_le(&mut self, key: &T) -> bool {
        self.rep.find_first_le(key)
    }
    pub fn find_first_ge(&mut self, key: &T) -> bool {
        self.rep.find_first_ge(key)
    }
    // The remaining smallest will be the root.
    pub fn del_smaller(&mut self, key: &T) {
        self.rep.del_smaller(key)
    }
    pub fn query_kth(&mut self, k: u32) -> Option<&T> {
        if self.rep.find_kth(k) {
            self.root_key()
        } else {
            None
        }
    }
    pub fn check_sanity(&self) {
        self.rep.check_sanity()
    }
}

impl<T: Ord + std::fmt::Display> RankTree<T> {
    pub fn print_tree(&self) {
        self.rep.print_tree()
    }
}
