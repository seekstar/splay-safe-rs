/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

mod tests;

pub use compare::Compare;
use compare::Natural;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};

use core::cmp::Ordering;
use core::ops::{Add, AddAssign, SubAssign};
use core::ops::{Bound, RangeBounds};
use std::fmt::Display;

pub trait BasicOps {
    #[allow(unused)]
    fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>) {}
    #[allow(unused)]
    fn push_down(&mut self, lc: Option<&mut Self>, rc: Option<&mut Self>) {}
}
impl BasicOps for () {}

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

pub struct Range<'a, T> {
    rt: &'a mut Option<Box<Node<T>>>,
}

impl<'a, T> Range<'a, T> {
    fn new(rt: &'a mut Option<Box<Node<T>>>) -> Self {
        Range { rt }
    }
}

enum Direction {
    Left,
    Stop,
    Right,
}
impl<'a, T: BasicOps> Range<'a, T> {
    // Not tested by OJ
    pub fn delete(&mut self) {
        self.rt.take();
    }
    fn root_data(&self) -> Option<&T> {
        self.rt.as_ref().map(|rt| &rt.d)
    }
    /// Warning: This function does not perform push_down.
    pub fn collect_data(&self) -> Vec<&T> {
        let mut elems = Vec::new();
        collect_subtree_data(&self.rt, &mut elems);
        elems
    }
    pub fn take_all_data(self) -> Vec<T> {
        let mut elems = Vec::new();
        take_subtree_data(self.rt.take(), &mut elems);
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

    fn walk<F: FnMut(&Node<T>) -> Direction>(
        &mut self,
        mut where_to_go: F,
    ) -> Option<Vec<(Box<Node<T>>, bool)>> {
        let mut path = Vec::new();
        let mut cur = match self.rt.take() {
            Some(rt) => rt,
            None => return Some(path),
        };
        loop {
            let side = match where_to_go(&cur) {
                Direction::Stop => {
                    self.rotate_to_root(cur, path);
                    return None;
                }
                Direction::Left => false,
                Direction::Right => true,
            };
            let next = cur.take_child(side);
            path.push((cur, side));
            if let Some(nex) = next {
                cur = nex
            } else {
                return Some(path);
            }
        }
    }
}

pub struct Splay<T> {
    root: Option<Box<Node<T>>>,
}

impl<T> Splay<T> {
    // use Basic::C as CT;
    pub fn new() -> Splay<T> {
        Splay { root: None }
    }
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
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

impl<T: BasicOps> Splay<T> {
    pub fn from_with_constructor<E, F>(
        mut v: Vec<E>,
        constructor: F,
    ) -> Splay<T>
    where
        F: Copy + Fn(E) -> T,
    {
        let root = build(&mut v, 0, constructor);
        debug_assert!(v.is_empty());
        Splay { root }
    }
}

impl<E, T: BasicOps + From<E>> From<Vec<E>> for Splay<T> {
    fn from(v: Vec<E>) -> Splay<T> {
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

impl<T: BasicOps> Splay<T> {
    pub fn to_range(&mut self) -> Range<T> {
        Range::new(&mut self.root)
    }
    fn __rotate_to_root(
        &mut self,
        x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        self.to_range().__rotate_to_root(x, path);
    }
    fn rotate_to_root(
        &mut self,
        x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        self.to_range().rotate_to_root(x, path);
    }

    pub fn root_data(&self) -> Option<&T> {
        self.root.as_ref().map(|root| &root.d)
    }
    // Return updated or not
    pub fn update_root_data<F>(&mut self, f: F) -> bool
    where
        F: FnOnce(&mut T),
    {
        self.to_range().update_root_data(f)
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
    fn collect_data(&self) -> Vec<&T> {
        let mut elems = Vec::new();
        collect_subtree_data(&self.root, &mut elems);
        elems
    }
}

pub trait Count: BasicOps {
    type CountType;
    fn cnt(&self) -> &Self::CountType;
}

pub trait CountAdd: Count {
    fn cnt_add(&mut self, delta: &Self::CountType);
}

pub trait CountSub: Count {
    fn cnt_sub(&mut self, delta: &Self::CountType);
}
pub trait SubtreeCount: BasicOps {
    type SubtreeCountType;
    fn subtree_count(&self) -> &Self::SubtreeCountType;
}

impl<T: CountSub> Splay<T> {
    fn deref_root(&mut self) -> bool
    where
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
}

impl<'a, T: SubtreeCount> Range<'a, T> {
    /// If T implements Count, then Count::cnt() should always return 1.
    /// We can't enforce this with the compiler because currently we can't
    /// define a trait CountIsOne : Count and override the "cnt" method of
    /// trait Count
    fn find_insert_location_by_index(
        &mut self,
        // Starts from zero
        mut index: T::SubtreeCountType,
    ) -> Option<Vec<(Box<Node<T>>, bool)>>
    where
        T::SubtreeCountType:
            Ord + for<'b> SubAssign<&'b T::SubtreeCountType> + Zero + One,
    {
        let zero = T::SubtreeCountType::zero();
        self.walk(|node| {
            assert!(&index <= node.d.subtree_count());
            let lscnt =
                node.c[0].as_ref().map_or(&zero, |lc| lc.d.subtree_count());
            if &index <= lscnt {
                Direction::Left
            } else {
                index -= lscnt;
                index -= &T::SubtreeCountType::one();
                Direction::Right
            }
        })
    }
    fn insert_at_index(&mut self, index: T::SubtreeCountType, data: T)
    where
        T::SubtreeCountType:
            Ord + for<'b> SubAssign<&'b T::SubtreeCountType> + Zero + One,
    {
        let path = match self.find_insert_location_by_index(index) {
            Some(path) => path,
            None => unreachable!(),
        };
        let node = Box::new(Node::new(data));
        self.__rotate_to_root(node, path);
    }
    fn splay_kth(&mut self, mut k: T::SubtreeCountType) -> bool
    where
        T::SubtreeCountType: Ord + Copy + Zero + Add + SubAssign,
    {
        let mut next = self.rt.take();
        let mut path = Vec::new();
        while let Some(mut cur) = next {
            cur.push_down();
            let lscnt =
                cur.c[0].as_ref().map_or(T::SubtreeCountType::zero(), |lc| {
                    *lc.d.subtree_count()
                });
            let rscnt =
                cur.c[1].as_ref().map_or(T::SubtreeCountType::zero(), |rc| {
                    *rc.d.subtree_count()
                });
            // TODO: Introduce "Sub" trait requirement in the next version with breaking changes.
            let mut ls_or_cur_cnt = *cur.d.subtree_count();
            ls_or_cur_cnt -= rscnt;
            if &lscnt < &k && ls_or_cur_cnt >= k {
                self.__rotate_to_root(cur, path);
                return true;
            }
            let side = lscnt < k;
            if side {
                k -= ls_or_cur_cnt;
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

impl<T: SubtreeCount> Splay<T> {
    pub fn size(&self) -> T::SubtreeCountType
    where
        T::SubtreeCountType: Zero + Copy,
    {
        match self.root {
            Some(ref root) => *root.d.subtree_count(),
            None => T::SubtreeCountType::zero(),
        }
    }
    pub fn insert_at_index(&mut self, index: T::SubtreeCountType, data: T)
    where
        T::SubtreeCountType:
            Ord + for<'a> SubAssign<&'a T::SubtreeCountType> + Zero + One,
    {
        self.to_range().insert_at_index(index, data)
    }

    /// If found, then the node will be the root, and return true.
    ///
    /// If not found, then the last accessed node will be the root, and return
    /// false.
    pub fn splay_kth<'a>(&mut self, k: T::SubtreeCountType) -> bool
    where
        T::SubtreeCountType: Ord + Copy + Zero + Add + SubAssign,
    {
        self.to_range().splay_kth(k)
    }
}

impl<T: Count + SubtreeCount> Splay<T> {
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

fn __print_subtree_non_empty<T, F>(
    rt: &Node<T>,
    str: &mut String,
    data_to_string: F,
) where
    T: BasicOps,
    F: Fn(&T) -> String + Clone,
{
    let ori_len = str.len();
    let node = data_to_string(&rt.d);
    let len = node.len();
    print!("{}", node);
    print!("---");
    // str.push_str(&String::from_iter(std::iter::repeat(' ').take(len)));
    str.push_str(&std::iter::repeat(' ').take(len).collect::<String>());
    str.push_str(" | ");
    __print_subtree(&rt.c[0], str, data_to_string.clone());
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
    __print_subtree(&rt.c[1], str, data_to_string);

    str.truncate(ori_len);
}
fn __print_subtree<T, F>(
    rt: &Option<Box<Node<T>>>,
    str: &mut String,
    data_to_string: F,
) where
    T: BasicOps,
    F: Fn(&T) -> String + Clone,
{
    if let Some(node) = rt {
        __print_subtree_non_empty(node, str, data_to_string);
    } else {
        println!("/\\");
    }
}
fn print_subtree<T, F>(rt: &Option<Box<Node<T>>>, data_to_string: F)
where
    T: BasicOps,
    F: Fn(&T) -> String + Clone,
{
    __print_subtree(rt, &mut String::new(), data_to_string);
}

impl<T: BasicOps> Splay<T> {
    pub fn print_tree_with<F>(&self, data_to_string: F)
    where
        F: Fn(&T) -> String + Clone,
    {
        print_subtree(&self.root, data_to_string);
    }
}
fn default_data_to_string<T>(data: &T) -> String
where
    T: Display,
{
    format!("{}", data)
}
impl<T: BasicOps + Display> Splay<T> {
    pub fn print_tree(&self) {
        self.print_tree_with(default_data_to_string);
    }
}

pub struct KeyMutValue<'a, K: Ord, V: BasicOpsWithKey<K>> {
    pub key: &'a K,
    pub value: &'a mut V,
}
pub trait BasicOpsWithKey<K: Ord>: Sized {
    #[allow(unused)]
    fn push_down<'a, 'b>(
        &mut self,
        k: &K,
        lc: Option<KeyMutValue<'a, K, Self>>,
        rc: Option<KeyMutValue<'b, K, Self>>,
    ) where
        Self: Sized,
    {
    }
    #[allow(unused)]
    fn push_up(
        &mut self,
        k: &K,
        lc: Option<&KeyValue<K, Self>>,
        rc: Option<&KeyValue<K, Self>>,
    ) {
    }
}
impl<K: Ord, V: BasicOps> BasicOpsWithKey<K> for V {
    fn push_down<'a, 'b>(
        &mut self,
        _k: &K,
        lc: Option<KeyMutValue<'a, K, Self>>,
        rc: Option<KeyMutValue<'b, K, Self>>,
    ) where
        Self: Sized,
    {
        <Self as BasicOps>::push_down(
            self,
            lc.map(|kv| kv.value),
            rc.map(|kv| kv.value),
        )
    }
    fn push_up(
        &mut self,
        _k: &K,
        lc: Option<&KeyValue<K, Self>>,
        rc: Option<&KeyValue<K, Self>>,
    ) {
        <Self as BasicOps>::push_up(
            self,
            lc.map(|kv| &kv.value),
            rc.map(|kv| &kv.value),
        )
    }
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct KeyValue<K: Ord, V: BasicOpsWithKey<K>> {
    pub key: K,
    pub value: V,
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>> From<&'a mut KeyValue<K, V>>
    for KeyMutValue<'a, K, V>
{
    fn from(kv: &'a mut KeyValue<K, V>) -> Self {
        Self {
            key: &kv.key,
            value: &mut kv.value,
        }
    }
}
impl<K: Ord, V: BasicOpsWithKey<K>> BasicOps for KeyValue<K, V> {
    fn push_down(&mut self, lc: Option<&mut Self>, rc: Option<&mut Self>) {
        self.value.push_down(
            &self.key,
            lc.map(|kv| kv.into()),
            rc.map(|kv| kv.into()),
        )
    }
    fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>) {
        self.value.push_up(&self.key, lc, rc)
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + Count> Count for KeyValue<K, V> {
    type CountType = V::CountType;
    fn cnt(&self) -> &Self::CountType {
        self.value.cnt()
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + CountSub> CountSub for KeyValue<K, V> {
    fn cnt_sub(&mut self, delta: &Self::CountType) {
        self.value.cnt_sub(delta)
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + SubtreeCount> SubtreeCount
    for KeyValue<K, V>
{
    type SubtreeCountType = V::SubtreeCountType;
    fn subtree_count(&self) -> &Self::SubtreeCountType {
        self.value.subtree_count()
    }
}

pub struct KeyRange<'a, K: Ord, V: BasicOpsWithKey<K> = (), C = Natural<K>> {
    range: Range<'a, KeyValue<K, V>>,
    comparator: &'a C,
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>, C> KeyRange<'a, K, V, C> {
    fn new(
        rt: &'a mut Option<Box<Node<KeyValue<K, V>>>>,
        comparator: &'a C,
    ) -> Self {
        KeyRange {
            range: Range::new(rt),
            comparator,
        }
    }
    pub fn root_data(&self) -> Option<&KeyValue<K, V>> {
        self.range.root_data()
    }
    pub fn collect_data(&self) -> Vec<&KeyValue<K, V>> {
        self.range.collect_data()
    }
    pub fn take_all_data(self) -> Vec<KeyValue<K, V>> {
        self.range.take_all_data()
    }

    /// # Arguments
    /// * ge
    /// 	- false: Find the first node whose value <= key.
    /// 	- true: Find the first node whose value >= key.
    fn path_to_first_le_or_ge<E>(
        &mut self,
        key: &E,
        ge: bool,
    ) -> (Vec<(Box<Node<KeyValue<K, V>>>, bool)>, usize)
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let mut next = self.range.rt.take();
        let mut path = Vec::new();
        let mut ans_depth = 0;
        while let Some(mut cur) = next {
            let res = self.comparator.compare(&cur.d.key, key);
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
    // If found, then the node will be the root, and return true.
    // Otherwise return false.
    fn splay_first_le_or_ge<E>(&mut self, key: &E, ge: bool) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let (path, ans_depth) = self.path_to_first_le_or_ge(key, ge);
        self.range.rotate_ans_to_root(path, ans_depth)
    }
    fn splay_first_le<E>(&mut self, key: &E) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.splay_first_le_or_ge(key, false)
    }
    pub fn splay_first_ge<E>(&mut self, key: &E) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.splay_first_le_or_ge(key, true)
    }

    fn path_to_first_less_or_greater<E, const GT: bool>(
        &mut self,
        key: &E,
    ) -> (Vec<(Box<Node<KeyValue<K, V>>>, bool)>, usize)
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let mut next = self.range.rt.take();
        let mut path = Vec::new();
        let mut ans_depth = 0;
        let go_right = if GT { C::compares_le } else { C::compares_lt };
        while let Some(mut cur) = next {
            let side = go_right(&self.comparator, &cur.d.key, key);
            next = cur.take_child(side);
            path.push((cur, side));
            if side != GT {
                ans_depth = path.len();
            }
        }
        (path, ans_depth)
    }
    fn splay_first_lt_or_gt<E, const GT: bool>(&mut self, key: &E) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let (path, ans_depth) =
            self.path_to_first_less_or_greater::<E, GT>(key);
        self.range.rotate_ans_to_root(path, ans_depth)
    }
    fn splay_first_lt<E>(&mut self, key: &E) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.splay_first_lt_or_gt::<E, false>(key)
    }
    pub fn splay_first_gt<E>(&mut self, key: &E) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.splay_first_lt_or_gt::<E, true>(key)
    }

    fn lt_or_gt<E>(mut self, key: &E, gt: bool) -> Self
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let found = self.splay_first_le_or_ge(key, !gt);
        if found {
            let rt = self.range.rt.as_mut().unwrap();
            KeyRange::new(&mut rt.c[gt as usize], self.comparator)
        } else {
            self
        }
    }
    pub fn lt<E>(self, key: &E) -> Self
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.lt_or_gt(key, false)
    }
    fn gt<E>(self, key: &E) -> Self
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.lt_or_gt(key, true)
    }

    fn le_or_ge<E, const GE: bool>(mut self, key: &E) -> Self
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let found = if GE {
            self.splay_first_lt(key)
        } else {
            self.splay_first_gt(key)
        };
        if found {
            let rt = self.range.rt.as_mut().unwrap();
            Self::new(&mut rt.c[GE as usize], &self.comparator)
        } else {
            self
        }
    }
    fn le<E>(self, key: &E) -> Self
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.le_or_ge::<E, false>(key)
    }
    fn ge<E>(self, key: &E) -> Self
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.le_or_ge::<E, true>(key)
    }
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>, C> KeyRange<'a, K, V, C> {
    // Return updated or not
    pub fn update_root_value<F>(&mut self, f: F) -> bool
    where
        F: FnOnce(&K, &mut V),
    {
        let root = match self.range.rt.as_mut() {
            Some(root) => root,
            None => return false,
        };
        f(&root.d.key, &mut root.d.value);
        root.push_up();
        return true;
    }
}

pub struct SplayWithKey<K: Ord, V: BasicOpsWithKey<K> = (), C = Natural<K>> {
    splay: Splay<KeyValue<K, V>>,
    comparator: C,
}
impl<K: Ord, V: BasicOpsWithKey<K>, C: Compare<K, K>> SplayWithKey<K, V, C> {
    pub fn with_splay_comparator(
        splay: Splay<KeyValue<K, V>>,
        comparator: C,
    ) -> Self {
        Self { splay, comparator }
    }
    pub fn with_comparator(comparator: C) -> Self {
        Self {
            splay: Splay::new(),
            comparator,
        }
    }
    fn new() -> Self
    where
        C: Default,
    {
        Self::with_comparator(C::default())
    }
    pub fn construct_with_comparator<E, F>(
        v: Vec<E>,
        comparator: C,
        constructor: F,
    ) -> Self
    where
        F: Copy + Fn(E) -> KeyValue<K, V>,
    {
        Self {
            splay: Splay::from_with_constructor(v, constructor),
            comparator,
        }
    }
    pub fn construct<E, F>(v: Vec<E>, constructor: F) -> Self
    where
        C: Default,
        F: Copy + Fn(E) -> KeyValue<K, V>,
    {
        Self::construct_with_comparator(v, C::default(), constructor)
    }

    fn to_range(&mut self) -> KeyRange<K, V, C> {
        KeyRange {
            range: self.splay.to_range(),
            comparator: &self.comparator,
        }
    }
    pub fn root_data(&self) -> Option<&KeyValue<K, V>> {
        self.splay.root_data()
    }

    // If the key does not already exist, then return the path to the insert
    // location.
    // If the key already exists, then return None. The existing key will be
    // the root.
    fn find_insert_location<E>(
        &mut self,
        key: &E,
    ) -> Option<Vec<(Box<Node<KeyValue<K, V>>>, bool)>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.splay.to_range().walk(|node| {
            match self.comparator.compare(&node.d.key, key) {
                Ordering::Equal => Direction::Stop,
                Ordering::Less => Direction::Right,
                Ordering::Greater => Direction::Left,
            }
        })
    }
    // If the key already exists, then make it the root and return false.
    // Otherwise, construct the data with `func`, insert the node, rotate
    // the new node to root, and return true.
    // Return whether the insertion is successful or not.
    pub fn insert_with<F>(&mut self, key: K, func: F) -> bool
    where
        F: FnOnce(&K) -> V,
    {
        let path = match self.find_insert_location(&key) {
            Some(path) => path,
            None => return false,
        };
        let value = func(&key);
        let node = Box::new(Node::new(KeyValue { key, value }));
        self.splay.__rotate_to_root(node, path);
        return true;
    }
    // Return successful or not.
    pub fn insert(&mut self, key: K, value: V) -> bool {
        self.insert_with(key, |_| value)
    }
    pub fn insert_or_inc_cnt(&mut self, key: K)
    where
        V: CountAdd + Default,
        V::CountType: One,
    {
        if self.insert_with(key, |_| V::default()) == false {
            self.splay
                .update_root_data(|d| d.value.cnt_add(&V::CountType::one()));
        }
    }

    pub fn splay<E>(&mut self, key: &E) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let mut next = self.splay.root.take();
        let mut path = Vec::new();
        while let Some(mut cur) = next {
            let res = self.comparator.compare(&cur.d.key, key);
            if res == Ordering::Equal {
                self.splay.rotate_to_root(cur, path);
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
        self.splay.__rotate_to_root(prev, path);
        return false;
    }
    pub fn remove<E>(&mut self, key: &E) -> Option<KeyValue<K, V>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let ret = self.splay(key);
        if ret {
            Some(self.splay.take_root().unwrap().d)
        } else {
            None
        }
    }

    fn splay_smallest_or_largest(&mut self, is_largest: bool) {
        let mut path = Vec::new();
        find_smallest_or_largest(self.splay.root.take(), is_largest, &mut path);
        let x = match path.pop() {
            Some((x, _)) => x,
            None => return,
        };
        self.splay.__rotate_to_root(x, path);
    }
    pub fn pop_smallest(&mut self) -> Option<KeyValue<K, V>> {
        self.splay_smallest_or_largest(false);
        self.splay.pop_root()
    }
    pub fn pop_largest(&mut self) -> Option<KeyValue<K, V>> {
        self.splay_smallest_or_largest(true);
        self.splay.pop_root()
    }
    fn query_smallest_or_largest(
        &mut self,
        is_largest: bool,
    ) -> Option<&KeyValue<K, V>> {
        self.splay_smallest_or_largest(is_largest);
        self.root_data()
    }
    pub fn query_smallest(&mut self) -> Option<&KeyValue<K, V>> {
        self.query_smallest_or_largest(false)
    }

    pub fn splay_first_le<E>(&mut self, key: &E) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.to_range().splay_first_le(key)
    }
    pub fn splay_first_ge<E>(&mut self, key: &E) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.to_range().splay_first_ge(key)
    }

    fn query_first_le_or_ge<E>(
        &mut self,
        key: &E,
        ge: bool,
    ) -> Option<&KeyValue<K, V>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let found = self.to_range().splay_first_le_or_ge(key, ge);
        if !found {
            return None;
        }
        let ret = self.root_data();
        assert!(ret.is_some());
        ret
    }
    pub fn query_first_le<E>(&mut self, key: &E) -> Option<&KeyValue<K, V>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.query_first_le_or_ge(key, false)
    }
    pub fn query_first_ge<E>(&mut self, key: &E) -> Option<&KeyValue<K, V>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.query_first_le_or_ge(key, true)
    }

    fn query_first_lt_or_gt<E, const GT: bool>(
        &mut self,
        key: &E,
    ) -> Option<&KeyValue<K, V>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let found = self.to_range().splay_first_lt_or_gt::<E, GT>(key);
        if !found {
            return None;
        }
        let ret = self.root_data();
        assert!(ret.is_some());
        ret
    }
    pub fn query_first_lt<E>(&mut self, key: &E) -> Option<&KeyValue<K, V>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.query_first_lt_or_gt::<E, false>(key)
    }
    pub fn query_first_gt<E>(&mut self, key: &E) -> Option<&KeyValue<K, V>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        self.query_first_lt_or_gt::<E, true>(key)
    }

    // The remaining smallest will be the root.
    pub fn del_smaller<E>(&mut self, key: &E)
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let (mut path, ans_depth) =
            self.to_range().path_to_first_le_or_ge(key, true);
        path.truncate(ans_depth);
        let mut ans = match path.pop() {
            Some((ans, _)) => ans,
            None => return,
        };
        ans.__splay(path);
        ans.set_child(false, None);
        self.splay.root = Some(ans);
    }

    pub fn range<E, R>(&mut self, range: R) -> KeyRange<K, V, C>
    where
        C: Compare<K, E>,
        E: ?Sized,
        R: RangeBounds<E>,
    {
        let mut ans = self.to_range();
        match range.start_bound() {
            Bound::Included(key) => ans = ans.ge(key),
            Bound::Excluded(key) => ans = ans.gt(key),
            Bound::Unbounded => {}
        }
        match range.end_bound() {
            Bound::Included(key) => ans = ans.le(key),
            Bound::Excluded(key) => ans = ans.lt(key),
            Bound::Unbounded => {}
        }
        ans
    }

    pub fn collect_data(&self) -> Vec<&KeyValue<K, V>> {
        self.splay.collect_data()
    }
    pub fn take_all_data(&mut self) -> Vec<KeyValue<K, V>> {
        let mut elems = Vec::new();
        take_subtree_data(self.splay.root.take(), &mut elems);
        elems
    }
}
impl<K: Ord, V: BasicOpsWithKey<K>, C: Compare<K, K>> SplayWithKey<K, V, C> {
    // Return updated or not
    pub fn update_root_value<F>(&mut self, f: F) -> bool
    where
        F: FnOnce(&K, &mut V),
    {
        self.to_range().update_root_value(f)
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + CountSub, C> SplayWithKey<K, V, C> {
    pub fn deref_root(&mut self) -> bool
    where
        V: CountSub,
        V::CountType: Zero + One,
    {
        self.splay.deref_root()
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + SubtreeCount, C> SplayWithKey<K, V, C> {
    pub fn size(&self) -> V::SubtreeCountType
    where
        V::SubtreeCountType: Zero + Copy,
    {
        self.splay.size()
    }
    pub fn splay_kth<'a>(&mut self, k: V::SubtreeCountType) -> bool
    where
        V::SubtreeCountType: Ord + Copy + Zero + Add + SubAssign,
    {
        self.splay.splay_kth(k)
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + Count + SubtreeCount, C>
    SplayWithKey<K, V, C>
{
    // Only for DEBUG
    pub fn check_sanity(&self)
    where
        V::CountType: Copy,
        V::SubtreeCountType:
            std::fmt::Debug + From<V::CountType> + AddAssign + Eq + Copy,
    {
        self.splay.check_sanity()
    }
}
impl<K: Ord, V: BasicOpsWithKey<K>, C> SplayWithKey<K, V, C> {
    pub fn print_tree_with<F>(&self, data_to_string: F)
    where
        F: Fn(&KeyValue<K, V>) -> String + Clone,
    {
        self.splay.print_tree_with(data_to_string)
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + Default, C: Compare<K, K> + Default>
    From<Vec<K>> for SplayWithKey<K, V, C>
{
    fn from(v: Vec<K>) -> Self {
        Self::construct(v, |key| KeyValue {
            key,
            value: V::default(),
        })
    }
}

// Example
struct RankTreeValue {
    cnt: u32,
    scnt: u32,
}

impl BasicOps for RankTreeValue {
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

impl Default for RankTreeValue {
    fn default() -> Self {
        RankTreeValue { cnt: 1, scnt: 1 }
    }
}

impl Count for RankTreeValue {
    type CountType = u32;
    fn cnt(&self) -> &Self::CountType {
        &self.cnt
    }
}

impl CountAdd for RankTreeValue {
    fn cnt_add(&mut self, delta: &Self::CountType) {
        self.cnt += delta;
    }
}

impl SubtreeCount for RankTreeValue {
    type SubtreeCountType = u32;
    fn subtree_count(&self) -> &Self::SubtreeCountType {
        &self.scnt
    }
}

fn ranktree_data_to_string<K: Ord + Display>(
    data: &KeyValue<K, RankTreeValue>,
) -> String {
    format!("{}*{}", data.key, data.value.cnt)
}

pub struct RankTree<K: Ord> {
    rep: SplayWithKey<K, RankTreeValue>,
}

impl<K: Ord> RankTree<K> {
    pub fn new() -> RankTree<K> {
        RankTree {
            rep: SplayWithKey::new(),
        }
    }
}

impl<K: Ord> RankTree<K> {
    pub fn size(&self) -> u32 {
        self.rep.size()
    }
    pub fn root_key(&self) -> Option<&K> {
        self.rep.root_data().map(|d| &d.key)
    }
    pub fn insert(&mut self, key: K) {
        self.rep.insert_or_inc_cnt(key);
    }
    pub fn splay(&mut self, key: &K) -> bool {
        self.rep.splay(key)
    }
    pub fn splay_first_le(&mut self, key: &K) -> bool {
        self.rep.splay_first_le(key)
    }
    pub fn splay_first_ge(&mut self, key: &K) -> bool {
        self.rep.splay_first_ge(key)
    }
    // The remaining smallest will be the root.
    pub fn del_smaller(&mut self, key: &K) {
        self.rep.del_smaller(key)
    }
    pub fn query_kth(&mut self, k: u32) -> Option<&K> {
        if self.rep.splay_kth(k) {
            self.root_key()
        } else {
            None
        }
    }
    pub fn check_sanity(&self) {
        self.rep.check_sanity()
    }
}

impl<K: Ord + std::fmt::Display> RankTree<K> {
    pub fn print_tree(&self) {
        self.rep.print_tree_with(ranktree_data_to_string);
    }
}
