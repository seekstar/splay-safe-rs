/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

//! Splay implemented with safe rust.
//!
//! # Examples
//!
//! ```
//! use splay_safe_rs::{BasicOpsWithKey, KeyValue, SplayWithKey};
//! use std::ops::Bound;
//!
//! struct SplayValue {
//!     vlen: usize,
//!     kvsize: usize,
//! }
//! impl BasicOpsWithKey<String> for SplayValue {
//!     fn push_up(
//!         &mut self,
//!         key: &String,
//!         lc: Option<&KeyValue<String, Self>>,
//!         rc: Option<&KeyValue<String, Self>>,
//!     ) {
//!         self.kvsize = key.len() + self.vlen;
//!         if let Some(d) = lc {
//!             self.kvsize += d.value.kvsize;
//!         }
//!         if let Some(d) = rc {
//!             self.kvsize += d.value.kvsize;
//!         }
//!     }
//! }
//!
//! let mut keys = SplayWithKey::<String, SplayValue>::new();
//! keys.insert("aa".to_owned(), SplayValue { vlen: 1, kvsize: 3 });
//! keys.insert("bb".to_owned(), SplayValue { vlen: 2, kvsize: 4 });
//! keys.insert("cc".to_owned(), SplayValue { vlen: 3, kvsize: 5 });
//! keys.insert("dd".to_owned(), SplayValue { vlen: 4, kvsize: 6 });
//! assert_eq!(
//!     keys.range::<str, _>((Bound::Included("bb"), Bound::Included("cc")))
//!         .root_data()
//!         .unwrap()
//!         .value
//!         .kvsize,
//!     9
//! );
//! ```

#![cfg_attr(not(test), no_std)]

#[cfg(feature = "std")]
extern crate std;

mod tests;

pub use compare::Compare;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};

use core::cmp::Ordering;
use core::fmt;
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, SubAssign};
use core::ops::{Bound, RangeBounds};
use core::ops::{Deref, DerefMut};

extern crate alloc;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

#[cfg(feature = "std")]
use alloc::format;
#[cfg(feature = "std")]
use fmt::Display;
#[cfg(feature = "std")]
use std::print;
#[cfg(feature = "std")]
use std::println;

// Extends compare::Natural
pub struct Natural<T: Ord + ?Sized>(PhantomData<fn(&T)>);
impl<T: Ord + ?Sized> Compare<T> for Natural<T> {
    fn compare(&self, l: &T, r: &T) -> Ordering {
        Ord::cmp(l, r)
    }
}
impl<T: Ord + ?Sized> Default for Natural<T> {
    fn default() -> Self {
        Natural(PhantomData)
    }
}
impl Compare<String, str> for Natural<String> {
    fn compare(&self, l: &String, r: &str) -> Ordering {
        l.as_str().cmp(r)
    }
}

pub trait BasicOps {
    #[allow(unused)]
    fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>) {}
    #[allow(unused)]
    fn push_down(&mut self, lc: Option<&mut Self>, rc: Option<&mut Self>) {}
}
impl BasicOps for () {}

impl BasicOps for usize {}
impl BasicOps for u8 {}
impl BasicOps for u16 {}
impl BasicOps for u32 {}
impl BasicOps for u64 {}
#[cfg(has_i128)]
impl BasicOps for u128 {}

impl BasicOps for isize {}
impl BasicOps for i8 {}
impl BasicOps for i16 {}
impl BasicOps for i32 {}
impl BasicOps for i64 {}
#[cfg(has_i128)]
impl BasicOps for i128 {}

#[derive(Clone, PartialEq)]
struct Node<T> {
    c: [Option<Box<Node<T>>>; 2],
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

struct DataMutRef<'a, T: BasicOps> {
    node: &'a mut Node<T>,
}
impl<'a, T: BasicOps> From<&'a mut Node<T>> for DataMutRef<'a, T> {
    fn from(node: &'a mut Node<T>) -> Self {
        Self { node }
    }
}
impl<'a, T: BasicOps> Deref for DataMutRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.node.d
    }
}
impl<'a, T: BasicOps> DerefMut for DataMutRef<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.node.d
    }
}
impl<'a, T: BasicOps> Drop for DataMutRef<'a, T> {
    fn drop(&mut self) {
        self.node.push_up();
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
    fn root_data_mut(&mut self) -> Option<DataMutRef<T>> {
        Some(self.rt.as_mut()?.deref_mut().into())
    }
    fn __rotate_to_root(
        &mut self,
        mut x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        x.splay(path);
        *self.rt = Some(x);
    }
    fn rotate_to_root_defer_pushup(
        &mut self,
        mut x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        x.__splay(path);
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
    // The root is at depth 1
    // ans_depth == 0 means no ans, and the last node in path is rotated to
    // root.
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
        let mut next = self.rt.take();
        while let Some(mut cur) = next {
            let side = match where_to_go(&cur) {
                Direction::Stop => {
                    self.rotate_to_root(cur, path);
                    return None;
                }
                Direction::Left => false,
                Direction::Right => true,
            };
            next = cur.take_child(side);
            path.push((cur, side));
        }
        Some(path)
    }
}

pub struct Splay<T> {
    root: Option<Box<Node<T>>>,
}

impl<T> Splay<T> {
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
    pub fn construct<E, F>(mut v: Vec<E>, constructor: F) -> Splay<T>
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
        Splay::construct(v, T::from)
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
    fn rotate_to_root_defer_pushup(
        &mut self,
        x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        self.to_range().rotate_to_root_defer_pushup(x, path);
    }

    pub fn root_data(&self) -> Option<&T> {
        self.root.as_ref().map(|root| &root.d)
    }
    fn root_data_mut(&mut self) -> Option<DataMutRef<T>> {
        self.root.as_mut().map(|root| root.deref_mut().into())
    }

    fn splay_first_or_last(&mut self, is_last: bool) {
        let mut path = Vec::new();
        find_smallest_or_largest(self.root.take(), is_last, &mut path);
        let x = match path.pop() {
            Some((x, _)) => x,
            None => return,
        };
        self.__rotate_to_root(x, path);
    }
    fn take_first_or_last(&mut self, is_last: bool) -> Option<Box<Node<T>>> {
        self.splay_first_or_last(is_last);
        let mut root = match self.root.take() {
            Some(root) => root,
            None => return None,
        };
        self.root = root.take_child(!is_last);
        Some(root)
    }
    fn pop_first_or_last(&mut self, is_last: bool) -> Option<T> {
        self.take_first_or_last(is_last).map(|rt| rt.d)
    }

    // second is whether there is a prev/next node
    fn take_root_and_splay(
        &mut self,
        splay_next: bool,
    ) -> Option<(Box<Node<T>>, bool)> {
        let mut root = match self.root.take() {
            Some(root) => root,
            None => return None,
        };
        let mut path = root.find_prev_or_next(splay_next);
        let mut x = match path.pop() {
            Some((x, _)) => x,
            None => {
                self.root = root.take_child(!splay_next);
                return Some((root, false));
            }
        };
        x.__splay(path);
        x.set_child(!splay_next, root.take_child(!splay_next));
        self.root = Some(x);
        return Some((root, true));
    }
    fn delete_root(&mut self) -> bool {
        self.take_root_and_splay(false).is_some()
    }
    fn pop_root_and_splay(&mut self, splay_next: bool) -> Option<(T, bool)> {
        self.take_root_and_splay(splay_next)
            .map(|(rt, exists)| (rt.d, exists))
    }
    /// Return (root popped, whether there exists a next node)
    pub fn pop_root_splay_next(&mut self) -> Option<(T, bool)> {
        self.pop_root_and_splay(true)
    }
    fn pop_root(&mut self) -> Option<T> {
        self.pop_root_and_splay(false).map(|(rt, _)| rt)
    }
    fn collect_data(&self) -> Vec<&T> {
        let mut elems = Vec::new();
        collect_subtree_data(&self.root, &mut elems);
        elems
    }
    pub fn take_all_data(mut self) -> Vec<T> {
        self.to_range().take_all_data()
    }
}

pub trait Count: BasicOps {
    type CountType;
    // Don't return reference because sometimes we just want it to return one,
    // and it would be difficult to return the reference to one with a static
    // lifetime if the type is unknown.
    fn cnt(&self) -> Self::CountType;
}

pub trait CountAdd: Count {
    fn cnt_add(&mut self, delta: &Self::CountType);
}

pub trait CountSub: Count {
    fn cnt_sub(&mut self, delta: &Self::CountType);
}

macro_rules! impl_count {
    ($t:ty) => {
        impl Count for $t {
            type CountType = $t;
            fn cnt(&self) -> Self::CountType {
                *self
            }
        }
        impl CountAdd for $t {
            fn cnt_add(&mut self, delta: &Self::CountType) {
                *self += delta;
            }
        }
        impl CountSub for $t {
            fn cnt_sub(&mut self, delta: &Self::CountType) {
                *self -= delta;
            }
        }
    };
}
impl_count!(usize);
impl_count!(u8);
impl_count!(u16);
impl_count!(u32);
impl_count!(u64);
#[cfg(has_i128)]
impl_count!(u128);

impl_count!(isize);
impl_count!(i8);
impl_count!(i16);
impl_count!(i32);
impl_count!(i64);
#[cfg(has_i128)]
impl_count!(i128);

pub trait Rank: Count {
    type RankType;
    fn subtree_count(&self) -> &Self::RankType;
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

impl<'a, T: Rank> Range<'a, T> {
    /// If T implements Count, then Count::cnt() should always return 1.
    /// We can't enforce this with the compiler because currently we can't
    /// define a trait CountIsOne : Count and override the "cnt" method of
    /// trait Count
    fn find_insert_location_by_index(
        &mut self,
        // Starts from zero
        mut index: T::RankType,
    ) -> Option<Vec<(Box<Node<T>>, bool)>>
    where
        T::RankType: Ord + for<'b> SubAssign<&'b T::RankType> + Zero + One,
    {
        let zero = T::RankType::zero();
        self.walk(|node| {
            assert!(&index <= node.d.subtree_count());
            let lscnt =
                node.c[0].as_ref().map_or(&zero, |lc| lc.d.subtree_count());
            if &index <= lscnt {
                Direction::Left
            } else {
                index -= lscnt;
                index -= &T::RankType::one();
                Direction::Right
            }
        })
    }
    fn insert_at_index(&mut self, index: T::RankType, data: T)
    where
        T::RankType: Ord + for<'b> SubAssign<&'b T::RankType> + Zero + One,
    {
        let path = match self.find_insert_location_by_index(index) {
            Some(path) => path,
            None => unreachable!(),
        };
        let node = Box::new(Node::new(data));
        self.__rotate_to_root(node, path);
    }
    fn splay_kth(&mut self, mut k: T::RankType) -> bool
    where
        T::RankType: Ord + Copy + Zero + Add + SubAssign,
    {
        let mut next = self.rt.take();
        let mut path = Vec::new();
        while let Some(mut cur) = next {
            cur.push_down();
            let lscnt = cur.c[0]
                .as_ref()
                .map_or(T::RankType::zero(), |lc| *lc.d.subtree_count());
            let rscnt = cur.c[1]
                .as_ref()
                .map_or(T::RankType::zero(), |rc| *rc.d.subtree_count());
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

impl<T: Rank> Splay<T> {
    pub fn size(&self) -> T::RankType
    where
        T::RankType: Zero + Copy,
    {
        match self.root {
            Some(ref root) => *root.d.subtree_count(),
            None => T::RankType::zero(),
        }
    }
    pub fn insert_at_index(&mut self, index: T::RankType, data: T)
    where
        T::RankType: Ord + for<'a> SubAssign<&'a T::RankType> + Zero + One,
    {
        self.to_range().insert_at_index(index, data)
    }

    /// If found, then the node will be the root, and return true.
    ///
    /// If not found, then the last accessed node will be the root, and return
    /// false.
    pub fn splay_kth<'a>(&mut self, k: T::RankType) -> bool
    where
        T::RankType: Ord + Copy + Zero + Add + SubAssign,
    {
        self.to_range().splay_kth(k)
    }
    pub fn query_kth<'a>(&mut self, k: T::RankType) -> Option<&T>
    where
        T::RankType: Ord + Copy + Zero + Add + SubAssign,
    {
        if self.splay_kth(k) {
            self.root_data()
        } else {
            None
        }
    }

    fn check_sanity_subtree<'a>(&self, rt: &Box<Node<T>>)
    where
        T::CountType: Copy,
        T::RankType: fmt::Debug + From<T::CountType> + AddAssign + Eq + Copy,
    {
        let mut scnt = T::RankType::from(rt.d.cnt());
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
    /// Only for DEBUG
    pub fn check_sanity(&self)
    where
        T::CountType: Copy,
        T::RankType: fmt::Debug + From<T::CountType> + AddAssign + Eq + Copy,
    {
        if let Some(ref root) = self.root {
            self.check_sanity_subtree(root);
        }
    }
}

#[cfg(feature = "std")]
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
    str.pop();
    str.pop();
    str.push('-');
    str.push('-');
    print!("{}", str);

    str.pop();
    str.pop();
    str.push(' ');
    str.push(' ');
    __print_subtree(&rt.c[1], str, data_to_string);

    str.truncate(ori_len);
}
#[cfg(feature = "std")]
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
#[cfg(feature = "std")]
fn print_subtree<T, F>(rt: &Option<Box<Node<T>>>, data_to_string: F)
where
    T: BasicOps,
    F: Fn(&T) -> String + Clone,
{
    __print_subtree(rt, &mut String::new(), data_to_string);
}

#[cfg(feature = "std")]
impl<T: BasicOps> Splay<T> {
    pub fn print_tree_with<F>(&self, data_to_string: F)
    where
        F: Fn(&T) -> String + Clone,
    {
        print_subtree(&self.root, data_to_string);
    }
}
#[cfg(feature = "std")]
fn default_data_to_string<T>(data: &T) -> String
where
    T: Display,
{
    format!("{}", data)
}
#[cfg(feature = "std")]
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
    fn cnt(&self) -> Self::CountType {
        self.value.cnt()
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + CountSub> CountSub for KeyValue<K, V> {
    fn cnt_sub(&mut self, delta: &Self::CountType) {
        self.value.cnt_sub(delta)
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + Rank> Rank for KeyValue<K, V> {
    type RankType = V::RankType;
    fn subtree_count(&self) -> &Self::RankType {
        self.value.subtree_count()
    }
}

pub struct ValueMutRef<'a, K: Ord, V: BasicOpsWithKey<K>> {
    d: DataMutRef<'a, KeyValue<K, V>>,
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>> From<DataMutRef<'a, KeyValue<K, V>>>
    for ValueMutRef<'a, K, V>
{
    fn from(data: DataMutRef<'a, KeyValue<K, V>>) -> Self {
        Self { d: data }
    }
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>> Deref for ValueMutRef<'a, K, V> {
    type Target = V;
    fn deref(&self) -> &Self::Target {
        &self.d.value
    }
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>> DerefMut for ValueMutRef<'a, K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.d.value
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
    pub fn root_value_mut(&mut self) -> Option<ValueMutRef<K, V>> {
        self.range.root_data_mut().map(|d| d.into())
    }
    pub fn collect_data(&self) -> Vec<&KeyValue<K, V>> {
        self.range.collect_data()
    }
    pub fn take_all_data(self) -> Vec<KeyValue<K, V>> {
        self.range.take_all_data()
    }

    /// Return updated or not
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

pub struct VacantEntry<'a, K: Ord, V: BasicOpsWithKey<K>, C> {
    splay_path_key: Option<(
        &'a mut SplayWithKey<K, V, C>,
        Vec<(Box<Node<KeyValue<K, V>>>, bool)>,
        K,
    )>,
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>, C: Compare<K>>
    VacantEntry<'a, K, V, C>
{
    fn new(
        splay: &'a mut SplayWithKey<K, V, C>,
        path: Vec<(Box<Node<KeyValue<K, V>>>, bool)>,
        key: K,
    ) -> Self {
        Self {
            splay_path_key: Some((splay, path, key)),
        }
    }
    pub fn key(&self) -> &K {
        &self.splay_path_key.as_ref().unwrap().2
    }
    pub fn insert(mut self, value: V) -> ValueMutRef<'a, K, V> {
        let (splay, path, key) = self.splay_path_key.take().unwrap();
        let node = Box::new(Node::new(KeyValue { key, value }));
        splay.splay.rotate_to_root_defer_pushup(node, path.into());
        splay.root_value_mut().unwrap()
    }
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>, C> Drop for VacantEntry<'a, K, V, C> {
    fn drop(&mut self) {
        if let Some((splay, mut path, _)) = self.splay_path_key.take() {
            if let Some((node, _)) = path.pop() {
                splay.splay.__rotate_to_root(node, path);
            }
        }
    }
}

pub struct OccupiedEntry<'a, K: Ord, V: BasicOpsWithKey<K>, C> {
    splay: &'a mut SplayWithKey<K, V, C>,
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>, C: Compare<K>>
    OccupiedEntry<'a, K, V, C>
{
    fn new(splay: &'a mut SplayWithKey<K, V, C>) -> Self {
        Self { splay }
    }
    pub fn get_mut(&'a mut self) -> ValueMutRef<'a, K, V> {
        self.splay.root_value_mut().unwrap()
    }
    pub fn into_mut(self) -> ValueMutRef<'a, K, V> {
        self.splay.root_value_mut().unwrap()
    }
}

pub enum Entry<'a, K: Ord, V: BasicOpsWithKey<K>, C> {
    Vacant(VacantEntry<'a, K, V, C>),
    /// https://github.com/rust-lang/rfcs/issues/690
    Occupied(OccupiedEntry<'a, K, V, C>, K),
}
impl<'a, K: Ord, V: BasicOpsWithKey<K>, C> Entry<'a, K, V, C> {
    pub fn and_modify<F>(mut self, f: F) -> Entry<'a, K, V, C>
    where
        F: FnOnce(&K, &mut V),
    {
        if let Self::Occupied(entry, _) = &mut self {
            let mut d = entry.splay.splay.root_data_mut().unwrap();
            let d = d.deref_mut();
            f(&d.key, &mut d.value);
        }
        self
    }
    pub fn or_insert(self, default: V) -> ValueMutRef<'a, K, V>
    where
        C: Compare<K>,
    {
        match self {
            Self::Vacant(entry) => entry.insert(default),
            Self::Occupied(entry, _) => entry.into_mut(),
        }
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
    pub fn new() -> Self
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
            splay: Splay::construct(v, constructor),
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

    pub fn comparator(&self) -> &C {
        &self.comparator
    }

    pub fn is_empty(&self) -> bool {
        self.splay.is_empty()
    }
    pub fn root_data(&self) -> Option<&KeyValue<K, V>> {
        self.splay.root_data()
    }
    fn root_value_mut(&mut self) -> Option<ValueMutRef<K, V>> {
        self.splay.root_data_mut().map(|d| d.into())
    }
    pub fn pop_smallest(&mut self) -> Option<KeyValue<K, V>> {
        self.splay.pop_first_or_last(false)
    }
    pub fn pop_largest(&mut self) -> Option<KeyValue<K, V>> {
        self.splay.pop_first_or_last(true)
    }
    /// Return root popped and whether there exists a next node
    pub fn pop_root_splay_next(&mut self) -> Option<(KeyValue<K, V>, bool)> {
        self.splay.pop_root_splay_next()
    }

    fn to_range(&mut self) -> KeyRange<K, V, C> {
        KeyRange {
            range: self.splay.to_range(),
            comparator: &self.comparator,
        }
    }
    /// Return updated or not
    pub fn update_root_value<F>(&mut self, f: F) -> bool
    where
        F: FnOnce(&K, &mut V),
    {
        self.to_range().update_root_value(f)
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
    pub fn entry(&mut self, key: K) -> Entry<K, V, C> {
        if let Some(path) = self.find_insert_location(&key) {
            Entry::Vacant(VacantEntry::new(self, path, key))
        } else {
            Entry::Occupied(OccupiedEntry::new(self), key)
        }
    }
    /// If already exists, replace and return the old key and value.
    pub fn insert(&mut self, key: K, mut value: V) -> Option<(K, V)> {
        match self.entry(key) {
            Entry::Occupied(mut entry, key) => {
                core::mem::swap(&mut entry.get_mut().d.value, &mut value);
                return Some((key, value));
            }
            Entry::Vacant(entry) => {
                entry.insert(value);
                return None;
            }
        }
    }
    pub fn insert_or_inc_cnt(&mut self, key: K)
    where
        V: CountAdd + From<V::CountType>,
        V::CountType: One,
    {
        self.entry(key)
            .and_modify(|_, v| v.cnt_add(&V::CountType::one()))
            .or_insert(V::CountType::one().into());
    }

    /// Return found or not
    pub fn splay<E>(&mut self, key: &E) -> bool
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let mut path = if let Some(path) = self.find_insert_location(key) {
            path
        } else {
            return true;
        };
        // Not found. Rotate the last accessed node to root to maintain
        // complexity.
        if let Some((prev, _)) = path.pop() {
            self.splay.__rotate_to_root(prev, path);
        }
        return false;
    }
    pub fn get<E>(&mut self, key: &E) -> Option<&V>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let ret = self.splay(key);
        if ret {
            Some(&self.root_data().unwrap().value)
        } else {
            None
        }
    }
    pub fn get_mut<E>(&mut self, key: &E) -> Option<ValueMutRef<K, V>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let ret = self.splay(key);
        if ret {
            self.root_value_mut()
        } else {
            None
        }
    }
    pub fn remove<E>(&mut self, key: &E) -> Option<KeyValue<K, V>>
    where
        C: Compare<K, E>,
        E: ?Sized,
    {
        let ret = self.splay(key);
        if ret {
            Some(self.splay.pop_root().unwrap())
        } else {
            None
        }
    }

    fn query_smallest_or_largest(
        &mut self,
        is_largest: bool,
    ) -> Option<&KeyValue<K, V>> {
        self.splay.splay_first_or_last(is_largest);
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
impl<K: Ord, V: BasicOpsWithKey<K> + CountSub, C> SplayWithKey<K, V, C> {
    pub fn deref_root(&mut self) -> bool
    where
        V: CountSub,
        V::CountType: Zero + One,
    {
        self.splay.deref_root()
    }
}
impl<K: Ord, V: BasicOpsWithKey<K> + Rank, C> SplayWithKey<K, V, C> {
    pub fn size(&self) -> V::RankType
    where
        V::RankType: Zero + Copy,
    {
        self.splay.size()
    }
    pub fn splay_kth(&mut self, k: V::RankType) -> bool
    where
        V::RankType: Ord + Copy + Zero + Add + SubAssign,
    {
        self.splay.splay_kth(k)
    }
    pub fn query_kth_key(&mut self, k: V::RankType) -> Option<&K>
    where
        V::RankType: Ord + Copy + Zero + Add + SubAssign,
    {
        self.splay.query_kth(k).map(|d| &d.key)
    }

    /// Only for DEBUG
    pub fn check_sanity(&self)
    where
        V::CountType: Copy,
        V::RankType: fmt::Debug + From<V::CountType> + AddAssign + Eq + Copy,
    {
        self.splay.check_sanity()
    }
}
#[cfg(feature = "std")]
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
impl<K: Ord, V: BasicOpsWithKey<K>, C: Compare<K, K> + Default>
    From<Vec<(K, V)>> for SplayWithKey<K, V, C>
{
    fn from(v: Vec<(K, V)>) -> Self {
        Self::construct(v, |(key, value)| KeyValue { key, value })
    }
}

pub struct CountedRankTreeValue<CountType = u64, RankType = CountType> {
    cnt: CountType,
    scnt: RankType,
}

impl<CountType, RankType> BasicOps for CountedRankTreeValue<CountType, RankType>
where
    CountType: Clone,
    RankType:
        Clone + From<CountType> + for<'a> core::ops::AddAssign<&'a RankType>,
{
    fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>) {
        self.scnt = self.cnt.clone().into();
        if let Some(d) = lc {
            self.scnt += &d.scnt;
        }
        if let Some(d) = rc {
            self.scnt += &d.scnt;
        }
    }
}

impl<CountType, RankType> Default for CountedRankTreeValue<CountType, RankType>
where
    CountType: num_traits::One,
    RankType: num_traits::One,
{
    fn default() -> Self {
        CountedRankTreeValue {
            cnt: CountType::one(),
            scnt: RankType::one(),
        }
    }
}

impl<CountType, RankType> Count for CountedRankTreeValue<CountType, RankType>
where
    CountType: Clone,
    RankType:
        Clone + From<CountType> + for<'a> core::ops::AddAssign<&'a RankType>,
{
    type CountType = CountType;
    fn cnt(&self) -> Self::CountType {
        self.cnt.clone()
    }
}

impl<CountType, RankType> CountAdd for CountedRankTreeValue<CountType, RankType>
where
    CountType: Clone + for<'a> AddAssign<&'a CountType>,
    RankType:
        Clone + From<CountType> + for<'a> core::ops::AddAssign<&'a RankType>,
{
    fn cnt_add(&mut self, delta: &Self::CountType) {
        self.cnt += delta;
    }
}

impl<CountType, RankType> Rank for CountedRankTreeValue<CountType, RankType>
where
    CountType: Clone,
    RankType:
        Clone + From<CountType> + for<'a> core::ops::AddAssign<&'a RankType>,
{
    type RankType = RankType;
    fn subtree_count(&self) -> &Self::RankType {
        &self.scnt
    }
}

impl<CountType, RankType> From<CountType>
    for CountedRankTreeValue<CountType, RankType>
where
    CountType: Clone,
    RankType: From<CountType>,
{
    fn from(cnt: CountType) -> Self {
        Self {
            cnt: cnt.clone(),
            scnt: cnt.into(),
        }
    }
}

#[cfg(feature = "std")]
fn ranktree_data_to_string<K: Ord + Display>(
    data: &KeyValue<K, CountedRankTreeValue>,
) -> String {
    format!("{}*{}", data.key, data.value.cnt)
}

pub type CountedRankTreeWithKey<K, CountType = u64, RankType = CountType> =
    SplayWithKey<K, CountedRankTreeValue<CountType, RankType>>;

#[cfg(feature = "std")]
impl<K: Ord + Display> CountedRankTreeWithKey<K> {
    pub fn print_tree(&self) {
        self.print_tree_with(ranktree_data_to_string);
    }
}

#[derive(Debug)]
pub struct RankTreeValue<V, RankType = usize> {
    pub value: V,
    scnt: RankType,
}
impl<V, RankType> BasicOps for RankTreeValue<V, RankType>
where
    RankType: num_traits::One + for<'a> AddAssign<&'a RankType>,
{
    fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>) {
        self.scnt = RankType::one();
        if let Some(d) = lc {
            self.scnt += &d.scnt;
        }
        if let Some(d) = rc {
            self.scnt += &d.scnt;
        }
    }
}
impl<V, RankType> Count for RankTreeValue<V, RankType>
where
    RankType: num_traits::One + for<'a> AddAssign<&'a RankType>,
{
    type CountType = RankType;
    fn cnt(&self) -> Self::CountType {
        RankType::one()
    }
}
// Doesn't support CountAdd and CountSub because we don't store count.
impl<V, RankType> Rank for RankTreeValue<V, RankType>
where
    RankType: num_traits::One + for<'a> AddAssign<&'a RankType>,
{
    type RankType = RankType;
    fn subtree_count(&self) -> &Self::RankType {
        &self.scnt
    }
}

impl<V, RankType> From<V> for RankTreeValue<V, RankType>
where
    RankType: num_traits::One,
{
    fn from(value: V) -> Self {
        Self {
            value,
            scnt: RankType::one(),
        }
    }
}

pub type RankTree<V, RankType = usize> = Splay<RankTreeValue<V, RankType>>;
