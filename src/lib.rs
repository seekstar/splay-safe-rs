mod tests;

use num_traits::{One, Zero};

use core::cmp::Ordering;
use core::ops::{Add, AddAssign, SubAssign};

pub trait BasicOps {
    type KeyType: Ord;
    fn key(&self) -> &Self::KeyType;
    fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>);
}

// TODO: Use From trait instead.
pub trait WithKey: BasicOps {
    fn with_key(key: Self::KeyType) -> Self;
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
}

fn find_smallest_or_largest<T>(
    rt: Option<Box<Node<T>>>,
    is_largest: bool,
    path: &mut Vec<(Box<Node<T>>, bool)>,
) {
    let mut next = rt;
    while let Some(mut cur) = next {
        next = cur.c[is_largest as usize].take();
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
    // y is the parent of x
    // Will update y.scnt
    // Dirty: x.scnt, x <-> to
    fn __rotate_up(
        &mut self, // x
        mut y: Box<Node<T>>,
        side_x: bool,
    ) {
        let w = self.c[!side_x as usize].take();
        y.c[side_x as usize] = w;
        y.push_up();
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
        let next = self.c[is_next as usize].take();
        find_smallest_or_largest(next, !is_next, &mut path);
        path
    }
}

struct Interval<'a, T> {
    rt: &'a mut Option<Box<Node<T>>>,
}

impl<'a, T> From<&'a mut Option<Box<Node<T>>>> for Interval<'a, T> {
    fn from(rt: &'a mut Option<Box<Node<T>>>) -> Interval<'a, T> {
        Interval { rt }
    }
}

impl<'a, T: BasicOps> Interval<'a, T> {
    fn root_data(self) -> Option<&'a T> {
        self.rt.as_ref().map(|x| &x.d)
    }
    fn rotate_to_root(
        &mut self,
        mut x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        x.splay(path);
        *self.rt = Some(x);
    }
    /// # Arguments
    /// * ge
    /// 	- false: Find the first node whose value <= key.
    /// 	- true: Find the first node whose value >= key.
    fn __find_first_le_or_ge(
        &mut self,
        key: &T::KeyType,
        ge: bool,
    ) -> (Vec<(Box<Node<T>>, bool)>, usize) {
        let mut next = self.rt.take();
        let mut path = Vec::new();
        let mut ans_depth = 0;
        while let Some(mut cur) = next {
            let res = cur.d.key().cmp(key);
            if res == Ordering::Equal {
                path.push((cur, false));
                ans_depth = path.len();
                return (path, ans_depth);
            }
            let side = res == Ordering::Less;
            next = cur.c[side as usize].take();
            path.push((cur, side));
            if side != ge {
                ans_depth = path.len();
            }
        }
        (path, ans_depth)
    }
    // If found, then the node will be the root, and return true.
    // Otherwise return false.
    fn find_first_le_or_ge(&mut self, key: &T::KeyType, ge: bool) -> bool {
        let (mut path, ans_depth) = self.__find_first_le_or_ge(key, ge);
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
        self.rotate_to_root(ans, path);
        return true;
    }
    fn find_first_le(&mut self, key: &T::KeyType) -> bool {
        self.find_first_le_or_ge(key, false)
    }
    fn find_first_ge(&mut self, key: &T::KeyType) -> bool {
        self.find_first_le_or_ge(key, true)
    }
}

impl<'a, T: BasicOps + SubtreeCount> Interval<'a, T> {
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
            let lscnt = if let Some(ref lc) = cur.c[0] {
                *lc.d.subtree_count()
            } else {
                T::SubtreeCountType::zero()
            };
            let cur_cnt = *cur.d.cnt();
            if &lscnt < &k && &(lscnt + cur_cnt) >= &k {
                self.rotate_to_root(cur, path);
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
        self.rotate_to_root(x, path);
        return false;
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
}

fn build<T: BasicOps + WithKey>(
    v: &mut Vec<T::KeyType>,
    start: usize,
) -> Option<Box<Node<T>>> {
    let len = v.len() - start;
    if len == 0 {
        return None;
    }
    let mid = start + len / 2;
    let rc = build(v, mid + 1);
    debug_assert_eq!(mid + 1, v.len());
    let key = v.pop().unwrap();
    let lc = build(v, start);
    let mut node = Box::new(Node {
        d: T::with_key(key),
        c: [lc, rc],
    });
    node.push_up();
    Some(node)
}
impl<T: WithKey> From<Vec<T::KeyType>> for Splay<T> {
    fn from(mut v: Vec<T::KeyType>) -> Splay<T> {
        v.sort_unstable();
        let root = build(&mut v, 0);
        debug_assert!(v.is_empty());
        Splay { root }
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

fn take_non_empty_subtree_data<T>(mut rt: Box<Node<T>>, elems: &mut Vec<T>) {
    take_subtree_data(rt.c[0].take(), elems);
    elems.push(rt.d);
    take_subtree_data(rt.c[1].take(), elems);
}
fn take_subtree_data<T>(rt: Option<Box<Node<T>>>, elems: &mut Vec<T>) {
    if let Some(rt) = rt {
        take_non_empty_subtree_data(rt, elems);
    }
}

impl<T: BasicOps> Splay<T> {
    fn to_interval(&mut self) -> Interval<T> {
        Interval { rt: &mut self.root }
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
        let root = match self.root.as_mut() {
            Some(root) => root,
            None => return false,
        };
        f(&mut root.d);
        root.push_up();
        return true;
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
                self.root = root.c[1].take();
                return Some(root);
            }
        };
        x.__splay(path);
        x.c[1] = root.c[1].take();
        x.push_up();
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
    fn find_insert_location(
        &mut self,
        key: &T::KeyType,
    ) -> Option<Vec<(Box<Node<T>>, bool)>> {
        let mut path = Vec::new();
        let mut cur = match self.root.take() {
            Some(root) => root,
            None => {
                return Some(path);
            }
        };
        loop {
            if *cur.d.key() == *key {
                self.rotate_to_root(cur, path);
                return None;
            }
            let side = cur.d.key() < key;
            let next = cur.c[side as usize].take();
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
    pub fn insert_owned_key_with_func<F>(
        &mut self,
        key: T::KeyType,
        func: F,
    ) -> bool
    where
        F: FnOnce(T::KeyType) -> T,
    {
        let path = match self.find_insert_location(&key) {
            Some(path) => path,
            None => return false,
        };
        let node = Box::new(Node::new(func(key)));
        self.rotate_to_root(node, path);
        return true;
    }
    pub fn insert_owned_key(&mut self, key: T::KeyType) -> bool
    where
        T: WithKey,
    {
        self.insert_owned_key_with_func(key, |key| T::with_key(key))
    }
    pub fn insert_owned_key_or_inc_cnt(&mut self, key: T::KeyType)
    where
        T: WithKey + CountAdd,
        T::CountType: One,
    {
        if self.insert_owned_key(key) == false {
            self.update_root_data(|d| d.cnt_add(&T::CountType::one()));
        }
    }

    pub fn find(&mut self, key: &T::KeyType) -> bool {
        let mut next = self.root.take();
        let mut path = Vec::new();
        while let Some(mut cur) = next {
            let res = key.cmp(cur.d.key());
            if res == Ordering::Equal {
                self.rotate_to_root(cur, path);
                return true;
            }
            let side = res == Ordering::Greater;
            next = cur.c[side as usize].take();
            path.push((cur, side));
        }
        // Not found. Rotate the last accessed node to root to maintain
        // complexity.
        let prev = match path.pop() {
            Some((prev, _)) => prev,
            None => return false,
        };
        self.rotate_to_root(prev, path);
        return false;
    }
    pub fn delete(&mut self, key: &T::KeyType) -> bool {
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
        self.rotate_to_root(x, path);
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

    pub fn find_first_le(&mut self, key: &T::KeyType) -> bool {
        self.to_interval().find_first_le(key)
    }
    pub fn find_first_ge(&mut self, key: &T::KeyType) -> bool {
        self.to_interval().find_first_ge(key)
    }

    // The remaining smallest will be the root.
    pub fn del_smaller(&mut self, key: &T::KeyType) {
        let (mut path, ans_depth) =
            self.to_interval().__find_first_le_or_ge(key, true);
        path.truncate(ans_depth);
        let mut ans = match path.pop() {
            Some((ans, _)) => ans,
            None => return,
        };
        ans.__splay(path);
        ans.c[0] = None;
        ans.push_up();
        self.root = Some(ans);
    }

    fn get_open_interval(
        &mut self,
        left: &T::KeyType,
        right: &T::KeyType,
    ) -> Interval<T> {
        let mut interval = self.to_interval();
        let found = interval.find_first_le(left);
        if found {
            let rt = interval.rt.as_mut().unwrap();
            interval = Interval::from(&mut rt.c[1]);
        }
        let found = interval.find_first_ge(right);
        if found {
            let rt = interval.rt.as_mut().unwrap();
            interval = Interval::from(&mut rt.c[0]);
        }
        interval
    }

    pub fn query_in_open_interval(
        &mut self,
        left: &T::KeyType,
        right: &T::KeyType,
    ) -> Option<&T> {
        let interval = self.get_open_interval(left, right);
        interval.root_data()
    }

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

impl<T: BasicOps + SubtreeCount> Splay<T> {
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

impl<T: BasicOps + std::fmt::Display> Splay<T> {
    pub fn print_tree(&self) {
        print_subtree(&self.root);
    }
}

// Example
struct RankTreeData<T> {
    key: T,
    cnt: u32,
    scnt: u32,
}

impl<T: Ord> BasicOps for RankTreeData<T> {
    type KeyType = T;
    fn key(&self) -> &Self::KeyType {
        &self.key
    }
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

impl<T: Ord> WithKey for RankTreeData<T> {
    fn with_key(key: Self::KeyType) -> Self {
        RankTreeData {
            key: key,
            cnt: 1,
            scnt: 1,
        }
    }
}

impl<T> Count for RankTreeData<T> {
    type CountType = u32;
    fn cnt(&self) -> &Self::CountType {
        &self.cnt
    }
}

impl<T> CountAdd for RankTreeData<T> {
    fn cnt_add(&mut self, delta: &Self::CountType) {
        self.cnt += delta;
    }
}

impl<T> SubtreeCount for RankTreeData<T> {
    type SubtreeCountType = u32;
    fn subtree_count(&self) -> &Self::SubtreeCountType {
        &self.scnt
    }
}

impl<T: std::fmt::Display> std::fmt::Display for RankTreeData<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}*{}", self.key, self.cnt)
    }
}

pub struct RankTree<T> {
    rep: Splay<RankTreeData<T>>,
}

impl<T> RankTree<T> {
    pub fn new() -> RankTree<T> {
        RankTree { rep: Splay::new() }
    }
}

impl<T: Ord> RankTree<T> {
    pub fn size(&self) -> u32 {
        self.rep.size()
    }
    pub fn root_key(&self) -> Option<&T> {
        self.rep.root_data().map(|d| d.key())
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
