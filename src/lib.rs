use num_traits::One;
use num_traits::Zero;

use std::ops::Add;
use std::ops::SubAssign;
use std::{cmp::Ordering, ops::AddAssign};

pub trait BasicOps {
    type KeyType;
    type CountType;
    fn new(key: Self::KeyType) -> Self;
    fn key(&self) -> &Self::KeyType;
    fn cnt(&self) -> &Self::CountType;
    fn cnt_mut(&mut self) -> &mut Self::CountType;
    fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>);
}

pub trait SubtreeCount {
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
        let mut next = self.c[is_next as usize].take();
        let side = !is_next;
        while let Some(mut cur) = next {
            next = cur.c[side as usize].take();
            path.push((cur, side));
        }
        return path;
    }
}

pub struct SplayGeneric<T> {
    root: Option<Box<Node<T>>>,
}

impl<T> SplayGeneric<T> {
    // use Basic::C as CT;
    pub fn new() -> SplayGeneric<T> {
        SplayGeneric { root: None }
    }
}

impl<T: BasicOps> SplayGeneric<T> {
    fn rotate_to_root(
        &mut self,
        mut x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        x.splay(path);
        self.root = Some(x);
    }

    pub fn root_data(&self) -> Option<&T> {
        self.root.as_ref().map(|root| &root.d)
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
                return None;
            }
        };
        x.__splay(path);
        x.c[1] = root.c[1].take();
        x.push_up();
        self.root = Some(x);
        return Some(root);
    }

    // The new node will be the root
    pub fn insert(&mut self, key: T::KeyType)
    where
        T::KeyType: Ord,
        T::CountType: AddAssign + One,
    {
        let tmp = self.root.take();
        let mut cur = match tmp {
            Some(root) => root,
            None => {
                self.root = Some(Box::new(Node::new(T::new(key))));
                return;
            }
        };
        let mut path = Vec::new();
        loop {
            if *cur.d.key() == key {
                *cur.d.cnt_mut() += T::CountType::one();
                // cur.scnt will be updated by subsequent rotate_to_root
                break;
            }
            let side = cur.d.key() < &key;
            let next = cur.c[side as usize].take();
            path.push((cur, side));
            if let Some(nex) = next {
                cur = nex
            } else {
                cur = Box::new(Node::new(T::new(key)));
                // cur <-> prev, cur.scnt and prev.scnt will be updated by
                // subsequent rotate_to_root
                break;
            }
        }
        self.rotate_to_root(cur, path);
    }

    pub fn find(&mut self, key: &T::KeyType) -> bool
    where
        T::KeyType: Ord,
    {
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
    pub fn delete(&mut self, key: &T::KeyType) -> bool
    where
        T::KeyType: Ord,
    {
        let ret = self.find(key);
        if ret {
            self.take_root();
        }
        return ret;
    }

    /// # Arguments
    /// * ge
    /// 	- false: Find the first node whose value <= key.
    /// 	- true: Find the first node whose value >= key.
    fn __find_first_le_or_ge(
        &mut self,
        key: &T::KeyType,
        ge: bool,
    ) -> (Vec<(Box<Node<T>>, bool)>, usize)
    where
        T::KeyType: Ord,
    {
        let mut next = self.root.take();
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
    fn find_first_le_or_ge(&mut self, key: &T::KeyType, ge: bool) -> bool
    where
        T::KeyType: Ord,
    {
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
                    self.root = Some(prev);
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
    pub fn find_first_le(&mut self, key: &T::KeyType) -> bool
    where
        T::KeyType: Ord,
    {
        self.find_first_le_or_ge(key, false)
    }
    pub fn find_first_ge(&mut self, key: &T::KeyType) -> bool
    where
        T::KeyType: Ord,
    {
        return self.find_first_le_or_ge(key, true);
    }

    // The remaining smallest will be the root.
    pub fn del_smaller(&mut self, key: &T::KeyType)
    where
        T::KeyType: Ord,
    {
        let (mut path, ans_depth) = self.__find_first_le_or_ge(key, true);
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
}

impl<T: BasicOps + SubtreeCount> SplayGeneric<T> {
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
    pub fn query_kth<'a>(&mut self, mut k: T::SubtreeCountType) -> bool
    where
        T::CountType: Copy,
        T::SubtreeCountType: Ord
            + Copy
            + Zero
            + Add<T::CountType, Output = T::SubtreeCountType>
            + SubAssign,
    {
        let mut next = self.root.take();
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

impl<T: BasicOps> SplayGeneric<T> {
    fn __print_subtree_non_empty(&self, rt: &Node<T>, str: &mut String)
    where
        T::KeyType: std::fmt::Display,
        T::CountType: One + PartialEq + std::fmt::Display,
    {
        let ori_len = str.len();
        let node = if rt.d.cnt().is_one() {
            format!("{}", rt.d.key())
        } else {
            format!("{}*{}", rt.d.key(), rt.d.cnt())
        };
        let len = node.len();
        print!("{}", node);
        print!("---");
        // str.push_str(&String::from_iter(std::iter::repeat(' ').take(len)));
        str.push_str(&std::iter::repeat(' ').take(len).collect::<String>());
        str.push_str(" | ");
        self.__print_subtree(&rt.c[0], str);
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
        self.__print_subtree(&rt.c[1], str);

        str.truncate(ori_len);
    }
    fn __print_subtree(&self, rt: &Option<Box<Node<T>>>, str: &mut String)
    where
        T::KeyType: std::fmt::Display,
        T::CountType: One + PartialEq + std::fmt::Display,
    {
        if let Some(node) = rt {
            self.__print_subtree_non_empty(node, str);
        } else {
            println!("/\\");
        }
    }
    fn print_subtree(&self, rt: &Option<Box<Node<T>>>)
    where
        T::KeyType: std::fmt::Display,
        T::CountType: One + PartialEq + std::fmt::Display,
    {
        self.__print_subtree(rt, &mut String::new());
    }
    pub fn print_tree(&self)
    where
        T::KeyType: std::fmt::Display,
        T::CountType: One + PartialEq + std::fmt::Display,
    {
        self.print_subtree(&self.root);
    }
}

// Example
struct SplayData<T> {
    key: T,
    cnt: u32,
    scnt: u32,
}

impl<T> BasicOps for SplayData<T> {
    type KeyType = T;
    type CountType = u32;
    fn new(key: T) -> Self {
        SplayData {
            key,
            cnt: 1,
            scnt: 1,
        }
    }
    fn key(&self) -> &Self::KeyType {
        &self.key
    }
    fn cnt(&self) -> &Self::CountType {
        &self.cnt
    }
    fn cnt_mut(&mut self) -> &mut Self::CountType {
        &mut self.cnt
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

impl<T> SubtreeCount for SplayData<T> {
    type SubtreeCountType = u32;
    fn subtree_count(&self) -> &Self::SubtreeCountType {
        &self.scnt
    }
}

pub struct Splay<T> {
    rep: SplayGeneric<SplayData<T>>,
}

impl<T> Splay<T> {
    pub fn new() -> Splay<T> {
        Splay {
            rep: SplayGeneric::new(),
        }
    }
    pub fn size(&self) -> u32 {
        self.rep.size()
    }
    pub fn root_key(&self) -> Option<&T> {
        self.rep.root_data().map(|d| d.key())
    }
}

impl<T: Ord> Splay<T> {
    pub fn insert(&mut self, key: T) {
        self.rep.insert(key)
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
    // find_first_ge
    pub fn lower_bound(&mut self, key: &T) -> bool {
        self.rep.find_first_ge(key)
    }
    // The remaining smallest will be the root.
    pub fn del_smaller(&mut self, key: &T) {
        self.rep.del_smaller(key)
    }
    pub fn query_kth(&mut self, k: u32) -> Option<&T> {
        if self.rep.query_kth(k) {
            self.root_key()
        } else {
            None
        }
    }
    pub fn check_sanity(&self) {
        self.rep.check_sanity()
    }
}

impl<T: std::fmt::Display> Splay<T> {
    pub fn print_tree(&self) {
        self.rep.print_tree()
    }
}
