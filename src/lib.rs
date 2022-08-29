use std::cmp::Ordering;

#[derive(Clone, PartialEq)]
#[cfg(feature = "rank")]
struct Node<T> {
    c: [Option<Box<Node<T>>>; 2],
    // Number of elements in this node
    cnt: u32,
    // Number of elements in the subtree
    scnt: u32,
    key: T,
}

#[derive(Clone, PartialEq)]
#[cfg(not(feature = "rank"))]
struct Node<T> {
    c: [Option<Box<Node<T>>>; 2],
    // Number of elements in this node
    cnt: u32,
    key: T,
}

impl<T> Node<T> {
    #[cfg(feature = "rank")]
    fn new(key: T) -> Node<T> {
        Node {
            c: [None, None],
            cnt: 1,
            scnt: 1,
            key: key,
        }
    }
    #[cfg(not(feature = "rank"))]
    fn new(key: T) -> Node<T> {
        Node {
            c: [None, None],
            cnt: 1,
            key: key,
        }
    }
}

impl<T> Node<T> {
    #[cfg(feature = "rank")]
    fn push_up(&mut self) {
        self.scnt = self.cnt;
        if let Some(ref c) = self.c[0] {
            self.scnt += c.scnt;
        }
        if let Some(ref c) = self.c[1] {
            self.scnt += c.scnt;
        }
    }
    #[cfg(not(feature = "rank"))]
    fn push_up(&mut self) {}

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

pub struct Splay<T> {
    root: Option<Box<Node<T>>>,
}

impl<T: std::cmp::Ord> Splay<T> {
    pub fn new() -> Splay<T> {
        Splay { root: None }
    }

    fn rotate_to_root(
        &mut self,
        mut x: Box<Node<T>>,
        path: Vec<(Box<Node<T>>, bool)>,
    ) {
        x.splay(path);
        self.root = Some(x);
    }

    #[cfg(feature = "rank")]
    pub fn size(&self) -> u32 {
        match self.root {
            Some(ref root) => root.scnt,
            None => 0,
        }
    }
    pub fn root_key(&self) -> Option<&T> {
        self.root.as_ref().map(|root| &root.key)
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
    pub fn insert(&mut self, key: T) {
        let tmp = self.root.take();
        let mut cur = match tmp {
            Some(root) => root,
            None => {
                self.root = Some(Box::new(Node::new(key)));
                return;
            }
        };
        let mut path = Vec::new();
        loop {
            if cur.key == key {
                cur.cnt += 1;
                // cur.scnt will be updated by subsequent rotate_to_root
                break;
            }
            let side = cur.key < key;
            let next = cur.c[side as usize].take();
            path.push((cur, side));
            if let Some(nex) = next {
                cur = nex
            } else {
                cur = Box::new(Node::new(key));
                // cur <-> prev, cur.scnt and prev.scnt will be updated by
                // subsequent rotate_to_root
                break;
            }
        }
        self.rotate_to_root(cur, path);
    }

    pub fn find(&mut self, key: &T) -> bool {
        let mut next = self.root.take();
        let mut path = Vec::new();
        while let Some(mut cur) = next {
            let res = key.cmp(&cur.key);
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
    pub fn delete(&mut self, key: &T) -> bool {
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
        key: &T,
        ge: bool,
    ) -> (Vec<(Box<Node<T>>, bool)>, usize) {
        let mut next = self.root.take();
        let mut path = Vec::new();
        let mut ans_depth = 0;
        while let Some(mut cur) = next {
            let res = cur.key.cmp(key);
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
    fn find_first_le_or_ge(&mut self, key: &T, ge: bool) -> bool {
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
    pub fn find_first_le(&mut self, key: &T) -> bool {
        self.find_first_le_or_ge(key, false)
    }
    // find_first_ge
    pub fn lower_bound(&mut self, key: &T) -> bool {
        return self.find_first_le_or_ge(key, true);
    }

    // The remaining smallest will be the root.
    pub fn del_smaller(&mut self, key: &T) {
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

    // If found, then the node will be the root, and return true.
    // If not found, then the last accessed node will be the root, and return
    // false.
    #[cfg(feature = "rank")]
    fn query_kth_no_ret_val(&mut self, mut k: u32) -> bool {
        let mut next = self.root.take();
        let mut path = Vec::new();
        while let Some(mut cur) = next {
            let lscnt = if let Some(ref lc) = cur.c[0] {
                lc.scnt
            } else {
                0
            };
            let cur_cnt = cur.cnt;
            if lscnt < k && lscnt + cur_cnt >= k {
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
    #[cfg(feature = "rank")]
    pub fn query_kth(&mut self, k: u32) -> Option<&T> {
        let found = self.query_kth_no_ret_val(k);
        if found {
            return Some(&self.root.as_ref().unwrap().key);
        } else {
            return None;
        }
    }

    #[cfg(feature = "rank")]
    fn check_sanity_subtree(&self, rt: &Box<Node<T>>) {
        let mut scnt = rt.cnt;
        if let Some(ref c) = rt.c[0] {
            scnt += c.scnt;
            self.check_sanity_subtree(c);
        }
        if let Some(ref c) = rt.c[1] {
            scnt += c.scnt;
            self.check_sanity_subtree(c);
        }
        assert_eq!(scnt, rt.scnt);
    }
    // Only for DEBUG
    #[cfg(feature = "rank")]
    pub fn check_sanity(&self) {
        if let Some(ref root) = self.root {
            self.check_sanity_subtree(root);
        }
    }
}

impl<T: std::cmp::Ord + std::fmt::Display> Splay<T> {
    fn __print_subtree_non_empty(&self, rt: &Node<T>, str: &mut String) {
        let ori_len = str.len();
        let node = if rt.cnt == 1 {
            format!("{}", rt.key)
        } else {
            format!("{}*{}", rt.key, rt.cnt)
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
    fn __print_subtree(&self, rt: &Option<Box<Node<T>>>, str: &mut String) {
        if let Some(node) = rt {
            self.__print_subtree_non_empty(node, str);
        } else {
            println!("/\\");
        }
    }
    fn print_subtree(&self, rt: &Option<Box<Node<T>>>) {
        self.__print_subtree(rt, &mut String::new());
    }
    pub fn print_tree(&self) {
        self.print_subtree(&self.root);
    }
}
