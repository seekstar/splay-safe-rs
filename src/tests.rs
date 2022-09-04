#[cfg(test)]
mod tests {
    use crate::{BasicOps, Count, CountAdd, CountSub, Splay, WithKey};

    #[test]
    fn luogu_1090() {
        struct SplayData {
            key: i32,
            cnt: u32,
        }
        impl BasicOps for SplayData {
            type KeyType = i32;
            fn key(&self) -> &Self::KeyType {
                &self.key
            }
            fn push_up(&mut self, _: Option<&Self>, _: Option<&Self>) {}
        }
        impl WithKey for SplayData {
            fn with_key(key: Self::KeyType) -> Self {
                SplayData { key: key, cnt: 1 }
            }
        }
        impl Count for SplayData {
            type CountType = u32;
            fn cnt(&self) -> &Self::CountType {
                &self.cnt
            }
        }
        impl CountAdd for SplayData {
            fn cnt_add(&mut self, delta: &Self::CountType) {
                self.cnt += delta;
            }
        }
        impl CountSub for SplayData {
            fn cnt_sub(&mut self, delta: &Self::CountType) {
                self.cnt -= delta;
            }
        }
        let mut splay = Splay::<SplayData>::new();
        assert!(splay.insert_owned_key(1));
        assert!(splay.insert_owned_key(2));
        assert!(splay.insert_owned_key(9));
        assert_eq!(splay.query_smallest().unwrap().key(), &1);
        assert!(splay.deref_root());
        assert_eq!(splay.query_smallest().unwrap().key(), &2);
        assert!(splay.deref_root());
        splay.insert_owned_key_or_inc_cnt(3);
        assert_eq!(splay.query_smallest().unwrap().key(), &3);
        assert!(splay.deref_root());
        assert_eq!(splay.query_smallest().unwrap().key(), &9);
        assert!(splay.deref_root());
        splay.insert_owned_key_or_inc_cnt(12);
        assert_eq!(splay.query_smallest().unwrap().key(), &12);
        assert!(splay.deref_root());
        assert!(splay.query_smallest().is_none());
    }
}
