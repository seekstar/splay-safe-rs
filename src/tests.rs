/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#[cfg(test)]
mod common {
    use rand::distributions::Uniform;
    use rand::prelude::Distribution;
    use rand::Rng;
    pub fn rand_digits<R: Rng>(rng: &mut R, num: usize) -> Vec<u8> {
        let dist = Uniform::new(b'0', b'9' + 1);
        let mut ret = Vec::with_capacity(num);
        for _ in 0..num {
            ret.push(dist.sample(rng));
        }
        ret
    }
}

#[cfg(test)]
mod rand_with_key {
    use rand::distributions::{Distribution, Uniform};
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use rand_op::{rand_op, OpCnt};
    use std::cmp::Ordering;
    use std::collections::BTreeMap;
    use std::ops::Bound::{self, Excluded, Unbounded};
    use std::ops::RangeBounds;

    use super::common::rand_digits;
    use crate::{BasicOps, BasicOpsWithKey, SplayWithKey};

    struct GeneralEnv<K: Ord, V: BasicOpsWithKey<K>> {
        splay: SplayWithKey<K, V>,
        btree: BTreeMap<K, V>,
        key_len: usize,
        val_len: usize,
    }
    fn general_insert<K, V>(env: &mut GeneralEnv<K, V>, key: K, value: V)
    where
        K: Ord + Clone + core::fmt::Debug,
        V: Clone + BasicOpsWithKey<K> + core::cmp::PartialEq + core::fmt::Debug,
    {
        let old_key_value = env.splay.insert(key.clone(), value.clone());
        let old_value = old_key_value.map(|(old_key, old_value)| {
            assert_eq!(old_key, key);
            old_value
        });
        let std_old_value = env.btree.insert(key, value);
        assert_eq!(old_value, std_old_value);
    }
    fn general_query_first_lt<K, V>(env: &mut GeneralEnv<K, V>, key: &K)
    where
        K: Ord + Clone + std::fmt::Debug,
        V: BasicOpsWithKey<K> + Clone + std::fmt::Debug + std::cmp::PartialEq,
    {
        let std_ret = env.btree.range((Unbounded, Excluded(key))).next_back();
        let ret = env.splay.query_first_lt(key);
        if let Some((key, value)) = std_ret {
            assert!(ret.is_some());
            let ret = ret.unwrap();
            assert_eq!(&ret.key, key);
            assert_eq!(&ret.value, value);
        } else {
            assert!(ret.is_none());
        }
    }
    fn general_query_first_gt<K, V>(env: &mut GeneralEnv<K, V>, key: &K)
    where
        K: Ord + Clone + std::fmt::Debug,
        V: BasicOps + Clone + std::fmt::Debug + std::cmp::PartialEq,
    {
        let std_ret = env.btree.range((Excluded(key), Unbounded)).next();
        let ret = env.splay.query_first_gt(key);
        if let Some((key, value)) = std_ret {
            assert!(ret.is_some());
            let ret = ret.unwrap();
            assert_eq!(&ret.key, key);
            assert_eq!(&ret.value, value);
        } else {
            assert!(ret.is_none());
        }
    }
    fn general_query_range<K, V, Range>(
        env: &mut GeneralEnv<K, V>,
        range: Range,
    ) where
        K: Ord + Clone + std::fmt::Debug,
        V: BasicOpsWithKey<K> + Clone + std::fmt::Debug + std::cmp::PartialEq,
        Range: RangeBounds<K> + Clone,
    {
        let std_ret: Vec<(&K, &V)> =
            env.btree.range(range.clone()).into_iter().collect();
        let range = env.splay.range(range);
        let ret: Vec<(&K, &V)> = range
            .collect_data()
            .iter()
            .map(|kv| (&kv.key, &kv.value))
            .collect();
        assert_eq!(std_ret, ret);
    }
    fn general_iter_delete<K, V>(env: &mut GeneralEnv<K, V>, key: &K, n: usize)
    where
        K: Ord + Clone + std::fmt::Debug,
        V: BasicOpsWithKey<K> + Clone + std::fmt::Debug + std::cmp::PartialEq,
    {
        let mut range = env.btree.range(key..);
        let mut found = env.splay.splay_first_ge(key);
        let mut keys = Vec::new();
        for _ in 0..n {
            if let Some((k, v)) = range.next() {
                keys.push(k.clone());
                assert!(found);
                let ret;
                (ret, found) = env.splay.pop_root_splay_next().unwrap();
                assert_eq!(&ret.key, k);
                assert_eq!(&ret.value, v);
            } else {
                assert!(!found);
                break;
            }
        }
        for key in &keys {
            env.btree.remove(key);
        }
    }
    #[derive(Clone, Debug, PartialEq)]
    struct SplayValue {
        value: Vec<u8>,
    }
    impl BasicOps for SplayValue {}
    type Env = GeneralEnv<Vec<u8>, SplayValue>;
    fn insert(rng: &mut StdRng, env: &mut Env) -> bool {
        let key = rand_digits(rng, env.key_len);
        let value = SplayValue {
            value: rand_digits(rng, env.val_len),
        };
        general_insert(env, key, value);
        true
    }
    fn query_first_lt(rng: &mut StdRng, env: &mut Env) -> bool {
        let key = rand_digits(rng, env.key_len);
        general_query_first_lt(env, &key);
        true
    }
    fn query_first_gt(rng: &mut StdRng, env: &mut Env) -> bool {
        let key = rand_digits(rng, env.key_len);
        general_query_first_gt(env, &key);
        true
    }
    fn query_range(rng: &mut StdRng, env: &mut Env) -> bool {
        // 0: Included, 1: Excluded, 2: Unbounded
        let get_bound = |t: i32, k: Vec<u8>| match t {
            0 => Bound::Included(k),
            1 => Bound::Excluded(k),
            _ => unreachable!(),
        };
        let bound_dist = Uniform::from(0..3);
        let t1 = bound_dist.sample(rng);
        let t2 = bound_dist.sample(rng);
        let range = if t1 != 2 {
            let k1 = rand_digits(rng, env.key_len);
            if t2 != 2 {
                let k2 = rand_digits(rng, env.key_len);
                let res = k1.cmp(&k2);
                match res {
                    Ordering::Less => (get_bound(t1, k1), get_bound(t2, k2)),
                    Ordering::Greater => (get_bound(t2, k2), get_bound(t1, k1)),
                    Ordering::Equal => {
                        if t1 == 1 && t2 == 1 {
                            // To avoid panic
                            (Bound::Included(k1), Bound::Excluded(k2))
                        } else {
                            (get_bound(t1, k1), get_bound(t2, k2))
                        }
                    }
                }
            } else {
                (get_bound(t1, k1), Bound::Unbounded)
            }
        } else {
            (
                Bound::Unbounded,
                match t2 {
                    0 => Bound::Included(rand_digits(rng, env.key_len)),
                    1 => Bound::Excluded(rand_digits(rng, env.key_len)),
                    2 => Bound::Unbounded,
                    _ => unreachable!(),
                },
            )
        };
        general_query_range(env, range);
        true
    }
    fn iter_delete(rng: &mut StdRng, env: &mut Env) -> bool {
        let key = rand_digits(rng, env.key_len);
        general_iter_delete(env, &key, 10);
        true
    }
    fn rand_insert_query_first_lt_or_gt(magnitude: usize) {
        let n = 10u64.pow(magnitude as u32);
        rand_op(
            &mut StdRng::seed_from_u64(233),
            &mut Env {
                splay: SplayWithKey::new(),
                btree: BTreeMap::new(),
                key_len: magnitude,
                val_len: magnitude,
            },
            vec![
                OpCnt::new(insert, n),
                OpCnt::new(query_first_lt, n),
                OpCnt::new(query_first_gt, n),
            ],
        );
    }
    #[test]
    fn rand_insert_query_first_lt_or_gt_1e1() {
        rand_insert_query_first_lt_or_gt(1);
    }
    #[test]
    fn rand_insert_query_first_lt_or_gt_1e2() {
        rand_insert_query_first_lt_or_gt(2);
    }
    #[test]
    fn rand_insert_query_first_lt_or_gt_1e3() {
        rand_insert_query_first_lt_or_gt(3);
    }
    #[test]
    fn rand_insert_query_first_lt_or_gt_1e4() {
        rand_insert_query_first_lt_or_gt(4);
    }
    #[test]
    fn rand_insert_query_first_lt_or_gt_1e5() {
        rand_insert_query_first_lt_or_gt(5);
    }

    fn rand_insert_query_long_range(magnitude: usize) {
        let n = 10u64.pow(magnitude as u32);
        rand_op(
            &mut StdRng::seed_from_u64(233),
            &mut Env {
                splay: SplayWithKey::new(),
                btree: BTreeMap::new(),
                key_len: magnitude,
                val_len: magnitude,
            },
            vec![
                OpCnt::new(insert, n),
                OpCnt::new(query_range, (n as f64).sqrt() as u64),
            ],
        );
    }
    #[test]
    fn rand_insert_query_long_range_1e1() {
        rand_insert_query_long_range(1);
    }
    #[test]
    fn rand_insert_query_range_1e2() {
        rand_insert_query_long_range(2);
    }
    #[test]
    fn rand_insert_query_range_1e3() {
        rand_insert_query_long_range(3);
    }
    #[test]
    fn rand_insert_query_range_1e4() {
        rand_insert_query_long_range(4);
    }
    #[test]
    fn rand_insert_query_range_1e5() {
        rand_insert_query_long_range(5);
    }

    #[test]
    fn pop_root_splay_next_1() {
        let mut splay = SplayWithKey::<usize, ()>::new();
        assert_eq!(splay.pop_root_splay_next(), None);
        splay.insert(1, ());
        let (ret, has_next) = splay.pop_root_splay_next().unwrap();
        assert!(!has_next);
        assert_eq!(ret.key, 1);
        splay.insert(1, ());
        splay.insert(2, ());
        splay.query_smallest();
        let (ret, has_next) = splay.pop_root_splay_next().unwrap();
        assert!(has_next);
        assert_eq!(ret.key, 1);
        let (ret, has_next) = splay.pop_root_splay_next().unwrap();
        assert!(!has_next);
        assert_eq!(ret.key, 2);
    }

    fn seq_insert_pop_root_splay_next(n: usize) {
        let mut splay = SplayWithKey::<usize, ()>::new();
        for i in 0..n {
            splay.insert(i, ());
        }
        assert_eq!(splay.query_smallest().unwrap().key, 0);
        for i in 0..n {
            let (ret, has_next) = splay.pop_root_splay_next().unwrap();
            assert_eq!(ret.key, i);
            if i == n - 1 {
                assert!(!has_next);
            } else {
                assert!(has_next);
            }
        }
        assert!(splay.is_empty());
    }
    #[test]
    fn seq_insert_pop_root_splay_next_1e1() {
        seq_insert_pop_root_splay_next(10);
    }

    fn rand_insert_iter_delete(magnitude: usize) {
        let n = 10u64.pow(magnitude as u32);
        rand_op(
            &mut StdRng::seed_from_u64(233),
            &mut Env {
                splay: SplayWithKey::new(),
                btree: BTreeMap::new(),
                key_len: magnitude,
                val_len: magnitude,
            },
            vec![OpCnt::new(insert, n), OpCnt::new(iter_delete, n / 100)],
        );
    }
    #[test]
    fn rand_insert_iter_delete_1e1() {
        rand_insert_iter_delete(1);
    }
    #[test]
    fn rand_insert_iter_delete_1e2() {
        rand_insert_iter_delete(2);
    }
    #[test]
    fn rand_insert_iter_delete_1e3() {
        rand_insert_iter_delete(3);
    }
    #[test]
    fn rand_insert_iter_delete_1e4() {
        rand_insert_iter_delete(4);
    }
    #[test]
    fn rand_insert_iter_delete_1e5() {
        rand_insert_iter_delete(5);
    }
}

#[cfg(test)]
mod rand_with_count {
    use std::fmt::Debug;

    use rand::{prelude::Distribution, rngs::StdRng, Rng, SeedableRng};
    use rand_op::{rand_op, OpCnt};

    use crate::{RankTree, Splay};

    struct GeneralEnv<T> {
        splay: RankTree<T>,
        vec: Vec<T>,
    }
    fn general_insert<T>(env: &mut GeneralEnv<T>, index: usize, data: T)
    where
        T: Clone,
    {
        env.splay.insert_at_index(index, data.clone().into());
        env.vec.insert(index.into(), data);
    }
    fn general_find_by_index<T>(env: &mut GeneralEnv<T>, index: usize)
    where
        T: PartialEq + Debug,
    {
        let std_ret = env.vec.get(index);
        let k = index + 1;
        let found = env.splay.splay_kth(k);
        if let Some(data) = std_ret {
            assert!(found);
            assert_eq!(data, &env.splay.root_data().unwrap().value);
        } else {
            assert!(!found);
        }
    }
    type Env = GeneralEnv<u64>;
    fn insert(rng: &mut StdRng, env: &mut Env) -> bool {
        let index =
            rand::distributions::Uniform::new(0, env.vec.len() + 1).sample(rng);
        general_insert(env, index, rng.gen());
        true
    }
    fn find(rng: &mut StdRng, env: &mut Env) -> bool {
        let index =
            rand::distributions::Uniform::new(0, env.vec.len()).sample(rng);
        general_find_by_index(env, index);
        true
    }
    fn rand_insert_find(magnitude: usize) {
        let n = 10u64.pow(magnitude as u32);
        rand_op(
            &mut StdRng::seed_from_u64(233),
            &mut Env {
                splay: Splay::new(),
                vec: Vec::new(),
            },
            vec![OpCnt::new(insert, n), OpCnt::new(find, n)],
        );
    }
    #[test]
    fn rand_insert_find_1e1() {
        rand_insert_find(1);
    }
    #[test]
    fn rand_insert_find_1e2() {
        rand_insert_find(2);
    }
    #[test]
    fn rand_insert_find_1e3() {
        rand_insert_find(3);
    }
    #[test]
    fn rand_insert_find_1e4() {
        rand_insert_find(4);
    }
}

#[cfg(test)]
mod online_judge {
    use crate::{BasicOps, CountedRankTreeWithKey, KeyValue, SplayWithKey};
    use std::ops::Bound::Included;

    #[test]
    fn luogu_1486() {
        let mut splay = CountedRankTreeWithKey::<i32>::new();
        splay.insert_or_inc_cnt(60);
        splay.insert_or_inc_cnt(70);
        assert_eq!(splay.size(), 2);
        assert_eq!(splay.query_kth_key(1), Some(&60));
        splay.insert_or_inc_cnt(80);
        splay.del_smaller(&75);
        assert_eq!(splay.size(), 1);
        assert_eq!(splay.query_kth_key(1), Some(&80));
        assert_eq!(splay.query_kth_key(2), None);
    }

    #[test]
    fn luogu_1503() {
        let mut destroyed = Vec::new();
        let mut splay = SplayWithKey::<u32>::new();
        let n = 7;
        let d =
            |splay: &mut SplayWithKey<_, _>, destroyed: &mut Vec<u32>, x| {
                destroyed.push(x);
                splay.insert(x, ());
            };
        let r = |splay: &mut SplayWithKey<_, _>, destroyed: &mut Vec<u32>| {
            let x = destroyed.pop().unwrap();
            splay.remove(&x);
        };
        let q = |splay: &mut SplayWithKey<u32>, x, expected| {
            let begin = match splay.query_first_le(&x) {
                Some(d) => d.key + 1,
                None => 1,
            };
            let end = match splay.query_first_ge(&x) {
                Some(d) => d.key,
                None => n + 1,
            };
            let ans = if end <= begin { 0 } else { end - begin };
            assert_eq!(ans, expected);
        };
        d(&mut splay, &mut destroyed, 3);
        d(&mut splay, &mut destroyed, 6);
        d(&mut splay, &mut destroyed, 5);
        q(&mut splay, 4, 1);
        q(&mut splay, 5, 0);
        r(&mut splay, &mut destroyed);
        q(&mut splay, 4, 2);
        r(&mut splay, &mut destroyed);
        q(&mut splay, 4, 4);
    }

    #[test]
    fn luogu_1090() {
        let mut splay =
            SplayWithKey::<i32, u32>::from(vec![(1, 1), (2, 1), (9, 1)]);
        assert_eq!(splay.query_smallest().unwrap().key, 1);
        assert!(splay.deref_root());
        assert_eq!(splay.query_smallest().unwrap().key, 2);
        assert!(splay.deref_root());
        splay.insert_or_inc_cnt(3);
        assert_eq!(splay.query_smallest().unwrap().key, 3);
        assert!(splay.deref_root());
        assert_eq!(splay.query_smallest().unwrap().key, 9);
        assert!(splay.deref_root());
        splay.insert_or_inc_cnt(12);
        assert_eq!(splay.query_smallest().unwrap().key, 12);
        assert!(splay.deref_root());
        assert!(splay.query_smallest().is_none());
    }

    #[test]
    fn luogu_2073() {
        #[derive(PartialEq, Debug)]
        struct SplayValue {
            value: i32,
        }
        impl From<i32> for SplayValue {
            fn from(value: i32) -> Self {
                Self { value }
            }
        }
        impl BasicOps for SplayValue {}
        let mut splay = SplayWithKey::<i32, SplayValue>::new();
        assert!(splay.insert(1, 1.into()).is_none());
        assert!(splay.insert(5, 2.into()).is_none());
        assert_eq!(
            splay.pop_largest(),
            Some(KeyValue {
                key: 5,
                value: 2.into()
            })
        );
        assert!(splay.insert(3, 3.into()).is_none());
        assert_eq!(
            splay.pop_smallest(),
            Some(KeyValue {
                key: 1,
                value: 1.into()
            })
        );
        assert!(splay.insert(2, 5.into()).is_none());
        assert_eq!(
            splay.collect_data(),
            vec![
                &KeyValue {
                    key: 2,
                    value: 5.into()
                },
                &KeyValue {
                    key: 3,
                    value: 3.into()
                },
            ]
        );
        assert_eq!(
            splay.take_all_data(),
            vec![
                KeyValue {
                    key: 2,
                    value: 5.into()
                },
                KeyValue {
                    key: 3,
                    value: 3.into()
                },
            ]
        );
    }

    #[test]
    fn luogu_3368() {
        struct SplayValue {
            value: i32,
            lazy: i32,
        }
        impl BasicOps for SplayValue {
            fn push_down(
                &mut self,
                lc: Option<&mut Self>,
                rc: Option<&mut Self>,
            ) {
                if self.lazy != 0 {
                    if let Some(c) = lc {
                        c.value += self.lazy;
                        c.lazy += self.lazy;
                    }
                    if let Some(c) = rc {
                        c.value += self.lazy;
                        c.lazy += self.lazy;
                    }
                    self.lazy = 0;
                }
            }
        }
        fn range_add(
            splay: &mut SplayWithKey<i32, SplayValue>,
            x: i32,
            y: i32,
            k: i32,
        ) {
            if let Some(mut v) =
                splay.range((Included(x), Included(y))).root_value_mut()
            {
                v.value += k;
                v.lazy += k;
            }
        }
        fn point_query(
            splay: &mut SplayWithKey<i32, SplayValue>,
            x: i32,
        ) -> i32 {
            splay.get(&x).unwrap().value
        }
        let mut splay = SplayWithKey::construct(
            vec![(1, 1), (2, 5), (3, 4), (4, 2), (5, 3)],
            |(key, value)| KeyValue {
                key,
                value: SplayValue { value, lazy: 0 },
            },
        );
        // 1, 5, 4, 2, 3
        range_add(&mut splay, 2, 4, 2);
        // 1, 7, 6, 4, 3
        assert_eq!(point_query(&mut splay, 3), 6);
        range_add(&mut splay, 1, 5, -1);
        // 0, 6, 5, 3, 2
        range_add(&mut splay, 3, 5, 7);
        // 0, 6, 12, 10, 9
        assert_eq!(point_query(&mut splay, 4), 10);

        // Additional
        let range = splay.range((Included(6), Included(6)));
        assert!(range.collect_data().is_empty());
        let range = splay.range((Included(0), Included(0)));
        assert!(range.collect_data().is_empty());
        let range = splay.range((Included(2), Included(2)));
        assert_eq!(
            range
                .take_all_data()
                .iter()
                .map(|x| (x.key, x.value.value))
                .collect::<Vec<_>>(),
            vec![(2, 6)],
        );
        // (1, 0), (3, 12), (4, 10), (5, 9)
        assert_eq!(
            splay
                .collect_data()
                .iter()
                .map(|x| (x.key, x.value.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (3, 12), (4, 10), (5, 9)],
        );

        let range = splay.range((Included(3), Included(4)));
        assert_eq!(
            range
                .take_all_data()
                .iter()
                .map(|x| (x.key, x.value.value))
                .collect::<Vec<_>>(),
            vec![(3, 12), (4, 10)],
        );
        // (1, 0), (5, 9)
        assert_eq!(
            splay
                .collect_data()
                .iter()
                .map(|x| (x.key, x.value.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (5, 9)],
        );

        let range = splay.range((Included(0), Included(6)));
        assert_eq!(
            range
                .take_all_data()
                .iter()
                .map(|x| (x.key, x.value.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (5, 9)],
        );
        assert!(splay.collect_data().is_empty());
    }

    #[test]
    fn luogu_1428() {
        fn num_less_than(
            splay: &mut CountedRankTreeWithKey<u8, u8>,
            x: u8,
        ) -> u8 {
            match splay.to_range().lt(&x).root_data() {
                Some(d) => d.value.scnt,
                None => 0,
            }
        }
        let mut splay = CountedRankTreeWithKey::<u8, u8>::new();
        assert_eq!(num_less_than(&mut splay, 4), 0);
        splay.insert_or_inc_cnt(4);
        assert_eq!(num_less_than(&mut splay, 3), 0);
        splay.insert_or_inc_cnt(3);
        assert_eq!(num_less_than(&mut splay, 0), 0);
        splay.insert_or_inc_cnt(0);
        assert_eq!(num_less_than(&mut splay, 5), 3);
        splay.insert_or_inc_cnt(5);
        assert_eq!(num_less_than(&mut splay, 1), 1);
        splay.insert_or_inc_cnt(1);
        assert_eq!(num_less_than(&mut splay, 2), 2);
        splay.insert_or_inc_cnt(2);
    }
}
