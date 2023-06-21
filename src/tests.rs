/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#[cfg(test)]
mod rand_tests {
    use rand::distributions::{Distribution, Uniform};
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::cmp::Ordering;
    use std::collections::BTreeMap;
    use std::ops::Bound::{self, Excluded, Unbounded};
    use std::ops::RangeBounds;

    use crate::{BasicOps, SplayWithKey, WithKey};

    fn rand_digits<R: Rng>(rng: &mut R, num: usize) -> Vec<u8> {
        let dist = Uniform::new(b'0', b'9' + 1);
        let mut ret = Vec::with_capacity(num);
        for _ in 0..num {
            ret.push(dist.sample(rng));
        }
        ret
    }

    struct Env<'a, 'b, 'c, T: WithKey>
    where
        T::KeyType: Ord,
    {
        rng: &'a mut StdRng,
        splay: &'b mut SplayWithKey<T>,
        btree: &'c mut BTreeMap<T::KeyType, T>,
        key_len: usize,
        val_len: usize,
    }
    struct OpNum {
        insert: usize,
        query_first_lt: usize,
        query_first_gt: usize,
        range: usize,
    }
    impl Default for OpNum {
        fn default() -> OpNum {
            OpNum {
                insert: 0,
                query_first_lt: 0,
                query_first_gt: 0,
                range: 0,
            }
        }
    }
    fn try_insert<'a, 'b, 'c, T>(
        env: &mut Env<'a, 'b, 'c, T>,
        key: T::KeyType,
        value: T,
    ) where
        T::KeyType: Ord + Clone,
        T: WithKey + Clone,
    {
        let mut std_exists = false;
        let succeed = env.splay.insert(&key, value.clone());
        env.btree
            .entry(key.clone())
            .and_modify(|_| std_exists = true)
            .or_insert_with(|| {
                std_exists = false;
                value
            });
        assert_eq!(std_exists, !succeed);
    }
    fn query_first_lt<'a, 'b, 'c, T>(
        env: &mut Env<'a, 'b, 'c, T>,
        key: &T::KeyType,
    ) where
        T::KeyType: Ord + Clone + std::fmt::Debug,
        T: BasicOps + WithKey + Clone + std::fmt::Debug + std::cmp::PartialEq,
    {
        let std_ret = env.btree.range((Unbounded, Excluded(key))).next_back();
        let ret = env.splay.query_first_lt(key);
        if let Some((key, value)) = std_ret {
            assert!(ret.is_some());
            let ret = ret.unwrap();
            assert_eq!(ret.key(), key);
            assert_eq!(ret, value);
        } else {
            assert!(ret.is_none());
        }
    }
    fn query_first_gt<'a, 'b, 'c, T>(
        env: &mut Env<'a, 'b, 'c, T>,
        key: &T::KeyType,
    ) where
        T::KeyType: Ord + Clone + std::fmt::Debug,
        T: BasicOps + WithKey + Clone + std::fmt::Debug + std::cmp::PartialEq,
    {
        let std_ret = env.btree.range((Excluded(key), Unbounded)).next();
        let ret = env.splay.query_first_gt(key);
        if let Some((key, value)) = std_ret {
            assert!(ret.is_some());
            let ret = ret.unwrap();
            assert_eq!(ret.key(), key);
            assert_eq!(ret, value);
        } else {
            assert!(ret.is_none());
        }
    }
    fn query_range<'a, 'b, 'c, T, Range>(
        env: &mut Env<'a, 'b, 'c, T>,
        range: Range,
    ) where
        T::KeyType: Ord + Clone + std::fmt::Debug,
        T: BasicOps + WithKey + Clone + std::fmt::Debug + std::cmp::PartialEq,
        Range: RangeBounds<T::KeyType> + Clone,
    {
        let std_ret: Vec<&T> = env
            .btree
            .range(range.clone())
            .into_iter()
            .map(|p| p.1)
            .collect();
        let range = env.splay.range(range);
        let ret = range.collect_data();
        assert_eq!(std_ret, ret);
    }
    fn rand_op(mut num: OpNum, key_len: usize, val_len: usize) {
        #[derive(Clone, Debug, PartialEq)]
        struct SplayData {
            key: Vec<u8>,
            value: Vec<u8>,
        }
        impl WithKey for SplayData {
            type KeyType = Vec<u8>;
            fn key(&self) -> &Vec<u8> {
                &self.key
            }
        }
        impl BasicOps for SplayData {}
        let mut rng = StdRng::seed_from_u64(233);
        let mut splay = SplayWithKey::<SplayData>::new();
        let mut btree = BTreeMap::<Vec<u8>, SplayData>::new();
        let mut env = Env {
            rng: &mut rng,
            splay: &mut splay,
            btree: &mut btree,
            key_len,
            val_len,
        };
        let mut tot =
            num.insert + num.query_first_lt + num.query_first_gt + num.range;
        while tot > 0 {
            let op_dist = Uniform::from(0..tot);
            let mut rand_num = op_dist.sample(env.rng);
            if rand_num < num.insert {
                num.insert -= 1;
                tot -= 1;
                let data = SplayData {
                    key: rand_digits(env.rng, env.key_len),
                    value: rand_digits(env.rng, env.val_len),
                };
                try_insert(&mut env, data.key.clone(), data);
                continue;
            }
            rand_num -= num.insert;
            if rand_num < num.query_first_lt {
                num.query_first_lt -= 1;
                tot -= 1;
                let key = rand_digits(env.rng, env.key_len);
                query_first_lt(&mut env, &key);
                continue;
            }
            rand_num -= num.query_first_lt;
            if rand_num < num.query_first_gt {
                num.query_first_gt -= 1;
                tot -= 1;
                let key = rand_digits(env.rng, env.key_len);
                query_first_gt(&mut env, &key);
                continue;
            }
            rand_num -= num.query_first_gt;
            if rand_num < num.range {
                num.range -= 1;
                tot -= 1;
                // 0: Included, 1: Excluded, 2: Unbounded
                let get_bound = |t: i32, k: Vec<u8>| match t {
                    0 => Bound::Included(k),
                    1 => Bound::Excluded(k),
                    _ => unreachable!(),
                };
                let bound_dist = Uniform::from(0..3);
                let t1 = bound_dist.sample(env.rng);
                let t2 = bound_dist.sample(env.rng);
                let range = if t1 != 2 {
                    let k1 = rand_digits(env.rng, env.key_len);
                    if t2 != 2 {
                        let k2 = rand_digits(env.rng, env.key_len);
                        let res = k1.cmp(&k2);
                        match res {
                            Ordering::Less => {
                                (get_bound(t1, k1), get_bound(t2, k2))
                            }
                            Ordering::Greater => {
                                (get_bound(t2, k2), get_bound(t1, k1))
                            }
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
                            0 => Bound::Included(rand_digits(
                                env.rng,
                                env.key_len,
                            )),
                            1 => Bound::Excluded(rand_digits(
                                env.rng,
                                env.key_len,
                            )),
                            2 => Bound::Unbounded,
                            _ => unreachable!(),
                        },
                    )
                };
                query_range(&mut env, range);
                continue;
            }
            // rand_num -= num.range;
            unreachable!();
        }
        assert_eq!(num.insert, 0);
        assert_eq!(num.query_first_lt, 0);
        assert_eq!(num.query_first_gt, 0);
    }
    fn rand_insert_query_first_lt_or_gt(magnitude: usize) {
        let n = 10usize.pow(magnitude as u32);
        rand_op(
            OpNum {
                insert: n,
                query_first_lt: n,
                query_first_gt: n,
                ..Default::default()
            },
            magnitude,
            magnitude,
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
        let n = 10usize.pow(magnitude as u32);
        rand_op(
            OpNum {
                insert: n,
                range: (n as f64).sqrt() as usize,
                ..Default::default()
            },
            magnitude,
            magnitude,
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
}

#[cfg(test)]
mod online_judge {
    use crate::{
        BasicOps, Count, CountAdd, CountSub, RankTree, SplayWithKey, WithKey,
        WithValue,
    };
    use std::ops::Bound::Included;

    #[test]
    fn luogu_1486() {
        let mut splay = RankTree::<i32>::new();
        splay.insert(60);
        splay.insert(70);
        assert_eq!(splay.size(), 2);
        assert_eq!(splay.query_kth(1), Some(&60));
        splay.insert(80);
        splay.del_smaller(&75);
        assert_eq!(splay.size(), 1);
        assert_eq!(splay.query_kth(1), Some(&80));
        assert_eq!(splay.query_kth(2), None);
    }

    #[test]
    fn luogu_1503() {
        let mut destroyed = Vec::new();
        let mut splay = SplayWithKey::<u32>::new();
        let n = 7;
        let d =
            |splay: &mut SplayWithKey<_, _>, destroyed: &mut Vec<u32>, x| {
                destroyed.push(x);
                splay.insert_owned_key(x);
            };
        let r = |splay: &mut SplayWithKey<_, _>, destroyed: &mut Vec<u32>| {
            let x = destroyed.pop().unwrap();
            splay.remove(&x);
        };
        let q = |splay: &mut SplayWithKey<u32>, x, expected| {
            let begin = match splay.query_first_le(&x) {
                Some(d) => d + 1,
                None => 1,
            };
            let end = match splay.query_first_ge(&x) {
                Some(d) => *d,
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
        struct SplayData {
            key: i32,
            cnt: u32,
        }
        impl BasicOps for SplayData {
            fn push_up(&mut self, _: Option<&Self>, _: Option<&Self>) {}
        }
        impl WithKey for SplayData {
            type KeyType = i32;
            fn key(&self) -> &i32 {
                &self.key
            }
        }
        impl From<i32> for SplayData {
            fn from(key: i32) -> Self {
                SplayData { key, cnt: 1 }
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
        let mut splay = SplayWithKey::<SplayData>::from(vec![1, 2, 9]);
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

    #[test]
    fn luogu_2073() {
        #[derive(PartialEq, Debug)]
        struct SplayData {
            key: i32,
            value: i32,
        }
        impl BasicOps for SplayData {
            fn push_up(&mut self, _: Option<&Self>, _: Option<&Self>) {}
        }
        impl WithKey for SplayData {
            type KeyType = i32;
            fn key(&self) -> &i32 {
                &self.key
            }
        }
        let mut splay = SplayWithKey::<SplayData>::new();
        assert!(splay
            .insert_owned_key_with_func(1, |key| SplayData { key, value: 1 }));
        assert!(splay
            .insert_owned_key_with_func(5, |key| SplayData { key, value: 2 }));
        assert_eq!(splay.pop_largest(), Some(SplayData { key: 5, value: 2 }));
        assert!(splay
            .insert_owned_key_with_func(3, |key| SplayData { key, value: 3 }));
        assert_eq!(splay.pop_smallest(), Some(SplayData { key: 1, value: 1 }));
        assert!(splay
            .insert_owned_key_with_func(2, |key| SplayData { key, value: 5 }));
        assert_eq!(
            splay.collect_data(),
            vec![
                &SplayData { key: 2, value: 5 },
                &SplayData { key: 3, value: 3 },
            ]
        );
        assert_eq!(
            splay.take_all_data(),
            vec![
                SplayData { key: 2, value: 5 },
                SplayData { key: 3, value: 3 },
            ]
        );
    }

    #[test]
    fn luogu_3368() {
        struct SplayValue {
            value: i32,
            lazy: i32,
        }
        struct SplayData {
            key: i32,
            other: SplayValue,
        }
        impl BasicOps for SplayData {
            fn push_down(
                &mut self,
                lc: Option<&mut Self>,
                rc: Option<&mut Self>,
            ) {
                if self.other.lazy != 0 {
                    if let Some(c) = lc {
                        c.other.value += self.other.lazy;
                        c.other.lazy += self.other.lazy;
                    }
                    if let Some(c) = rc {
                        c.other.value += self.other.lazy;
                        c.other.lazy += self.other.lazy;
                    }
                    self.other.lazy = 0;
                }
            }
        }
        impl WithKey for SplayData {
            type KeyType = i32;
            fn key(&self) -> &i32 {
                &self.key
            }
        }
        impl WithValue for SplayData {
            type ValueType = SplayValue;
            fn value(&self) -> &Self::ValueType {
                &self.other
            }
            fn key_immut_value_mut(
                &mut self,
            ) -> (&Self::KeyType, &mut Self::ValueType) {
                (&self.key, &mut self.other)
            }
        }
        fn range_add(
            splay: &mut SplayWithKey<SplayData>,
            x: i32,
            y: i32,
            k: i32,
        ) {
            let mut range = splay.range((Included(x), Included(y)));
            range.update_root_value(|_, v| {
                v.value += k;
                v.lazy += k;
            });
        }
        fn point_query(splay: &mut SplayWithKey<SplayData>, x: i32) -> i32 {
            assert!(splay.splay(&x));
            splay.root_data().unwrap().other.value
        }
        let mut splay = SplayWithKey::from_with_constructor(
            vec![(1, 1), (2, 5), (3, 4), (4, 2), (5, 3)],
            |(key, value)| SplayData {
                key,
                other: SplayValue { value, lazy: 0 },
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
                .map(|x| (x.key, x.other.value))
                .collect::<Vec<_>>(),
            vec![(2, 6)],
        );
        // (1, 0), (3, 12), (4, 10), (5, 9)
        assert_eq!(
            splay
                .collect_data()
                .iter()
                .map(|x| (x.key, x.other.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (3, 12), (4, 10), (5, 9)],
        );

        let range = splay.range((Included(3), Included(4)));
        assert_eq!(
            range
                .take_all_data()
                .iter()
                .map(|x| (x.key, x.other.value))
                .collect::<Vec<_>>(),
            vec![(3, 12), (4, 10)],
        );
        // (1, 0), (5, 9)
        assert_eq!(
            splay
                .collect_data()
                .iter()
                .map(|x| (x.key, x.other.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (5, 9)],
        );

        let range = splay.range((Included(0), Included(6)));
        assert_eq!(
            range
                .take_all_data()
                .iter()
                .map(|x| (x.key, x.other.value))
                .collect::<Vec<_>>(),
            vec![(1, 0), (5, 9)],
        );
        assert!(splay.collect_data().is_empty());
    }

    #[test]
    fn luogu_1428() {
        struct SplayData {
            key: u8,
            cnt: u8,
            scnt: u8,
        }
        impl BasicOps for SplayData {
            fn push_up(&mut self, lc: Option<&Self>, rc: Option<&Self>) {
                self.scnt = self.cnt;
                if let Some(c) = lc {
                    self.scnt += c.scnt;
                }
                if let Some(c) = rc {
                    self.scnt += c.scnt;
                }
            }
        }
        impl WithKey for SplayData {
            type KeyType = u8;
            fn key(&self) -> &u8 {
                &self.key
            }
        }
        impl From<u8> for SplayData {
            fn from(key: u8) -> Self {
                SplayData {
                    key,
                    cnt: 1,
                    scnt: 1,
                }
            }
        }
        impl Count for SplayData {
            type CountType = u8;
            fn cnt(&self) -> &Self::CountType {
                &self.cnt
            }
        }
        impl CountAdd for SplayData {
            fn cnt_add(&mut self, delta: &Self::CountType) {
                self.cnt += delta;
            }
        }
        fn num_less_than(splay: &mut SplayWithKey<SplayData>, x: u8) -> u8 {
            match splay.to_range().lt(&x).root_data() {
                Some(d) => d.scnt,
                None => 0,
            }
        }
        let mut splay = SplayWithKey::<SplayData>::new();
        assert_eq!(num_less_than(&mut splay, 4), 0);
        splay.insert_owned_key_or_inc_cnt(4);
        assert_eq!(num_less_than(&mut splay, 3), 0);
        splay.insert_owned_key_or_inc_cnt(3);
        assert_eq!(num_less_than(&mut splay, 0), 0);
        splay.insert_owned_key_or_inc_cnt(0);
        assert_eq!(num_less_than(&mut splay, 5), 3);
        splay.insert_owned_key_or_inc_cnt(5);
        assert_eq!(num_less_than(&mut splay, 1), 1);
        splay.insert_owned_key_or_inc_cnt(1);
        assert_eq!(num_less_than(&mut splay, 2), 2);
        splay.insert_owned_key_or_inc_cnt(2);
    }
}
