-- | ignore

import "vtree"

module T = vtree

--==
-- entry: test_lprp
-- input {} output { true }

entry test_lprp =
  let t: T.t i64 [6] =
    T.lprp { lp = [0, 1, 2, 4, 6, 9]
           , rp = [11, 8, 3, 5, 7, 10]
           , data = iota 6
           }
  let fs2: [6]f64 = [1.1, 2.0, 3.0, 6.0, 0.5, 1.2]
  let d = T.depth t
  let t2 = T.map (\i -> fs2[i]) t
  let rs = T.irootfix (f64.+) f64.neg 0 t2
  let ls = T.ileaffix (f64.+) f64.neg 0 t2
  in all (\b -> b) (map2 (==) d [0, 1, 1, 2, 1, 1])
     && all (\b -> b) (map2 (==) rs [1.1, 3.1, 6.1, 9.1, 3.5999999999999996, 2.3])
     && all (\b -> b) (map2 (==) ls [13.799999999999999, 11.5, 2.9999999999999996, 6.0, 0.5, 1.1999999999999993])

entry test_split =
  let t: T.t i64 [6] =
    T.lprp { lp = [0, 1, 2, 4, 6, 9]
           , rp = [11, 8, 3, 5, 7, 10]
           , data = iota 6
           }
  let splits = [false, true, false, false, false, false]
  let [k] (subtree_res: T.ts i64 [k], remainder) = T.split t splits
  -- Check subtrees
  let subtrees_ok =
    k == 1
    && let subtree = T.unmk (T.get_t 0 subtree_res)
       in length subtree.data == 4
          && and (map2 (==) (sized (4) subtree.data) [1, 2, 3, 4])
          && and (map2 (==) (sized (4) subtree.lp) [0i64, 1, 3, 5])
          && and (map2 (==) (sized (4) subtree.rp) [7i64, 2, 4, 6])
  -- Check remainder
  let rem = T.unmk remainder
  let remainder_ok =
    length rem.data == 2
    && and (map2 (==) (sized (2) rem.data) [0, 5])
    && and (map2 (==) (sized (2) rem.lp) [0i64, 1])
    && and (map2 (==) (sized (2) rem.rp) [3i64, 2])
  in subtrees_ok && remainder_ok

entry test_split_at_leaf =
  let t: T.t i64 [6] =
    T.lprp { lp = [0, 1, 2, 4, 6, 9]
           , rp = [11, 8, 3, 5, 7, 10]
           , data = iota 6
           }
  -- Split at node 2 (a leaf under node 1)
  let splits = [false, false, true, false, false, false]
  let (subtree_res, remainder) = T.split t splits
  let subtrees = T.unmk (T.get_t 0 subtree_res)
  let rem = T.unmk remainder
  -- Subtree should just be node 2
  let subtrees_ok =
    length subtrees.data == 1
    && and (map2 (==) (sized (1) subtrees.data) [2])
  -- Remainder should be nodes 0, 1, 3, 4, 5
  let remainder_ok = length rem.data == 5
  in subtrees_ok && remainder_ok

entry test_split_multiple =
  let t: T.t i64 [6] =
    T.lprp { lp = [0, 1, 2, 4, 6, 9]
           , rp = [11, 8, 3, 5, 7, 10]
           , data = iota 6
           }
  -- Split at both node 1 and node 5 (siblings under root)
  let splits = [false, true, false, false, false, true]
  let (subtree_res, remainder) = T.split t splits
  let t0 = T.unmk (T.get_t 0 subtree_res)
  let t1 = T.unmk (T.get_t 1 subtree_res)
  -- Subtrees should contain nodes 1,2,3,4 and node 5
  let t0_ok =
    length t0.data == 4 && and (map2 (==) (sized 4 t0.data) [1, 2, 3, 4])
  let t1_ok =
    length t1.data == 1 && and (map2 (==) (sized 1 t1.data) [5])
  -- Remainder should only be root (node 0)
  let rem = T.unmk remainder
  let remainder_ok =
    length rem.data == 1
    && and (map2 (==) (sized (1) rem.data) [0])
  in t0_ok && t1_ok && remainder_ok

entry test_split_none =
  let t: T.t i64 [6] =
    T.lprp { lp = [0, 1, 2, 4, 6, 9]
           , rp = [11, 8, 3, 5, 7, 10]
           , data = iota 6
           }
  let splits = [false, false, false, false, false, false]
  let [k] (_: T.ts i64 [k], remainder) = T.split t splits
  let rem = T.unmk remainder
  -- No subtrees
  let subtrees_ok = k == 0
  -- All nodes in remainder
  let remainder_ok = length rem.data == 6
  in subtrees_ok && remainder_ok

entry test_delete_vertices =
  let t: T.t i64 [6] =
    T.lprp { lp = [0, 1, 2, 4, 6, 9]
           , rp = [11, 8, 3, 5, 7, 10]
           , data = iota 6
           }
  -- Keep only nodes 0, 1, 5
  let keep = [true, true, false, false, false, true]
  let result = T.delete t keep
  let res = T.unmk result
  let ok =
    length res.data == 3
    && and (map2 (==) (sized (3) res.data) [0, 1, 5])
  in ok

entry test_merge_tree =
  let parent_tree: T.t i64 [4] =
    T.lprp { lp = [0, 1, 3, 4]
           , rp = [7, 2, 6, 5]
           , data = [0, 1, 2, 3]
           }
  let subtrees: T.t i64 [5] =
    T.lprp { lp = [0, 1, 0, 1, 3]
           , rp = [3, 2, 5, 2, 4]
           , data = [4, 5, 6, 7, 8]
           }
  let subtrees_shape = [2i64, 3i64]
  let parent_pointers = [0i64, 1i64, 0i64, -1i64]
  let expected =
    { lp = [0, 1, 2, 5, 6, 7, 9, 13, 14, 15, 18]
    , rp = [21, 4, 3, 12, 11, 8, 10, 20, 17, 16, 19]
    , data = [0, 4, 5, 1, 6, 7, 8, 2, 4, 5, 3]
    }
  let actual = T.unmk (T.merge (T.mk_ts subtrees subtrees_shape) parent_tree parent_pointers)
  let ok =
    length actual.data == 11
    && and (map2 (==) (sized (11) actual.lp) expected.lp)
    && and (map2 (==) (sized (11) actual.rp) expected.rp)
    && and (map2 (==) (sized (11) actual.data) expected.data)
  in ok

entry test_merge_no_subtrees =
  let parent_tree: T.t i64 [4] =
    T.lprp { lp = [0, 1, 3, 4]
           , rp = [7, 2, 6, 5]
           , data = [0, 1, 2, 3]
           }
  let subtrees: T.t i64 [0] =
    T.lprp { lp = []
           , rp = []
           , data = []
           }
  let subtrees_shape = []
  let parent_pointers = [-1i64, -1i64, -1i64, -1i64]
  let expected = T.unmk parent_tree
  let actual = T.unmk (T.merge (T.mk_ts subtrees subtrees_shape) parent_tree parent_pointers)
  let ok =
    length actual.data == 4
    && and (map2 (==) (sized (4) actual.lp) expected.lp)
    && and (map2 (==) (sized (4) actual.rp) expected.rp)
    && and (map2 (==) (sized (4) actual.data) expected.data)
  in ok

-- Tests
-- ==
-- entry: test_split test_split_at_leaf test_split_multiple test_split_none test_delete_vertices test_merge_tree test_merge_no_subtrees
-- input {} output { true }

-- Tests for mk_parent():

def subtree_sizes [n] (t: T.t i64 [n]) : [n]i64 =
  let ones = T.map (\_ -> 1i64) t
  in T.ileaffix (i64.+) i64.neg 0 ones

def path_sums [n] (t: T.t i64 [n]) : [n]i64 =
  T.rootfix (i64.+) i64.neg 0 t

-- Helper: avoid deprecated array "==" by comparing elementwise.
def eq_i64s (xs: []i64) (ys: []i64) : bool =
  length xs == length ys && and (map2 (==) xs ys)

-- ==
-- entry: test_parent_singleton_simple
-- input  { [0i64]
--          [42i64] }
-- output { true }
entry test_parent_singleton_simple (parent: []i64) (data: []i64) : bool =
  let t = T.mk_parent parent data
  in eq_i64s (T.depth t) [0i64]
     && eq_i64s (subtree_sizes t) [1i64]
     && eq_i64s (path_sums t) [0i64]

-- ==
-- entry: test_parent_chain4_root0_simple
-- input  { [0i64, 0i64, 1i64, 2i64]
--          [5i64, 7i64, 11i64, 13i64] }
-- output { true }
entry test_parent_chain4_root0_simple (parent: []i64) (data: []i64) : bool =
  let t = T.mk_parent parent data
  in eq_i64s (T.depth t) [0i64, 1i64, 2i64, 3i64]
     && eq_i64s (subtree_sizes t) [4i64, 3i64, 2i64, 1i64]
     && -- path_sums excludes the node itself, includes ancestors:
        -- node1: data[0]=5
        -- node2: data[0]+data[1]=5+7=12
        -- node3: 5+7+11=23
        eq_i64s (path_sums t) [0i64, 5i64, 12i64, 23i64]

-- ==
-- entry: test_parent_star5_root3_simple
-- input  { [3i64, 3i64, 3i64, 3i64, 3i64]
--          [10i64, 20i64, 30i64, 40i64, 50i64] }
-- output { true }
entry test_parent_star5_root3_simple (parent: []i64) (data: []i64) : bool =
  let t = T.mk_parent parent data
  in eq_i64s (T.depth t) [1i64, 1i64, 1i64, 0i64, 1i64]
     && eq_i64s (subtree_sizes t) [1i64, 1i64, 1i64, 5i64, 1i64]
     && -- every leaf has only the root (3) as ancestor, root has 0:
        eq_i64s (path_sums t) [40i64, 40i64, 40i64, 0i64, 40i64]

-- ==
-- entry: blelloch_example_preorder_ids
-- input  { [0i64, 0i64, 1i64, 1i64, 1i64, 0i64]
--          [0i64, 1i64, 2i64, 3i64, 4i64, 5i64] }
-- output { true }
entry blelloch_example_preorder_ids (parent: []i64) (data: []i64) : bool =
  let t = T.mk_parent parent data
  let tree = T.unmk t
  in eq_i64s (T.depth t) [0i64, 1i64, 2i64, 2i64, 2i64, 1i64]
     && eq_i64s tree.lp [0i64, 1i64, 2i64, 4i64, 6i64, 9i64]
     && eq_i64s tree.rp [11i64, 8i64, 3i64, 5i64, 7i64, 10i64]
