-- | Data-parallel implementation of trees based on Euler-tours
--
-- (Tarjan and Vishkin) and Blelloch's insights (see "Guy Blelloch. Vector
-- Models for Data-Parallel Computing, MIT Press, 1990"
-- (https://www.cs.cmu.edu/~guyb/papers/Ble90.pdf).
--
-- ## Acknowledgements
--
-- Includes contributions from Aziz Rmadi, Elias Smedegaard, and Thomas Bonde
-- Hansen.

import "../segmented/segmented"
import "../sorts/radix_sort"

module type vtree = {
  type t 'a [n]
  type~ ts 'a [k]

  val mk_preorder 'a [n] : [n]{parent: i64, data: a} -> t a [n]

  val mk_parent 'a [n] : [n]i64 -> [n]a -> t a [n]

  val unmk 'a [n] : t a [n] -> {lp: [n]i64, rp: [n]i64, data: [n]a}

  val mk_ts 'a [n] [k] : (subtrees: t a [n]) -> (shapes: [k]i64) -> ts a [k]

  -- preorder node numbering
  val lprp 'a [n] : {lp: [n]i64, rp: [n]i64, data: [n]a} -> t a [n]

  -- preorder node numbering

  val map 'a 'b [n] : (a -> b) -> t a [n] -> t b [n]

  val rootfix 'a [n] :
    (op: a -> a -> a)
    -> (inv: a -> a)
    -> (ne: a)
    -> t a [n] -> [n]a

  val irootfix 'a [n] :
    (op: a -> a -> a)
    -> (inv: a -> a)
    -> (ne: a)
    -> t a [n] -> [n]a

  val leaffix 'a [n] :
    (op: a -> a -> a)
    -> (inv: a -> a)
    -> (ne: a)
    -> t a [n] -> [n]a

  val ileaffix 'a [n] :
    (op: a -> a -> a)
    -> (inv: a -> a)
    -> (ne: a)
    -> t a [n] -> [n]a

  val depth 'a [n] : t a [n] -> [n]i64

  val split 'a [n] :
    t a [n]
    -> [n]bool
    -> ?[k][m].( ts a [k]
               , t a [m]
               )

  val get_t 'a [k] : i64 -> ts a [k] -> t a []

  val delete 'a [n] : t a [n] -> [n]bool -> t a []

  val merge 'a [m] [k] :
    ts a [k]
    -> -- There are k subtrees, n vertices in total
    (parent_tree: t a [m])
    -> -- Parent has m vertices
    (parent_pointers: [m]i64) -> t a []
}

-- [mk_preorder a] creates a vtree from the preorder specification `a` of a tree
-- where each node is specified with data and a parent pointer (index into the
-- preorder of the nodes in the tree).
--
-- [mk_parent a] creates a vtree from the parent specification `a` of a tree
-- where each node is specified with data and a parent pointer. It does not have
-- to be a preorder.
--
-- [mk_ts subtrees shapes] creates a collection of trees by interpreting a
-- single tree as a collection of subtrees, each of which has a shape given by
-- `shapes`.
--
-- [unmk t] exposes the underlying representation of a vtree - this is intended
-- solely for debugging of the library itself.
--
-- [lprp a] creates a vtree from a preorder specification `a` of a tree where
-- the `lp` and `rp` arrays specify the indices of a left- and right-parenthesis
-- print of the tree.
--
-- [map f t] maps a function `f` over the nodes in the tree.
--
-- [rootfix f inv ne t] computes, for each node `n` in the tree with the path
-- `n0->n1->...->nm->n` from the root `n0` to `n`, the values `f n0 (f n1
-- (...nm...))` (i.e., excluding the data for node `n`).
--
-- [rootfixi f inv ne t] computes, for each node `n` in the tree with the path
-- `n0->n2->...->n` from the root `n0` to `n`, the values `f n0 (f n1
-- (...n...))` (i.e., including the data for node `n`).
--
-- [leaffix f inv ne t] computes, for each node `n` in the tree with descendants
-- `[n1,n2,...,nm]` the accumulated value `f n1 (f n2 (...nm...))` (i.e.,
-- excluding the data for node `n`).
--
-- [leaffixi f inv ne t] computes, for each node `n` in the tree with
-- descendants `[n1,n2,...,nm]` the accumulated value `f n (f n1 (f n2
-- (...nm...)))` (i.e., including the data for node `n`).
--
-- For all `Xfix` operations (i.e., rootfix, rootfixi, leaffix, leaffixi), `f`
-- is assumed to be associative, the value `ne` is supposed to be the neutral
-- element for `f`, and `inv` is assumed to be the inverse associated with `f`
-- such that if `c = f a b` then `a = f c (inv b)` and `b = f c (inv a)`. All
-- `Xfix` operations has Work O(`m`) and Depth O(1), assuming `f` has constant
-- work and depth complexities.
--
-- [depth t] returns, for each node `n`, the depth of the subtree rooted at `n`
-- in `t`.
--
-- [split t flags] splits the tree into subtrees rooted at each node marked as
-- true in the bool array. The subtrees must be disjoint, meaning no note marked
-- as a new root may have another new root as ancestor. Returns a collection of
-- hew trees as the type `ts`, as well as the residual tree.
--
-- [get_t i ts] extracts the `i`th subtree from a collection of trees.
--
-- [delete t flags] deletes those nodes marked as true.
--
-- [merge ts t ps] merges a collection of subtrees `ts`.

module vtree : vtree = {
  -- A vtree is represented by its left-parenthesis array and its
  -- right-parenthesis array.
  type t 'a [n] = {lp: [n]i64, rp: [n]i64, data: [n]a}

  type t0 'a [n] = [n]{parent: i64, data: a}

  type~ ts 'a [k] =
    ?[n].{ subtrees: t a [n]
         , subtrees_offsets: [k]i64
         }

  -- A tree consists of n nodes (vertices, named 0..n-1) and n-1 edges. An edge
  -- p->x is uniquely identified by x (the node pointed to). There is no edge 0.
  --
  -- For constructing a vtree, we first construct an Euler tour of the tree and then
  -- extract the lp and rp arrays.

  def wyllie_scan_step [n] 'a
                       (op: a -> a -> a)
                       (values: [n]a)
                       (parents: [n]i64) =
    let f i =
      if parents[i] == -1
      then (values[i], parents[i])
      else (values[i] `op` values[parents[i]], parents[parents[i]])
    in unzip (tabulate n f)

  def wyllie_scan [n] 'a
                  (op: a -> a -> a)
                  (values: [n]a)
                  (parents: [n]i64) =
    let (values, _) =
      loop (values, parents) for _i < 64 - i64.clz n do
        wyllie_scan_step op values parents
    in values

  def exscan f ne xs =
    map2 (\i x -> if i == 0 then ne else x)
         (indices xs)
         (rotate (-1) (scan f ne xs))

  def segmented_replicate [n] (reps: [n]i64) (vs: [n]i64) : []i64 =
    map (\i -> vs[i]) (replicated_iota reps)

  def size (h: i64) : i64 =
    (1 << h) - 1

  def mk_tree [n] 't (op: t -> t -> t) (ne: t) (arr: [n]t) =
    let temp = i64.num_bits - i64.clz n
    let h = i64.i32 <| if i64.popc n == 1 then temp else temp + 1
    let tree_size = size h
    let offset = size (h - 1)
    let offsets = iota n |> map (+ offset)
    let tree = scatter (replicate tree_size ne) offsets arr
    let arr = copy tree[offset:]
    let (tree, _, _) =
      loop (tree, arr, level) = (tree, arr, h - 2)
      while level >= 0 do
        let new_size = length arr / 2
        let new_arr =
          tabulate new_size (\i -> arr[2 * i] `op` arr[2 * i + 1])
        let offset = size level
        let offsets = iota new_size |> map (+ offset)
        let new_tree = scatter tree offsets new_arr
        in (new_tree, new_arr, level - 1)
    in tree

  def find_next [n] 't
                (op: t -> t -> bool)
                (tree: [n]t)
                (idx: i64) : i64 =
    let sibling i = i - i64.bool (i % 2 == 0) + i64.bool (i % 2 == 1)
    let parent i = (i - 1) / 2
    let is_right i = i % 2 == 0
    let h = i64.i32 <| i64.num_bits - i64.clz n
    let offset = size (h - 1)
    let start = offset + idx
    let v = tree[start]
    let ascent i = i != 0 && (is_right i || !(tree[sibling i] `op` v))
    let descent i = 2 * i + 2 - i64.bool (tree[2 * i + 1] `op` v)
    let index = iterate_while ascent parent start
    in if index != 0
       then iterate_while (< offset) descent (sibling index) - offset
       else -1

  def mk_preorder 'a [n] (ns: t0 a [n]) : t a [n] =
    let data = map (.data) ns
    let parents = map (.parent) ns
    -- Compute depths of each node in tree.
    let ds = wyllie_scan (+) (tabulate n (i64.bool <-< (!= 0))) parents
    -- Every node can be seen as edge on the euler tour in the
    -- downwards direction, if the depth changes then it meant that
    -- some subpath is taken up the tree.  These are the missing edges
    -- in the euler path. The upwards going edges and downwards going
    -- edges can be seen as parenthesis so these are the number of
    -- missing right parenthesis after an given left parenthesis.
    let missing =
      map3 (\i d d' -> if i != n - 1 && d >= d' then d - d' + 1 else 0)
           (indices ds)
           ds
           (rotate 1 ds)
    -- Adjust left parenthesis indices to account for the number of
    -- right parenthesis that are needed to be added.
    let lp = map2 (+) (indices ds) (exscan (+) 0 missing)
    -- Scatter the left parenthesis to their new position.
    let parens = scatter (replicate (2 * n) (-1)) lp (rep 1)
    -- Compute the depth of every parenthesis.
    let depths =
      parens
      |> scan (+) 0
      |> map2 (\p d -> d - i64.bool (p == 1)) parens
    -- Construct a prefix tree of minima.
    let min_tree = mk_tree i64.min i64.highest depths
    -- Find the next smaller or equal element.
    let rp = map (find_next (<=) min_tree) lp
    in {lp, rp, data}

  def mk_ts 'a [n] [k] (subtrees: t a [n]) (shapes: [k]i64) : ts a [k] =
    {subtrees, subtrees_offsets = exscan (+) 0 shapes}

  def lprp 'a [n] (x: t a [n]) : t a [n] = x

  def rootfix 'a [n] (op: a -> a -> a) (inv: a -> a) (ne: a) ({lp, rp, data}: t a [n]) : [n]a =
    let I = replicate (2 * n) ne
    let L = scatter I lp data
    let R = scatter L rp (map inv data)
    let S = exscan op ne R
    in map (\i -> S[i]) lp

  def irootfix 'a [n] (op: a -> a -> a) (inv: a -> a) (ne: a) (t: t a [n]) : [n]a =
    map2 op (rootfix op inv ne t) t.data

  def ileaffix 'a [n] (op: a -> a -> a) (inv: a -> a) (ne: a) ({lp, rp, data}: t a [n]) : [n]a =
    let I = replicate (2 * n) ne
    let L = scatter I lp data
    let S = exscan op ne L
    let Rv = map (\i -> S[i]) rp
    let Lv = map (\i -> inv (S[i])) lp
    in map2 op Rv Lv

  def leaffix 'a [n] (op: a -> a -> a) (inv: a -> a) (ne: a) (t: t a [n]) : [n]a =
    map2 op (ileaffix op inv ne t) (map inv t.data)

  def enumerate [n] (flags: [n]bool) : [n]i64 =
    let ints = map (\b -> if b then 1 else 0) flags
    let ps = scan (+) 0 ints
    in map (\(b, s) -> if b then s - 1 else -1)
           (zip flags ps)

  def pack [n] 'a (flags: [n]bool) (xs: [n]a) : []a =
    map (.1) (filter (.0) (zip flags xs))

  def delete 'a [n] (t: t a [n]) (keep: [n]bool) : t a [] =
    -- compute the size of the resulting tree after deletion
    let m = i64.sum (map (\b -> if b then 1 else 0) keep)
    -- permute the keep flags to right and left parenthesis
    let paren_flags =
      scatter (replicate (2 * n) false)
              (concat t.lp t.rp)
              (concat keep keep)
    -- enumerate the parentheses to keep and get the new, renumbered parentheses indices
    let paren_enum = enumerate paren_flags
    let (new_left, new_right) =
      unzip (map (\(k, l, r) -> if k then (paren_enum[l], paren_enum[r]) else (-1, -1))
                 (zip3 keep t.lp t.rp))
    -- Pack the final results to get rid of the deleted vertices
    let zipped_tree_info = zip3 new_left new_right t.data
    let packed_tree_info = pack keep zipped_tree_info :> [m](i64, i64, a)
    let (lp, rp, data) = unzip3 packed_tree_info
    in {lp, rp, data}

  def split 'a [n]
            (t: t a [n])
            (splits: [n]bool) : ( ts a []
                                , t a []
                                ) =
    -- Phase 1: Propagate subtree root lp to all descendants
    let root_idx =
      map2 (\is_root l -> if is_root then l else 0) splits t.lp
    let t_root = {lp = t.lp, rp = t.rp, data = root_idx}
    let dist = irootfix (i64.+) i64.neg 0 t_root
    -- Phase 2: Compute local indices and membership in subtrees
    let L_local = map2 (-) t.lp dist
    let R_local = map2 (-) t.rp dist
    let in_subtree = map (\d -> d != 0) dist
    let is_rem = map not in_subtree
    -- Phase 3: Extract subtrees
    let sub_zipped =
      filter (\(keep, _, _, _) -> keep)
             (zip4 in_subtree L_local R_local t.data)
    let subtrees =
      { lp = map (.1) sub_zipped
      , rp = map (.2) sub_zipped
      , data = map (.3) sub_zipped
      }
    -- Phase 4: Compute offsets from subtree sizes
    let subtrees_shape = map2 (\l r -> (r - l + 1) / 2) t.lp t.rp
    let result_shape = pack splits subtrees_shape
    -- Phase 5: Build remainder
    let remainder = delete t is_rem
    in ( {subtrees, subtrees_offsets = exscan (+) 0 result_shape}
       , remainder
       )

  def get_t 'a [k] (i: i64) (s: ts a [k]) : t a [] =
    let o = s.subtrees_offsets[i]
    let l =
      if i + 1 < k
      then s.subtrees_offsets[i + 1]
      else length s.subtrees.data
    in { lp = s.subtrees.lp[o:l]
       , rp = s.subtrees.rp[o:l]
       , data = s.subtrees.data[o:l]
       }

  def offsets_to_shapes [n] (total: i64) (xs: [n]i64) : [n]i64 =
    map3 (\me next i ->
            if i == n - 1
            then total - me
            else next - me)
         xs
         (rotate 1 xs)
         (iota n)

  def merge 'a [n] [m] [k]
            ({ subtrees = subtrees: t a [n]
             , subtrees_offsets = subtrees_offsets: [k]i64
             }
            )
            -- There are k subtrees, n vertices in total
            (parent_tree: t a [m])
            -- Parent has m vertices
            (parent_pointers: [m]i64) : t a [] =
    -- Phase 1: Compute indices of parent nodes in the result
    let subtrees_shape = offsets_to_shapes n subtrees_offsets
    let size_to_allocate_for_each_parent = map (\i -> if i < 0 then 0 else subtrees_shape[i]) parent_pointers
    let num_children_left_of_each_parent = exscan (+) 0 size_to_allocate_for_each_parent
    let distances_between_parents = map (+ 1) size_to_allocate_for_each_parent
    let parent_indices = exscan (+) 0 distances_between_parents
    -- Phase 2: Compute the new parentheses of the parent nodes in the result
    let double_children_left = map (2 *) num_children_left_of_each_parent
    let new_parents_lp = map2 (+) parent_tree.lp double_children_left
    let parent_tree_with_child_counts =
      lprp { data = size_to_allocate_for_each_parent
           , lp = parent_tree.lp
           , rp = parent_tree.rp
           }
    let num_children_under_each_parent = ileaffix (+) i64.neg 0i64 parent_tree_with_child_counts
    let double_children_under = map (2 *) num_children_under_each_parent
    let new_parents_rp = map3 (\a b c -> a + b + c) parent_tree.rp double_children_left double_children_under
    -- Phase 3: Compute indices of child nodes in the result
    let num_of_children = num_children_left_of_each_parent[m - 1] + size_to_allocate_for_each_parent[m - 1]
    let result_size = m + num_of_children
    let child_indices =
      let flag_basis = replicate result_size true
      let flag_array = scatter flag_basis parent_indices (replicate m false)
      in filter (\i -> flag_array[i]) (iota result_size) |> sized num_of_children
    -- Phase 4: Compute the indices in subtrees of the result
    let subtree_indices =
      let iota_flags = scatter (replicate num_of_children false) num_children_left_of_each_parent (replicate m true)
      let iotas = segmented_iota iota_flags
      let iota_subtrees = segmented_replicate size_to_allocate_for_each_parent parent_pointers |> sized num_of_children
      let subtree_offsets = exscan (+) 0 subtrees_shape
      let iota_offsets = map (\i -> subtree_offsets[i]) iota_subtrees
      in map2 (+) iotas iota_offsets
    -- Phase 5: Compute lp and rp arrays of the children to be inserted in the allocated space
    let chosen_children_lp = map (\i -> subtrees.lp[i]) subtree_indices
    let chosen_children_rp = map (\i -> subtrees.rp[i]) subtree_indices
    let children_offset_values = map (1 +) new_parents_lp
    let children_offsets = segmented_replicate size_to_allocate_for_each_parent children_offset_values |> sized num_of_children
    let new_children_lp = map2 (+) chosen_children_lp children_offsets
    let new_children_rp = map2 (+) chosen_children_rp children_offsets
    -- Phase 6: Combine parent values with children values in result
    let new_lp = scatter (replicate result_size 0i64) parent_indices new_parents_lp
    let new_lp = scatter new_lp child_indices new_children_lp
    let new_rp = scatter (replicate result_size 0i64) parent_indices new_parents_rp
    let new_rp = scatter new_rp child_indices new_children_rp
    let new_data = scatter (replicate result_size parent_tree.data[0]) parent_indices parent_tree.data
    let new_data = scatter new_data child_indices (map (\i -> subtrees.data[i]) subtree_indices)
    in { lp = new_lp
       , rp = new_rp
       , data = new_data
       }

  def mk_parent 'a [n] (parent: [n]i64) (data: [n]a) : t a [n] =
    if n == 1
    then {lp = replicate n 0i64, rp = replicate n 1i64, data}
    else let root_candidates: [n]i64 =
           map2 (\v p -> if p == v then v else i64.highest) (iota n) parent
         let root: i64 =
           reduce i64.min i64.highest root_candidates
         let children: []i64 =
           filter (\v -> v != root) (iota n)
         let p_of_child: []i64 =
           map (\v -> parent[v]) children
         let ones: []i64 =
           map (\_ -> 1i64) p_of_child
         let child_count: [n]i64 =
           reduce_by_index (replicate n 0i64)
                           (i64.+)
                           0i64
                           p_of_child
                           ones
         let segd: [n]i64 =
           tabulate n (\v -> child_count[v] + i64.bool (v != root))
         let starts: [n]i64 =
           exscan (i64.+) 0i64 segd
         let m: i64 =
           reduce (i64.+) 0i64 segd
         let parent_slot: [n]i64 =
           tabulate n (\v -> if v == root then -1i64 else starts[v])
         let edges: []{p: i64, u: i64} =
           map2 (\p u -> {p, u}) p_of_child children
         let sedges: []{p: i64, u: i64} =
           radix_sort_int_by_key (.p)
                                 64i32
                                 (\bit k -> i32.i64 ((k >> i64.i32 bit) & 1i64))
                                 edges
         let sp: []i64 = map (.p) sedges
         let su: []i64 = map (.u) sedges
         let is: []i64 = indices sp
         let flags: []i64 =
           map (\i ->
                  if i == 0i64
                  then 1i64
                  else i64.bool (sp[i] != sp[i - 1i64]))
               is
         let marks: []i64 =
           map2 (\i f -> if f == 1i64 then i else -1i64) is flags
         let group_start: []i64 =
           scan i64.max (-1i64) marks
         let rank_in_group: []i64 =
           map2 (i64.-) is group_start
         let pos_in_parent_sorted: []i64 =
           map2 (\p r -> starts[p] + i64.bool (p != root) + r) sp rank_in_group
         let pos_in_parent: [n]i64 =
           scatter (replicate n (-1i64)) su pos_in_parent_sorted
         let child_slots: []i64 =
           map (\u -> parent_slot[u]) children
         let parent_slots: []i64 =
           map (\u -> pos_in_parent[u]) children
         let cross0: [m]i64 = replicate m (-1i64)
         let cross1: [m]i64 = scatter cross0 child_slots parent_slots
         let cross: [m]i64 = scatter cross1 parent_slots child_slots
         let owner: [m]i64 =
           scan i64.max (-1i64) (scatter (replicate m (-1i64)) starts (iota n))
         let next_in_seg: [m]i64 =
           tabulate m (\i ->
                         let v = owner[i]
                         let s = starts[v]
                         let deg = segd[v]
                         in if i + 1i64 < s + deg then i + 1i64 else s)
         let succ: [m]i64 =
           map (\c -> next_in_seg[c]) cross
         let head: i64 =
           starts[root]
         let pred: [m]i64 =
           (scatter (replicate m (-1i64)) succ (iota m)) with [head] = (-1i64)
         let init_vals: [m]i64 =
           (replicate m 1i64) with [head] = 0i64
         let rank: [m]i64 =
           wyllie_scan (i64.+) init_vals pred
         let lp: [n]i64 =
           tabulate n (\v ->
                         if v == root
                         then 0i64
                         else 1i64 + rank[pos_in_parent[v]])
         let rp: [n]i64 =
           tabulate n (\v ->
                         if v == root
                         then 2i64 * n - 1i64
                         else 1i64 + rank[parent_slot[v]])
         in {lp, rp, data}

  def map 'a 'b [n] (f: a -> b) ({lp, rp, data}: t a [n]) : t b [n] =
    {lp, rp, data = map f data}

  def depth 'a [n] (t: t a [n]) : [n]i64 =
    let t' = map (\_ -> 1) t
    in rootfix (i64.+) i64.neg 0 t'

  def unmk 'a [n] (t: t a [n]) : {lp: [n]i64, rp: [n]i64, data: [n]a} =
    { lp = t.lp
    , rp = t.rp
    , data = t.data
    }
}
