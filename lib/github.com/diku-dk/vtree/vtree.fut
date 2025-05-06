import "../sorts/merge_sort"
import "../segmented/segmented"

-- vtrees - data-parallel implementation of trees based on Euler-tours (Tarjan
-- and Vishkin) and Blelloch's insights (see "Guy Blelloch. Vector Models for Data-Parallel
-- Computing, MIT Press, 1990" (https://www.cs.cmu.edu/~guyb/papers/Ble90.pdf)

module type vtree = {

  type t 'a [n]

  val mk_preorder 'a [n] : [n]{parent:i64,data:a} -> t a [n]            -- preorder node numbering
  val lprp        'a [n] : {lp:[n]i64,rp:[n]i64,data:[n]a} -> t a [n]   -- preorder node numbering

  val map      'a 'b [n] : (a -> b) -> t a [n] -> t b [n]
  val rootfix     'a [n] : (op:a->a->a) -> (inv:a->a) -> (ne:a)
                           -> t a [n] -> [n]a
  val irootfix    'a [n] : (op:a->a->a) -> (inv:a->a) -> (ne:a)
                           -> t a [n] -> [n]a

  val leaffix     'a [n] : (op:a->a->a) -> (inv:a->a) -> (ne:a)
                           -> t a [n] -> [n]a
  val ileaffix    'a [n] : (op:a->a->a) -> (inv:a->a) -> (ne:a)
                           -> t a [n] -> [n]a

  val depth       'a [n] : t a [n] -> [n]i64
}

-- [mk_preorder a] creates a vtree from the preorder specification `a` of a tree
-- where each node is specified with data and a parent pointer (index into the
-- preorder of the nodes in the tree).
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

module vtree : vtree = {

  -- A vtree is represented by its left-parenthesis array and its
  -- right-parenthesis array.
  type t 'a [n] = {lp:[n]i64,rp:[n]i64,data:[n]a}

  type t0 'a [n] = [n]{parent:i64,data:a}

  -- A tree consists of n nodes (vertices, named 0..n-1) and n-1 edges. An edge
  -- p->x is uniquely identified by x (the node pointed to). There is no edge 0.
  --
  -- For constructing a vtree, we first construct an Euler tour of the tree and then
  -- extract the lp and rp arrays.

  def mk_preorder 'a [n] (ns:t0 a [n]) : t a [n] =
    assert (n >= 1 && ns[0].parent == -1)
    (let vs = map2 (\i n -> (n.parent,i)) (iota n) ns
     let A = map (\(p,x) -> [(p,x),(x,p)]) vs[1:] |> flatten
     let A = map2 (\e (x,y) -> (e,x,y)) (iota ((n-1)*2)) A
     let leq (_,x1,y1) (_,x2,y2) = x1 < x2 || (x1 == x2 && y1 <= y2)
     let B = merge_sort leq A
     -- given location in A - where is it in B
     let C = scatter (replicate ((n-1)*2) 0) (map (.0) B) (iota ((n-1)*2))
     let twin e = if e % 2 == 0 then e+1 else e-1
     let flags = map (\i -> i == 0 || B[i].1 != B[i-1].1)
		     (iota ((n-1)*2))
     let first =
       let op a b = if leq a b then a else b
       let ne = (0,i64.highest,i64.highest)
       in segmented_reduce op ne flags B |> map (.0)
     let next i =
       if i >= (n-1)*2 - 1 || B[i].1 != B[i+1].1 then first[B[i].1]
       else B[i+1].0
     let succ e = next(C[twin e])
     let E0 = replicate ((n-1)*2) 0i64
     let e0 = B[0].0
     let (E,_) = loop (E,e)=(E0 with [0]=e0,e0) for i in 1..<(n-1)*2 do
		 let e = succ e
		 in (E with [i] = e,e)
     let M = map (\i -> let (_,x,y) = A[i]
			let d = ns[y].parent == x
			in (d,x,y)) E
     let f op =
       let dir = map (\(d,_,_) -> if op d then 1 else 0) M
       let (is,vs) = scan (+) 0 dir
		     |> map3 (\i d j -> if d > 0 then (j-1,i+1) else (-1,0))
			     (iota ((n-1)*2)) dir
		     |> unzip
       in scatter (replicate (n-1) 0) is vs
     let lp = [0] ++ f id
     let rp = f not ++ [2*n-1]
     in {lp,rp,data=map (.data) ns} :> t a [n])

  def lprp 'a [n] (x:t a [n]) : t a [n] = x

  def xscan 'a [n] (op:a->a->a) (ne:a) (v:[n]a) : [n]a =
    take n (scan op ne ([ne]++v))

  def rootfix 'a [n] (op:a->a->a) (inv:a->a) (ne:a) ({lp,rp,data}:t a [n]) : [n]a =
    let I = replicate (2*n) ne
    let L = scatter I lp data
    let R = scatter L rp (map inv data)
    let S = xscan op ne R
    in map (\i -> S[i]) lp

  def irootfix 'a [n] (op:a->a->a) (inv:a->a) (ne:a) (t:t a [n]) : [n]a =
    map2 op (rootfix op inv ne t) t.data

  def ileaffix 'a [n] (op:a->a->a) (inv:a->a) (ne:a) ({lp,rp,data}:t a [n]) : [n]a =
    let I = replicate (2*n) ne
    let L = scatter I lp data
    let S = xscan op ne L
    let Rv = map (\i -> S[i]) rp
    let Lv = map (\i -> inv(S[i])) lp
    in map2 op Rv Lv

  def leaffix 'a [n] (op:a->a->a) (inv:a->a) (ne:a) (t:t a [n]) : [n]a =
    map2 op (ileaffix op inv ne t) (map inv t.data)

  def map 'a 'b [n] (f:a->b) ({lp,rp,data}:t a [n]) : t b [n] =
    {lp,rp,data=map f data}

  def depth 'a [n] (t:t a [n]) : [n]i64 =
    let t' = map (\_ -> 1) t
    in rootfix (i64.+) i64.neg 0 t'

}
