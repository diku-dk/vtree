import "../lib/github.com/diku-dk/vtree/vtree"

module T = vtree

entry test_mk =
  let mkt 'a [n] (ps:[n]i64) (ds:[n]a) : [n]{parent:i64,data:a} =
    map2 (\p d -> {parent=p,data=d}) ps ds
  let ps : [6]i64 = [-1,2,0,0,0,2]
  let fs : [6]f64 = [1.1, 2.3, 3.0, 6.9, 0.5, 1.2]
  let p = mkt ps fs
  let t0 = T.mk_preorder p
  let rs0 = T.irootfix (f64.+) f64.neg 0 t0
  in rs0

entry test_lprp =
  let t : T.t i64 [6] = T.lprp {lp=[0,1,2,4,6,9],
				rp=[11,8,3,5,7,10],
				data=iota 6}
  let fs2 : [6]f64 = [1.1, 2.0, 3.0, 6.0, 0.5, 1.2]
  let d = T.depth t
  let t2 = T.map (\i -> fs2[i]) t
  let rs = T.irootfix (f64.+) f64.neg 0 t2
  let ls = T.leaffix (f64.+) f64.neg 0 t2
  in all (\b->b) (map2 (==) d [0,1,1,2,1,1])

--==
-- entry: test_lprp
-- input {} output { true }
