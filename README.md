# vtree - A Tree Library for Futhark [![CI](https://github.com/diku-dk/vtree/workflows/CI/badge.svg)](https://github.com/diku-dk/vtree/actions) [![Documentation](https://futhark-lang.org/pkgs/github.com/diku-dk/vtree/status.svg)](https://futhark-lang.org/pkgs/github.com/diku-dk/vtree/latest/)

Data-parallel implementation of trees based on Euler-tours (Tarjan and Vishkin)
and Blelloch's insights (see "Guy Blelloch. [Vector Models for Data-Parallel Computing](https://www.cs.cmu.edu/~guyb/papers/Ble90.pdf), MIT Press, 1990".

## Interface

See [vtree.fut](lib/github.com/diku-dk/vtree/vtree.fut).

## Installation

```
$ futhark pkg add github.com/diku-dk/vtree
$ futhark pkg sync
```

## Usage example

See [Vector Models for Data-Parallel Computing](https://www.cs.cmu.edu/~guyb/papers/Ble90.pdf), pages 84-89.

```
$ futhark repl
> import "lib/github.com/diku-dk/vtree/vtree"
> module T = vtree
> def lp : [6]i64 = [0,1,2,4,6,9]
> def rp : [6]i64 = [11,8,3,5,7,10]
> def data : [6]f64 = [1.1, 2.0, 3.0, 6.0, 0.5, 1.2]
> def t : T.t f64 [6] = T.lprp {lp,rp,data}
> T.irootfix (f64.+) f64.neg 0 t
[1.1, 3.1, 6.1, 9.1, 3.5999999999999996, 2.3]
> T.ileaffix (f64.+) f64.neg 0 t
[13.799999999999999, 11.5, 2.9999999999999996, 6.0, 0.5, 1.1999999999999993]
```
