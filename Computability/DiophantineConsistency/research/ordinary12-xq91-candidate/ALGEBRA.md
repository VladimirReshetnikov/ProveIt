# Lean ring comparison for the 91-operation graph

`XQ91.lean` defines the complete 91-graph in expression syntax. For arbitrary
integer ports and valuations in any commutative ring, it proves `first_eval`,
`main_eval` and `ordinary_eval`: each residual equals the corresponding
92-graph residual after replacing `X` by `q*w`. Small generic `factor_bt` and
`factor_main` ring identities avoid expanding the entire expression. No
positivity, standard-model or fixed-port assumption is used in these ring
identities.

The bounded author check `observations/algebra-attempt01/` exited 0 in 4.2
seconds with no warnings or `sorryAx`. The first comparison reports Lean
metatheory axioms `[propext, Quot.sound]`; the other two report `[propext]`.
The source SHA-256 is
`616084961b539e3c8d8a6e01b7e1a576deeef67d9cfb6f779f0c7a8edb846617`,
and the runner SHA-256 is
`35d328a1bfa28cf733ea708c84456af38ee51d4679f38af19dbd6fee031f0d46`.
Two resource samples saw up to two Lean processes and at least 18,257,092 KiB
MemAvailable. The runner traversed and rechecked 75 selected provider files;
it does not inventory all symlinked directories, historical source-to-object,
package-transitive or dynamic ancestry. It is a single-author check, and its
local setting suppresses unused-`simp`-argument lints.

The narrow external `check_lean_graph.py` verifies the Lean graph's coordinate
and port indices, 91 rows and four projections against `candidate.json`, with
three rejected mutations. It does not make a Lean theorem about files. The
positive-witness existence bridge and fixed-port machine-halt theorem are
separate obligations; these three ring identities do not establish them.

With the recorded provider available, reproduce with fresh attempt names:

```sh
ATTEMPT=attempt02 python3 run.py
python3 -I -S -B check_lean_graph.py
```
