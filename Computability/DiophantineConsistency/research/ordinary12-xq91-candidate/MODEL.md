# Model-zero comparison after X=q*w

`XQ91Model.zero_iff_transformed` proves that in every model of `IΣ₁`, for
arbitrary natural-number ports and arbitrary model-valued coordinates, the
91-graph is zero if and only if the 92-graph is zero after replacing its
`X` coordinate by `q*w`. The statement includes nonstandard model values and
has no positivity or fixed-port hypotheses. It uses the checked ring
identities and the model's difference-ring interpretation.

The bounded author check in `observations/model-attempt01/` exited 0 in 4.2
seconds with no warnings or `sorryAx`. Both named reports list `[propext,
Classical.choice, Quot.sound]` as Lean metatheory axioms. The source and runner
SHA-256 hashes are
`f7400f5eefa3ac75896fce11e42b7ffde8077c1588e7d85816d4a748d765af94` and
`5b13e5fc74c744faa67cf1628d485e3be7fc46becb99ca73788e6132457ee3e4`.
Two resource samples saw up to two Lean processes and a minimum of
18,256,628 KiB MemAvailable. The runner traversed and rechecked 76 selected
provider files; symlinked directories and complete historical source-to-object,
package-transitive and dynamic ancestry remain outside that inventory.
Between-sample overlaps and memory changes are not ruled out. This is one
author build, not an independent Lean replay.

The theorem is a **specified-valuation** equivalence. It does not by itself
show that an arbitrary positive 92-zero has an `X=q*w` quotient, prove the
fixed-port positive-existence equivalence, or derive an iPRA sentence. The
candidate JSON and its Lean expression remain connected by an external source
check.

With the recorded provider available, use a fresh attempt name to reproduce:

```sh
ATTEMPT=attempt02 python3 run-model.py
```
