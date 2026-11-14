# Bundled and separate diagonal formulas

`PA194BundledDiagonal.lean` constructs finite derivation trees in the PA194
separate-diagonal numerical calculus for the following transformations. If
`Γ(c)` is the separate diagonal formula and `X` is the old gate's `V→Q`, then
`Γ(c)` together with `¬X` derives `¬(Γ(c)→X)`, and a derivation of the latter
formula yields derivations of both `Γ(c)` and `¬X`. In particular, a valid
separate diagonal head and guarded old-gate head derive the corresponding
bundled-diagonal formula. The proofs build on a checked deduction theorem and
classical double-negation elimination for the actual restricted implicational
basis. The three printed axiom lists are `[propext, Quot.sound]`.

The bundled formula here is specifically `¬(Γ(c)→(V→Q))`. It is distinct
from the existing PA196 equality-vacuity `Code.bundle`; the PA-refutation
translation still needs its equality/rewrite calibration. These are standard
Lean derivation transformations, not an internal PRA/iPRA theorem or a proof
of equivalence to Con(PA).

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-bundled-diagonal/check.sh
```

The script rebuilds the source-calculus compiler prerequisites in private
tmpfs and checks the transformations. The same full prerequisite build and transformations passed as part of the
standalone `../pa194-reverse-rewrite/check.sh` run; the Lean modules also
passed an independent replay from retained clean prerequisites.
