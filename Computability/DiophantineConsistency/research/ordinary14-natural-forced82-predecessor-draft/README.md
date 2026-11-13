# Conditional predecessor arithmetic for the 82 graph

These are **unelaborated source-only drafts** for the missing predecessor
argument in the [82-to-86 model bridge](../ordinary14-natural-forced82-ring-bridge-draft/).
`Predecessors82.lean` states the arithmetic core conditionally: the factor
equations and their nonnegativity premises are explicit hypotheses.
`PartialShift82To74.lean` proposes the partially shifted transfer, and
`GraphPredecessors82.lean` proposes obtaining the factor equations from the
74 own-zero and residue drafts. None of these source statements has been
accepted by Lean. The checker examines the source and finite controls; it
does not elaborate Lean or prove the unbounded statements.

The proposed helper works over the difference ring of an `IΣ₁` model and
assumes `a >= 0`, a nonnegative first-factor product `ellPart`, and these
three equations, where `f`, `r`, and `y` are the three embedded model slots:

```
r² = ellPart + 1
1 + I² − (a² + 4a + 3)(f² − 1) = 1
y² − (a² + 4a + 3)(f² − 1)(y² − v²) = 1.
```

The first equation excludes `r=0`; the second excludes `f=0` because
`Delta=a²+4a+3 > 1`. For the third, setting `y=0` makes
`Delta * ((f²−1)*v²) = 1`. In the discrete ordered difference ring the
second factor must then be positive and at least one, contradicting
`Delta>1`. This uses `ModelDifferenceRing.one_le_of_pos`, rather than a
false appeal to the units of an arbitrary ordered ring. Nonzero model values
then have predecessors by the natural model's order and additive-predecessor
properties. The source proof is a proposal and may require tactic or API
repairs when it is eventually elaborated.

An [independent source and mathematical review](../../reviews/ordinary14-natural-forced82-predecessor-independent/README.md)
checks these conditions and the proposed graph-factor linkage without
elaborating Lean.

## Proposed graph binding and remaining obligations

For a natural 82 valuation `w`, define a natural 74 valuation `u` by keeping
slots 3, 8, and 11 unchanged and adding one at the other eleven slots. The
following steps have source proposals, but none has been elaborated or
established as a Lean theorem:

1. `PartialShift82To74.lean` composes the proposed 82-to-86 and 86-to-74 ring identities, and the
   difference-ring interpretation, to show that an 82 `InternalZero` at
   `w` gives a 74 `InternalZero` at `u`. This is a **partially shifted**
   valuation, not the same valuation.
2. `GraphPredecessors82.lean` proposes the following own-zero argument: if port 0 is the image of a positive natural-model `beta`, then slots 0,
   6, and 7 of `u` are positive. Instantiate the source-only
   `OwnZeroProduct74Draft.factor_units_of_zero` with its three residue
   premises from source-only `FactorResidues74Draft.restricted_residues`.
   It yields the first natural equation and the strong and auxiliary signed
   pair units. Convert the latter with source-only
   `OwnZeroUnits74Draft.unit_iff_one`. These drafts and their dependencies
   have not been elaborated.
3. That same source proposes binding the literal 74 `a`, `I`, and `vroot` graph fields to the helper's
   ring expressions; the graph explicitly exposes all three fields. Use
   `FirstFactor74Draft.X`, `Y`, `m`, and `k` to express
   `a = X*Y+Y` and `ellPart = (m*k)*(m*k+k)` as embedded natural values,
   hence nonnegative. Rewrite slots 3, 8, and 11 of `u` back to `w` and
   apply the conditional helper.
4. Still required: elaborate the source drafts and validate their use in the
   full conversion to the target iPRA derivation. An intermediate proof may
   use a stronger metatheoretic model framework, but the ambient `IΣ₁` model
   hypothesis and the current source-only drafts do not themselves establish
   an iPRA theorem. Separately prove the coefficient and PDF bindings.

The source check additionally compares the 82 and partially shifted 74
graphs and the first, strong, and auxiliary factor formulas in 300 finite
modular controls. These tests do not prove the graph binding or predecessor
assertion.

The local 82-to-74 unit-factor route needs the beta representation and
positivity described above. The full inherited 74-to-parent endpoint also
uses the separate `K0 >= 0` condition; that assumption is not needed merely
to state the three arithmetic equations above.

```
python3 -I -S -B research/ordinary14-natural-forced82-predecessor-draft/check_source.py > /tmp/natural82-predecessors.json
cmp /tmp/natural82-predecessors.json research/ordinary14-natural-forced82-predecessor-draft/result.json
```
