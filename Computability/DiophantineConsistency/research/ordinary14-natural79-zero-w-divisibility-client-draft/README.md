# Natural-79 zero-w divisibility contradiction: source proposal

`Natural79ZeroWDivisibility.lean` proposes the next model-level step after the
[zero-w signed root cut](../ordinary14-natural79-zero-w-root-cut-draft/README.md).
All these sources, their imported graph/unit/quotient drafts, and the client
below are **unelaborated**. This packet does not establish a Lean theorem,
an iPRA derivation, provider/axiom closure or any physical-byte/PDF binding.

The root-cut draft's conditional conclusion for a 79 zero at `w=0` is

```
(4*ι(Y)+3) ∣ 3*ι(q)*ι(q)   in DiffRing V,
```

where `q=1+J*beta` and `Y=q³*(n_s+1)`. The proposed
`natural_dvd_three_square` client first rewrites these expressions as embedded
natural-model values and invokes the existing source declaration
`TenPositive80NaturalProjection.natural_dvd_of_signed`. That interface states
that divisibility in the difference ring between embedded natural-model
values reflects to divisibility inside the natural model. It does not appeal to
standard-natural prime factorization. The `simp`/cast rewrites, imports and
provider coherence have not been checked in Lean.

The proposed `no_divisor_in_window` is a separate fact-level statement: for
model values `Q,Y` with `Q>=2` and `Y>=Q³`, it assumes `(4Y+3) ∣ 3Q²` and
concludes false. The intended order argument is

```
0 < 3Q² < 4Y+3,
```

contradicting the natural-model positive-divisor bound `Arithmetic.le_of_dvd`.
The README's checker verifies the exact polynomial rearrangement

```
4Y+3 − 3Q² = 4(Y−Q³) + 4Q²(Q−1) + Q² + 3
```

as a formal integer-polynomial identity; under the stated order hypotheses its
right-hand side is positive. The actual Lean source uses monotonicity and
`nlinarith`; neither tactic behavior nor the model theorem has been verified.

The final proposed `w_pos_of_zero` assumes:

* an arbitrary signed port tuple `p` and a natural-model beta represented by
  `(p 0 : DiffRing V)=ι beta`, with `beta>0`;
* a natural-model K represented by `(p 1 : DiffRing V)=ι K`, so its embedding
  is nonnegative; no **strict** K0 assumption is needed for this local step;
* a literal 79 `InternalZero` in the same `IΣ₁` model.

It assumes no positivity of w, gamma or the root, and no representation or
bounds for MC or MF. Under a temporary `w=0` assumption it proposes using the
separate [zero-w J-positivity draft](../ordinary14-natural79-zero-w-jpos-draft/README.md),
the root-cut signed divisibility client, natural reflection, `q>=2` and
`Y>=q³`, obtaining a contradiction. It then proposes `w>0`. The unelaborated
[79-to-80 witness transfer](../ordinary14-natural79-wshift-model-draft/README.md)
accepts precisely a positive-w assertion for each 79 zero, but this packet
does not compose an endpoint. The selected symbolic-port representations and
the parent's stronger rank and endpoint conditions remain separate obligations.

The read-only checker pins the client and the cited source interfaces; checks
the explicit theorem assumptions and call directions; verifies the exact
size rearrangement using sparse-polynomial arithmetic; and runs finite
natural size and signed-divisibility controls. It does not validate Lean
syntax, tactic behavior, model order, casts, providers or any theorem. The
three `#print axioms` commands in the source have not been executed.

An [independent source and mathematical review](../../reviews/ordinary14-natural79-zero-w-divisibility-client-independent/README.md)
checks the reflection, size inequalities and explicit assumptions without
elaborating the proposed model theorem.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-zero-w-divisibility-client-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-zero-w-divisibility-client-draft/result.json
```
