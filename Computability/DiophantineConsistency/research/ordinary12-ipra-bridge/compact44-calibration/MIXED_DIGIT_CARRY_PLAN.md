# Uncompiled compact44 mixed-digit carry and clean-column interfaces

This is a proposed model-level proof interface, **not compiled Lean, a
carry/reset theorem, a machine simulation, or an iPRA derivation**. The
existing API references are source-declared interfaces in the audited window
provider; exact imports, definability obligations and coherent replay must
still be checked when implementing them. The 1063 dummy is not Boolean.

## A. Scaled remainder and bounded cyclic carry

For an arbitrary `IΣ₁` model V, model naturals `w,n,D,b,F`, an **external
finite** type `ι`, coefficients `a : ι → V`, and words `X : ι → V`, propose

```
mod_le_scaled_rep:
  (∀ i < k, dig w X i ≤ D) →
  X % Exp.exp (w*k) ≤ D * rep w k.
```

A proposed internal Σ₁ induction would use `ArithmeticWindowDigits.mod_exp_succ`, `rep_succ_add`, and the existing
`mod_le_rep` proof as a pattern. It must support nonstandard model k; a Lean
induction over standard ℕ would not suffice.

Define a new mixed-bound carry input with the exact fields of
`ArithmeticWindowCarry.CarryInput`, except replace `boolean` and `mass` by

```
∀ i, ∀ k<n, dig w (X i) k ≤ D
D * (∑ i, a i) + 1 ≤ (b+1) * (Exp.exp w − 1).
```

Retain all other fields: `n>0`, positive modulus, `X i < Exp.exp(w*n)`,
`F < Exp.exp(w*n)−1`, and the exact weighted-sum congruence. Rework the
existing `sum_mod_le`, `key_bound`, `excess_le`, and `carry_le` with the
scaled remainder estimate. The existing `raw`, `excess`, `prefixValue`,
`carry`, `prefix_succ`, `prefix_length`, `carry_last`, `incoming`,
`carry_column` and `end_around_carry` give the intended definitions and
proof pattern, but their current bundled input assumes Boolean digits; do not
invoke that bundled theorem unchanged. The desired result is the same cyclic
column equation and `carry k ≤ b` for `k<n`, now from the mixed digit bound.
It does not assert all carries vanish.

For the exact compact tuple, all ordinary supported digits are eventually
≤1, outside-support and selector 1 are zero, and the 1063 dummy is ≤3;
these must first follow from actual model MC-digit identities and the mask
`NoCarry` relation. The old 4M+8 bound cannot simply be tripled: the finite
recipe gives 4M+8 < ρ but 12M+8 > ρ. Although 3M+1 < ρ−1 numerically, no
claim is made that the actual weighted mass meets the corresponding premise
or that this settles the later reset.

## B. Local predecessor reset

A small separate arithmetic lemma should take `ρ>0`, a model incoming carry
`u≤b`, and a raw predecessor value `r` satisfying `r+b<ρ`, and conclude

```
(r+u) / ρ = 0.
```

Its proof should use `add_le_add`, strict transitivity, and
`div_eq_zero_of_lt`. The cyclic carry-column equation then makes that
predecessor's outgoing carry zero. It is essential to establish the raw
inequality from the actual current, spatial, and temporal contributions and
their model bounds; no global zero-carry assertion is assumed.

## C. Selecting a clean target and a bounded predecessor

Let `L=8807` and E be the **exact external 986-position support** of 943
selectors, 41 copy/anchor slots and dummy positions 1063,1064. For standard
`t` define `D_t={(t-e) mod L : e∈E}`. The separately reconstructed finite
recipe check reports

```
D_4393 ∩ D_5495 = ∅,
D_4392 ∩ D_5494 = ∅,
D_4392 ∩ D_5495 = ∅,
D_4393 ∩ D_5494 = {2198}.
```

The last hit corresponds to source offsets 2195 and 3296, both ordinary
Boolean anchor slots, not the 0–3 dummy at 1063. These are currently external
finite checks; bind the exact E and all four intersections into Lean or a
separately reviewed finite certificate before applying them.

The proposed all-model selection lemma should quantify over a model word
length `n=L*N`, `N>0`, an actual cell base `c` with `c+L≤n`, an internal
cyclic shift, and a decoded mixed-width source word. Define both target and
predecessor temporal source indices with the repository's actual `cyc`
operation. **Explicitly prove** that their model remainders modulo L equal the
standard offset computations above, including wraparound; do not replace a
model index by a standard residue without this bridge. A fractional-bit
rotation may combine adjacent radix digits; a single-residue finite set check
is not by itself a theorem about the resulting temporal digit or spill. Prove
that transport separately. Assume the support hypotheses (outside E digits vanish), ordinary digits ≤1, dummy digit ≤3,
and the exact finite-set identities. Conclude that at least one target
`t∈{4393,5495}` has temporal digit 0 and its predecessor temporal digit ≤1.
The pairwise-disjoint target sets give a clean target; the predecessor sets
and exceptional anchor case rule out selecting a target whose predecessor
has a dirty 1063 dummy. This argument remains uncompiled.

For the selected target, a separate exact-stencil theorem must establish the
raw bound required in B and identify the local current contribution with
`∑ cᵢxᵢ+2¹⁰W`. The **full spatial exponent** is `8807+42`; 42 is only its
residue modulo L. The exact original coefficient K, all model casts and
shifted high-mask conventions remain premises until independently bound.
`ArithmeticWindowBits.high_mask_digits` can then supply the local output
`NoCarry` relation only after its own high-mask and non-origin hypotheses are
proved. A clean temporal target and clean predecessor are needed before
identifying that output with the local sum.

The distinction is necessary: for `S=2⁵¹−2¹⁰`, adding temporal `2¹⁰`
produces `2⁵¹`, disjoint from `μ=2⁵¹−2`, although S itself intersects μ.
This is a standard-integer arithmetic example, not a claimed graph zero.
