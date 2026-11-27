# Lean formalization roadmap (uncompiled; no claim of a verified formalization)

The vendored project is a standalone Lake package with its own toolchain. Build from `vendor/grh-lean/grh`, using the README's commands, then import `Main` in an auxiliary target. Do not import its sources into the ProveIt root build without reconciling Lean/mathlib versions.

## Finite core — no GRH

Use a prime `ell` with `Fact (Nat.Prime ell)`, `X := Fin r → ZMod ell`, and a second copy `V` for the dual under the dot product. Use `c : X → ℤ` with `∑ a, c a = 0` and `c ≠ 0`. Define `s := (∑ a, |c a|)/2` in rational or real arithmetic (evenness follows from balance), `d v t := ∑ a with dot v a = t, c a`, `E v := ∑ t, (d v t)^2`, and `D := Finset.univ.filter (fun v => E v ≠ 0)`.

Suggested declarations (mathematical specifications, not syntax-checked Lean):

1. `projection_energy_expand`: `E v = ∑ a, ∑ b, c a * c b * if dot v (a-b)=0 then 1 else 0`.
2. `nonzero_linear_form_fiber_card`: for `a ≠ b`, the number of `v` with `dot v (a-b)=0` is `ell^(r-1)`. Prove by choosing a nonzero coordinate and solving uniquely for the corresponding coordinate of `v`.
3. `projection_energy_total`: `∑ v, E v = (ell-1)*ell^(r-1) * ∑ a, (c a)^2`. Use (1), (2), the diagonal term, and balance. State with `r≥1` and integer casts.
4. `projection_energy_cap`: `0 ≤ E v ≤ 2*s^2`; prove via positive/negative parts and a square of a finite sum of nonnegative terms. Prove equality forces all positive mass and negative mass into two distinct bins.
5. `signed_integrality`: `∑ a, (c a)^2 ≥ ∑ a, |c a|` with equality iff each value is in `{-1,0,1}`.
6. `disagreement_bound`: `ell * k * D.card ≥ (ell-1)*ell^r`, with casts chosen carefully. Derive from (3)–(5), `s≤k`, `s>0`. Equality classification: take the span of differences inside each residual support, use annihilator dimension and cardinality, and show the supports fill their cosets.
7. `projective_quantization`: rescaling a nonzero `v` permutes histogram bins, so `ell-1` divides `D.card`. Nonemptiness follows from (3), avoiding Fourier inversion.
8. `pencil_bound`: each agreement lies in an annihilator hyperplane based on a fixed positive anchor. Count its union using rank-nullity for two independent equations. Equality forces the common codimension-two intersection; show a union of at most `ell` distinct hyperplanes contains no additional hyperplane. This proves the incidence characterization.
9. `two_line_threshold`: use complex finite Fourier inversion or prove the elementary projection inversion formula `c(a) = ell^(1-r) * ∑_{projective v} d v (dot v a)` over rationals (count incidences for each `b`, cancel via balance). With two projective directions, it gives additive separation on two coordinates. An integer matrix nonzero count supplies the exact threshold.
10. `split_construction`, `nonsplit_construction`: formalize the cyclic multiplicative group, the quadratic finite-field extension, the norm-one group, and its reflections. The second can be implemented directly via `ZMod ell` quadratic extension or via a finite field of cardinality `ell^2`.

## Analytic bridge

The `Main` export `LFunction_ne_zero_of_half_lt_re` has type `DirichletLNonvanishingRightOfHalf`; `LFunction_eq_zero_re` gives the critical-strip zeros statement. A smoothed explicit formula for primitive Dirichlet characters and a uniform zero-count estimate are needed to produce the article's prime Gram estimate. These bridges are not supplied as a completed Lean development in this archive. Do not add them as axioms and then claim the new arithmetic result is fully formalized.

Once available, formulate the finite Fourier-algebra transfer as a generic lemma for a probability-like positive weighted measure whose character expectations differ from uniform by at most `e`. For the energy minorant use the character expansion of a hyperplane indicator; its Fourier coefficient L1 norm is one. The triangle inequality then gives norm at most two. The weighted Hamming decoding proof is purely finite and requires only triangle inequality and the distance lower bound.
