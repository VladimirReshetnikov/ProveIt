# Independent review of the 88 oriented main balance

On 2026-11-04 an independent reviewer inspected
[`Absorb88MainBalance.lean`](../../research/ordinary12-absorb88-main-balance-draft/Absorb88MainBalance.lean)
and the statements of its main-root extraction and evaluated-root positivity
dependencies. No sign, positivity, or hypothesis mismatch was found. This is
a source review; no fresh Lean replay was run.

The evaluated right-hand side of the graph's main factor is
`W²(1 + delta(a)c²)`, since the graph discriminant `a² + 4a + 3` equals
`delta(a) = (a + 1)(a + 3)`. For the same tuple, the inherited root theorem
supplies a model element `g` with `g² = 1 + delta(a)c²`. Vanishing of the
actual main residual therefore gives `Dstar² = (Wg)²` in the ordered
difference ring. The inherited negative-branch result supplies `Dstar > 0`;
`Wg ≥ 0` follows because both are images of model elements. Equality of
squares and these signs select `Dstar = Wg`, with no unproved choice of a
negative or positive square-root branch.

The corollary retains the positive actual 88 zero, positive `beta`, and
explicit negative-transport hypothesis required by the positivity theorem.
It proves the stated balance for a model element `g`; it does not prove the
signed rank window or congruence, construct an 89 witness, or establish an
iPRA endpoint. The author's check relies on temporary providers; their full
project, package, dynamic, and search-path ancestry is not independently
authenticated by this review.

Reviewed source SHA-256:
`8b96901410c94bce76043a0e6e183d14c36b0f617a1cb897fe2ff6fce6609806`.
