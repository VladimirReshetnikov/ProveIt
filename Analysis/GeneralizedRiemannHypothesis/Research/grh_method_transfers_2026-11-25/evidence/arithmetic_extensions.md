# Arithmetic transfer audit

Snapshot: `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`, read from `/workspace/scratch/8ed95454a998/sources/grh-lean`. No Lean build was run. Main contribution drafted in `notes/ramification_budget.tex`.

## 1. New analysis contribution: exact ramification cost

**Theorem.** Let O be one finite coefficient DVR containing the values of an ℓ-power character ψ, with absolute ramification index e and v(ℓ)=1. Let Q be nonempty, Q disjoint its CM conjugate. Suppose all powers ψ^j (1≤j≤m) ramify at every place of Q and its conjugate and satisfy

    Σ_(w in Q∪Qbar) v(ψ^j(γ_w)−1) ≤ ε.

If ℓ^k≤m<ℓ^(k+1), then **ε e≥2|Q|ℓ^k**.

Proof: at j=ℓ^k, each tame-generator value ζ_w has exact order ℓ^h_w with h_w>k. v(ζ_w^(ℓ^k)−1)=ℓ^k v(ζ_w−1)≥ℓ^k/e. There are 2|Q| terms. The precise root-of-unity valuation v(ζ_(ℓ^h)−1)=1/φ(ℓ^h) follows by evaluating Φ_(ℓ^h) at one and observing that all primitive-root factors have equal valuation.

**Consequence as a certification limit.** The generic source bound normalized_length(S_ψ)≤β+ε cannot force S_ψ=0 by integer rounding even if β=0, since ε≥2/e. The exact discrete threshold is normalized_length<1/e. It is not a theorem that S_ψ is nonzero; the estimate itself is too coarse. Arbitrarily small ε is enabled by growing e. The counterexample O_h/(ζ_(ℓ^h)−1) is nonzero with normalized_length=1/φ(ℓ^h)→0.

**Precise missing bridge.** If a fixed finite module S over O_0 injects after coefficient extension into each favorable twisted module for arbitrarily small bounds, then normalized length is invariant under coefficient extension and S=0. Twisting is not coefficient extension, and no such injection is in the general theorem. This distinguishes a valid target from a false ε→0 inference.

Status: elementary theorem proved in this analysis; no claim of literature novelty or an open conjecture resolved. The five locally available prior analyses discuss local scalar obstruction and quantifier order, but searches did not locate this normalized-length/ramification budget observation.

Source anchors (all `grh/src/`):

- `Lib/General/NumberTheory/PadicLimitsValuation.lean:302–338`: `normLength` sends integer n to n times v(uniformizer), hence n/e.
- `New/Congruences/Selmer/Line.lean:130–144`: `TwistedLengthLe` bounds normalized lengths for all sufficiently large coefficient rings containing character values.
- `New/Congruences/Selmer/GeneralTheorem.lean:55–76`: `IsSmallTwist`, ℓ-power order, ramification, normalized length and local sum budgets.
- `New/Congruences/Selmer/GeneralTheorem.lean:392–396`: every power j=1,...,m satisfies `IsSmallTwist`.

Canonical source URL example: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/GeneralTheorem.lean

## 2. Positive extracted refinement: bounded support cardinality

For exactly the hypotheses of `exists_anticyclotomic_twist`, there exists B depending on fixed Selmer data, systems, initial coefficient ring and torsion level, **not on m or ε**, such that outputs can retain 1≤|Q|≤B. Hence characters with arbitrarily large order can simultaneously make the first m powers have finite Selmer lengths, with a bounded number of auxiliary ramification pairs.

Proof extraction, not newly compiled theorem:

1. `Line.lean:646–681` chooses s₀ before any m or ε, through the bounded descent in `Descent.lean`.
2. `TwistPolynomials` has `two_mul_card_le:2*#Q≤s₀` at `Line.lean:507–512`.
3. In `Line.lean:610–616`, Q=J, and `AuxiliaryPrimes.lean:429–437` includes `first_mem:P₀∈J`. So Q is nonempty.
4. `GeneralTheorem.lean:403–416` selects roots of unity and their orders without adding any primes.
5. Retaining nonemptiness requires strengthening the intermediate output type or bundling the proof alongside it; the existing endpoint's type does not expressly assert Q≠∅.
6. Since ψ^j is ramified for 1≤j≤m and Q≠∅, ord(ψ)>m. Increasing m produces infinitely many distinct twists.

Do not say fixed support, bounded conductor, fixed order, density, elliptic-curve rank conclusions or new Goldfeld result. Actual primes, conductors and orders can vary. This is information from an existing proof, not an independent novel open-problem solution.

## 3. Exact broad arithmetic interface

`SelmerDatum` is more restrictive than an arbitrary Galois representation:

- nonzero finite rank lattice and continuous action;
- prescribed local cocycle modules above ℓ, finite and containing coboundaries;
- matrices span the full matrix algebra over O;
- finite global congruence term and finite local terms;
- an inertial scalar ζ at a place away from ℓ with ζ²−1 a unit.

See `New/Congruences/Selmer/SelmerData.lean:117–162` for the definition. The general `exists_anticyclotomic_twist` theorem assumes an embedded CM number field; it does **not itself** impose a primitive 5040th root. Certain later arithmetic applications and comparison lemmas do impose that extra hypothesis. Distinguish the abstract theorem from the specialized construction.

At `New/Congruences/FitTwistsExist.lean:377–393`, one local twist simultaneously controls finite main-summand families and first m powers. At `517ff`, the assembled family is indexed by prime and complex-to-ℓ-adic isomorphism; no single twist works at every prime. These distinctions prevent direct BSD/Bloch–Kato/Vandiver conclusions.

The source `New/Congruences/FirstOrder/DenominatorBound.lean:42–48` explicitly says even-class orders, where Vandiver lives, do not enter the denominator estimate. Avoiding their contribution is not proving their vanishing.

## 4. Relation to known primary literature

- Kriz–Nordentoft, *Horizontal p-adic L-functions*, arXiv:2310.20678v3, revised November 16, 2025, https://arxiv.org/abs/2310.20678. Primary abstract explicitly includes simultaneous nonvanishing for arbitrarily many elliptic curves, p-power characters with conductor prime to p, applications to Diophantine stability, and quantitative fixed-order results with assumptions. Browser ref `turn770094434view1` (root must reopen before citation). Do not claim these broad ideas are newly discovered in this repository.
- Mazur–Rubin with appendix by Larsen, *Diophantine stability*, arXiv:1503.04642v3, July 3, 2017, https://arxiv.org/abs/1503.04642. Primary abstract gives positive-density primes ℓ and infinitely many cyclic ℓ^n extensions preserving points for simple abelian varieties/positive-genus curves under mild hypotheses. Ref `turn770094434view2`.
- Search surfaced Fischer–Nordentoft, *Diophantine rank stability and non-vanishing of L-functions*, arXiv:2606.31646 (2026), with a statement about arbitrary finite abelian groups whose prime factors are sufficiently large. Direct opening was disabled; do not rely on it without further source verification. Search ref `turn727544691academia27`.

## 5. Practical suggested next work

1. Export a standalone normalized-length simultaneous twisting theorem, together with the bounded-support property; compare exact hypotheses to known horizontal-twist theorems.
2. For an arithmetic target, prove a model comparison and local-condition theorem before assigning standard Selmer-group names to the formal modules.
3. If exact vanishing is sought, supply a fixed-module descent/injection, a stronger Fitting-ideal certificate, or an actual zero-length calculation. Merely shrinking ε in the existing estimates cannot provide the rounding argument.
4. Only then investigate specific Goldfeld-type or K-theory applications. The present analysis does not solve BSD, Bloch–Kato or Vandiver.
