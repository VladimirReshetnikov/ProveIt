# Can the openai/math port give Theorems 18.2 and 18.7? A constants survey

Survey of 2026-10-08. It is read-only: nothing in `lib/openai-math` was
changed. Upstream is openai/math at `adc7f1241`, backported in this
repository to Lean 4.32.0.

## The question

The port proves `QuantitativeDensityTheorem` (`OAI/Combinatorics/Progressions/Model.lean`):

    ∃ C c η > 0, ∀ N ≥ 3, r_k(N) ≤ C·N·exp(−c (log log N)^(1+η)).

- **Theorem 1.3** needs only `∃ N₀`, so it follows as stated. The peer owns
  that bridge.
- **Theorem 18.2** needs a fixed threshold: N ≥ 2^2^(δ^(−M)) with
  M = 2^(2^(k+9)) forces a k-AP at density δ.
- **Corollary 18.7** follows from the δ = 1/2 case of 18.2
  (`corollary_18_7_at_of_half_density`).

An existential C can never be compared with a fixed threshold, so 18.2 and
18.7 need **explicit constants of bounded size**. For δ ≤ 1/2, past 18.2's
threshold log log N ≥ δ^(−M) ≥ 2^M. So it suffices that the bound holds once
log log N exceeds some explicit C₀ ≤ 2^(M−1), which is triple exponential
in k. The survey asks whether the port's constants can be made explicit,
and how large they are.

Labels: **V** means verified by reading the code; **I** means inferred from
definitions or rough size estimates.

## Proof architecture (V)

`Results/Conclusions.lean` → `quantitative_density_bound_of_uniform_relative_lifting`
(`Estimates/UniformRelativePatchSource.lean:418`). The proof has three
layers.

1. **Stage induction** over `stage = 0..s` (s = k−2). It carries a natural
   power E with `RelativePatchPowerInductionRule s n₀ stage τ E`, where cutoff
   and cost are both (p+2)^E. The base is `exists_relativePatch_scalarBase_fin_power`;
   the step is `exists_preparedRelativePatchPowerPassage` followed by
   `exists_relativePatchFinPositivePower_of_prepared`.
2. **Density descent.** The patch source `SubquadraticPatchSource` and
   `subquadratic_patch_descent` maintain the invariant
   p^β + C₀ ≤ log log N, where p = densityParameter α = max(2, log(2/α)).
   Each step lowers p by at least 1. The descent needs p ≥ T = max(pmin, p₀).
3. **Terminal.** Once p ≤ T (density ≥ e^(−T)), `no_interval_invariant_of_descent`
   calls `fixed_density_terminal`, then `fixed_density_hasAP`
   (`Probability/RelativeSourceDensityParameter.lean:283`), then
   `FixedDensity.szemeredi` (`FixedDensity/Conclusions.lean:1293`).

A heuristic scan of the constant spine (not committed) finds about 340
theorems whose conclusions begin with a scalar existential. Nearly all
its leaves are "budget" lemmas of the form ∃ C, cost(p) ≤ (p+2)^C. That
count is a heuristic, not an exact closure.

## Finding 1: every witness is explicit-able, but the code's witnesses are towers

- Every power E comes from `exists_natPolynomial_fixed_power_budget P`
  applied to an explicit composite polynomial in ℕ[X] (V).
- The helper `exists_natPolynomial_eval_budget`
  (`Polynomial/PolynomialDensityBudget.lean:14`) picks the witness
  `P.eval 1 + natDegree + 2`, i.e. the coefficient **sum**. The fixed-power
  version then squares it (V).
- Any polynomial containing (X+2)^C therefore gets a witness of at least
  9^C, so each call exponentiates (V). The helpers have 1013 call sites in
  528 files.

**Stage recurrence.** A sharp witness would be degree + ⌈log₂ P(1)⌉ + 2:
- the step is **linear**, E' ≤ a(s)·E + b(s), because no two E-dependent
  powers are ever multiplied (V);
- a(s) ≥ 2^((2s+3)²)·38^s, so E_s = 2^(poly s) (I).

With the literal witnesses, each stage exponentiates E. Separately,
`candidateNestedDegreeNetBound` recurses s times through `Classical.choose`
witnesses. The constants as produced are therefore **towers of height
about 2s to 4s** (V for the mechanism, I for the height).

**Stage-only degrees.** Under sharp witnesses they are at most
2^(O(s² log s)): the forward-seed composition depth and the BCH heights,
with `scalarNativeDimension s = (s+1)(s+3)` (V). No Ackermann-type
recursion occurs in the stage layer (I, broad sweep).

**Descent constants (V for the formulas, I for the sizes):**
- c = (1/2)^(1/β), so Θ(1);
- η = 1/β − 1 ≈ 1/(8 log₂(E+1));
- τ = xi/(4(s+1)(1+xi)) and c_desc = log(κH₀)/4 are explicit;
- pmin and p₀ come from `eventually_atTop`. They solve explicit "log ≤ ε·power"
  inequalities. The binding one,
  log(4P) + 2s²B log(2+p) ≤ β c_desc p^(ν/2) with ν = log 2/(4 log(E+1)),
  gives T ≈ (E+1)^(O(log Λ + log log E)), which is quasi-polynomial in E.

## Finding 2: the dense case is qualitative, and it decides 18.7 (V)

- `fixed_density_hasAP` sets N₀ = ⌈1/c⌉ + 1, where c is the Varnavides
  count constant of `FixedDensity.szemeredi` at density e^(−T)/4.
- That theorem is the port's **hypergraph-removal** proof: ordered removal,
  coarse-target regularity, and a schedule ceiling taken by
  `Classical.choice` of `bounded_nonempty` (`FixedDensity/Conclusions.lean:1080`).
- Its constants are tower- or Ackermann-type (I). So C₀ ≈ log log N₀ is far
  beyond 2^M.
- Corollary 18.7 is exactly the δ = 1/2 case. There p = 2 ≤ T, so the port
  runs **no** descent and goes straight to this terminal.

**As written, the port cannot give 18.2 or 18.7, even with every
existential made explicit.** A Gowers-type terminal would not rescue it
either. At density e^(−T), Gowers's bound gives log log N₀ = e^(T·M), and
C₀ ≤ 2^M fails by the factor T in the exponent.

## Finding 3: the terminal can probably be removed (proposal, interface-checked)

The descent needs p ≥ T only to keep its subquadratic invariant (Finding 1);
a density step itself works at any density.

- `scored_patch_density_step` (`Sampling/ScoredPatchDensityStep.lean:26`,
  V) is parameter-free. From a patch correlation exp(−U) with target G·α, it
  produces a subprogression with **new density > G·α**, at a loss of
  log(4P) + 2s²R in log log N. R and V are any bounds on log(rank+1) and
  log U. Its only density condition, 2 ≤ densityParameter α − δ, holds at
  every density with δ = 0.
- `positive_patch_score_target_lt_one` (V) shows that a positive correlation
  forces G·α < 1.
- The source step `APFreeInterval.patch_of_relative_absolute` (V) needs only
  exp(−p) ≤ α/2, which is **monotone in p**, and N ≥ exp((p+2)^E).

**Dense continuation.**
1. Freeze p = P* := T for every density α ≥ 2e^(−T).
2. Each step multiplies the density by G(T) = (κH₀)^(2^⌊levelCoefficient·log T⌋)/2 > 1,
   which `exists_selected_density_drop` bounds below.
3. Each step loses at most L(T) = log(4P) + 2s²R(T) in log log N.
4. Density cannot exceed 1, so there are at most about T/log G(T) steps.
   A k-AP-free set cannot survive them.

This would replace `FixedDensity.szemeredi` by C₀ ≈ (T/log G(T))·L(T) plus
cutoff terms, which is poly(T) (I). With E_s = 2^(poly s) and T
quasi-polynomial in E, C₀ = 2^(poly k). That is vastly below 2^M = 2^2^2^2^(k+9).
The same machinery would then cover the δ = 1/2 case, and with it 18.7.

**Caveat.** This is checked against lemma interfaces, not proved. The
source family also needs p ≥ n₀, which P* = T satisfies. The step-to-step
bookkeeping (cutoffs, the d₀ rank budget, the absolute rule at p = T) must
be redone without the subquadratic invariant.

## What a proof of 18.2 and 18.7 through the port would take

1. **Port compiles.** `Results.Conclusions` is not yet verified
   (manifest: "Backport in progress"). The peer owns this.
2. **Dense continuation lemma** (Finding 3). It is a new module using
   `scored_patch_density_step` and the source at frozen P*. Size: moderate.
3. **Explicit constants with bounds.** Every spine existential must be
   restated with an explicit witness or an explicit upper bound:
   - about 340 spine theorems;
   - the s-only `Classical.choose` chains (net exponent, observable,
     primitive, early/input exponents);
   - a sharp polynomial-budget helper that returns the degree, not the
     coefficient sum.
   This is the dominant cost: mechanical, but several hundred restatements
   in a tree that is still being ported.
4. **Size bookkeeping.** Bound C₀ by an explicit 2^(poly k), check
   C₀ ≤ 2^(M−1), and feed 18.2 and then 18.7.

Unaffected: 16.2, 16.11 and 18.1 are Gowers's internal statements. No
change of path reaches them (research notes, Parts D–J).
