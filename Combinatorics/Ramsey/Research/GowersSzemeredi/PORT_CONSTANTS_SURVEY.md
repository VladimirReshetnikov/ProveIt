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

## Finding 3: the dense case is intrinsic to the method (V; refutes the first proposal)

The first version of this survey proposed a "dense continuation": freeze the
parameter at p = T and keep incrementing the density. Lemma interfaces
seemed to allow it. Reading the proofs refutes it.

- **Lift step.** The lift from the n₀-dimensional absolute rule to a
  one-dimensional patch is `RelativePatchPowerInductionRule.of_mean_increment`
  (`Linear/RelativeRankZeroSource.lean:10`). It needs `2 * a ≤ mean` and
  `Λ ≤ 1`, and its target is `(1 − τ)^(s+1) · Λ = κ·Λ`.
- **Base rule.** The absolute rule at the base level
  (`exists_initial_relative_absolute_rule`, from the CRT window patch) has
  target Λ = (1 + xi)·a.
- **Amplified levels** j ≥ 1 have target H_j·a under
  `LowDensityThreshold H_j a`, i.e. H_j²·a ≤ 1
  (`Probability/LowDensityAmplification.lean:12`;
  `LowDensityRelativeAbsoluteRule`, `Estimates/RelativePatchAmplification.lean:549`).
- **The step.** `scored_patch_density_step` then turns a positive
  correlation with target G·α into new density > G·α, with G = κ·H/2
  (because a ≤ α/2).

**Consequence.**
- An increment needs G > 1, i.e. H > 2/κ.
- At the base level that means 1 + xi > 2/κ ≥ 2. The CRT window gives no
  such xi.
- At an amplified level, H_j²·a ≤ 1 with a = α/2 forces α ≤ 2/H_j² < κ²/2 < 1/2.
- So the method increments **only sets of density below about κ²/2 < 1/2**.
  Above that it has no step at all. Freezing p changes the terminal density
  from e^(−T) to a constant c₀ < 1/2; it cannot remove the terminal.

A proof of r_k(N) = o(N) by this method therefore needs, as a black box,
Szemerédi's theorem at one fixed density c₀ < 1/2. The port uses the
hypergraph-removal proof there. Corollary 18.7, at density exactly 1/2, is
entirely that black box.

## Bottom line for Theorems 18.2 and 18.7

Even with every constant made explicit, the port reduces both to a
**quantitative dense Szemerédi theorem**:
- **18.7:** sets of density 1/2 in [N] contain k-APs once
  N ≥ 2^2^2^2^2^(k+9).
- **18.2:** the same at density c₀, with log log N₀ ≤ 2^(M−1), plus the
  explicitized descent for smaller δ. This is the same tower scale as 18.7.

That dense statement is the core of Gowers's theorem. No other published
proof supplies explicit constants of this size:
- the hypergraph-removal and regularity proofs are tower or Ackermann-type;
- Shelah's van der Waerden bound is wowzer-type;
- the modern analytic proofs, the port included, leave the dense case to
  one of these.

So **the port cannot be the path to 18.2 or 18.7.** Their only available
route is Gowers's own density iteration, i.e. this project's Sections 16–18
lane. That lane is proved for k ≤ 5 (`corollary_18_7_le_five`) and blocked
for k ≥ 6 (research notes, Parts B, I and J).

Explicitizing the port is still worthwhile for its own sake. But it would
improve none of the catalogue statements: 1.3 needs only `∃ N₀`.

**The lesson** (recorded in project memory). An interface can look
monotone in a parameter while the proof pins the parameter to the data,
here through `exp(−p) = α/2` and the low-density threshold. Read the
step's proof before proposing a route through it.
