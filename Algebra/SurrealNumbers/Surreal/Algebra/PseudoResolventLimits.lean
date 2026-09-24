import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Order.Field
import Surreal.Algebra.MarkovEffective
import Surreal.HahnSeries.MarkovResidueShadow

/-!
# Endpoint limits of bounded pseudo-resolvents

This file removes the endpoint hypotheses from the abstract form of `markov:thm:effective` of
`docs/surreal/markov-generators-at-every-scale/article.tex`. It proves that every bounded real
family satisfying `markov:eq:same-scale` has endpoint limits satisfying
`markov:eq:endpoint-relations`. Hence the hypothesis package `MarkovEffective.IsCrossover` of
`Surreal/Algebra/MarkovEffective.lean` holds for every row-stochastic such family, and in
particular for the actual shadow `K_α(c) = res R_L(ct^α)` at every scale `α`.

**Rationality.** Let `K(c)`, `c > 0`, be real square matrices with
`(e - c)K(c)K(e) = eK(c) - cK(e)` for positive `c ≠ e` (`markov:eq:same-scale`, multiplied
out). Taking `e = 1` gives `K(c)(I - J + cJ) = cJ` with `J = K(1)` (`mul_affine`). With
`D(X) = det(I - J + XJ)` and `N_{ab}(X) = X(J adj(I - J + XJ))_{ab}` (`denom`, `numer`), it
follows that `K(c)_{ab} = N_{ab}(c)/D(c)` whenever `D(c) ≠ 0` (`apply_eq_div`,
`exists_rational`). Since `D(1) = 1`, the polynomial `D` is nonzero and has finitely many
roots. This representation is built from `K(1)` alone and is abstract: it is not the
leading-forest formula `markov:eq:shadow-formula` of `markov:thm:leading`, which is not proved
here. At the shadow it gives only rationality in `c` off a finite set
(`exists_rational_shadow`).

**Endpoint limits.** `exists_tendsto_atTop_div`: an eventually bounded real rational function
converges at `∞`, because its numerator cannot have larger degree than its denominator. Hence
a bounded family converges as `c → ∞` (`exists_tendsto_atTop`). The reflected family
`I - K(c⁻¹)` again satisfies `markov:eq:same-scale` (`sameScale_reflect`) and is bounded, which
gives the limit as `c → 0⁺` (`exists_tendsto_zero`). Only boundedness is used, not
stochasticity.

**Endpoint relations `markov:eq:endpoint-relations`.** Members of the family commute
(`mul_comm_of_sameScale`). Letting `e → ∞` in `(1 - c/e)K(c)K(e) = K(c) - (c/e)K(e)` gives
`K(c)P = K(c)` (`mul_fast`), hence `PK(c) = K(c)` (`fast_mul`). Letting `e → 0⁺` in
`markov:eq:same-scale` gives `K(c)Q = Q` (`mul_slow`), hence `QK(c) = Q` (`slow_mul`).

**Crossovers.** `isCrossover`, `exists_isCrossover`: every family of real row-stochastic
matrices satisfying `markov:eq:same-scale` has endpoint limits `P` (as `c → ∞`) and `Q` (as
`c → 0⁺`) and satisfies `IsCrossover K P Q`. `effective_of_sameScale` is
`MarkovEffective.effective_reconstruction_canonical` under these weaker hypotheses, with the
additional clause `rank G = p - rank Q`.

**The actual shadow.** `exists_isCrossover_shadow`, `effective_shadow`: take rates `q` with
nonnegative off-diagonal entries in `ℝ((t^Γ))`, for any ordered abelian group `Γ`, and let
`L` be their row Laplacian. At every scale `α`, critical or not, the literal shadow family
`c ↦ K_α(c)` has both endpoint limits (the existence part of `markov:eq:fast-endpoint` and
`markov:eq:slow-endpoint`), and all conclusions of `markov:thm:effective` hold for it. For the
canonical splitting `P = UV` and `H(c) = VK_α(c)U`, exactly one `G` has
`H(c) = c(cI + G)⁻¹` and `K_α(c) = Uc(cI + G)⁻¹V` for every `c > 0`, namely `G = H(1)⁻¹ - I`.
This `G` is a real row Laplacian with semisimple zero eigenvalue and zero-eigenvalue
projection `VQU`, `dim ker G = rank Q`, and `rank G = p - rank Q` with `p = rank P`, the
number of closed classes. `G` is indexed by the finset `closedClasses P` itself, so no
ordering of the classes is chosen; the source's remark that reordering the classes only
permutes `G` is `MarkovEffective.effectiveGenerator_compress_submatrix` together with
`MarkovEffective.IsSplitting.submatrix`, which hold for any family and apply to the shadow
unchanged. The inputs are `MarkovShadow.shadow_mem_rowStochastic` and
`MarkovShadow.shadow_same_scale`. The source's hypotheses that `α` is critical and that
`p > q` are not used.

**Pending.** Only the existence of the limits `P` and `Q` in `markov:eq:fast-endpoint` and
`markov:eq:slow-endpoint` is proved here. Their closed forms `B_{k₋}/b_{k₋}` and
`B_{k₊}/b_{k₊}`, their identification with the adjacent plateaux, the ranks `rank P = n - k₋`
and `rank Q = n - k₊`, and the strict drop `p > q` at a critical scale belong to
`markov:thm:flag`, which remains pending. Here `p` and `q` are simply the ranks of the two
limits. The leading-forest formula `markov:eq:shadow-formula` also remains pending.
-/

namespace Surreal.PseudoResolventLimits

open Matrix Filter Topology

noncomputable section

section RationalLimits

open Polynomial

/-- A real rational function that is eventually bounded as `x → ∞` converges. -/
theorem exists_tendsto_atTop_div {p q : ℝ[X]} (hq : q ≠ 0) {B : ℝ}
    (hb : ∀ᶠ x in atTop, |p.eval x / q.eval x| ≤ B) :
    ∃ l, Tendsto (fun x => p.eval x / q.eval x) atTop (𝓝 l) := by
  rcases lt_trichotomy p.degree q.degree with h | h | h
  · exact ⟨0, div_tendsto_atTop_zero_of_degree_lt p q h⟩
  · exact ⟨_, div_tendsto_atTop_leadingCoeff_div_of_degree_eq p q h⟩
  · exfalso
    obtain ⟨x, hx1, hx2⟩ :=
      (hb.and ((abs_div_tendsto_atTop_atTop_of_degree_gt p q h hq).eventually_gt_atTop B)).exists
    linarith

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The affine polynomial matrix `A(X) = I - J + XJ`. -/
def affine (J : Matrix n n ℝ) : Matrix n n ℝ[X] :=
  (1 - J).map C + (X : ℝ[X]) • J.map C

theorem eval_affine (J : Matrix n n ℝ) (c : ℝ) :
    (evalRingHom c).mapMatrix (affine J) = 1 - J + c • J := by
  ext a b
  simp [affine]
  ring

/-- The common denominator `D(X) = det(I - J + XJ)`. -/
def denom (J : Matrix n n ℝ) : ℝ[X] :=
  (affine J).det

/-- The numerators `N_{ab}(X) = X (J adj(I - J + XJ))_{ab}`. -/
def numer (J : Matrix n n ℝ) (a b : n) : ℝ[X] :=
  X * (J.map C * (affine J).adjugate) a b

theorem eval_denom (J : Matrix n n ℝ) (c : ℝ) : (denom J).eval c = (1 - J + c • J).det := by
  rw [denom, ← coe_evalRingHom, RingHom.map_det, eval_affine]

theorem eval_numer (J : Matrix n n ℝ) (c : ℝ) (a b : n) :
    (numer J a b).eval c = c * (J * (1 - J + c • J).adjugate) a b := by
  have hJ : (evalRingHom c).mapMatrix (J.map C) = J := by
    ext
    simp
  have h := congrFun (congrFun
    (map_mul (evalRingHom c).mapMatrix (J.map C) (affine J).adjugate) a) b
  rw [hJ, RingHom.map_adjugate, eval_affine] at h
  rw [numer, eval_mul, eval_X, ← h]
  rfl

theorem denom_ne_zero (J : Matrix n n ℝ) : denom J ≠ 0 := fun h => by
  have h1 := eval_denom J 1
  rw [h, eval_zero, one_smul, sub_add_cancel, det_one] at h1
  exact zero_ne_one h1

theorem finite_setOf_eval_denom_eq_zero (J : Matrix n n ℝ) :
    {c : ℝ | (denom J).eval c = 0}.Finite :=
  finite_setOf_isRoot (denom_ne_zero J)

end RationalLimits

section Family

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℝ → Matrix n n ℝ}

/-- `markov:eq:same-scale` at `e = 1`: `K(c)(I - K(1) + cK(1)) = cK(1)`. -/
theorem mul_affine
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e)
    {c : ℝ} (hc : 0 < c) : K c * (1 - K 1 + c • K 1) = c • K 1 := by
  rcases eq_or_ne c 1 with rfl | hc1
  · rw [one_smul, sub_add_cancel, Matrix.mul_one]
  · have h := hres c 1 hc one_pos hc1
    rw [one_smul] at h
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
    linear_combination (norm := module) -h

/-- `det(I - K(1) + cK(1)) K(c) = c K(1) adj(I - K(1) + cK(1))`. -/
theorem det_smul_eq
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e)
    {c : ℝ} (hc : 0 < c) :
    (1 - K 1 + c • K 1).det • K c = c • (K 1 * (1 - K 1 + c • K 1).adjugate) := by
  have h := congrArg (· * (1 - K 1 + c • K 1).adjugate) (mul_affine hres hc)
  simp only [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul] at h
  exact h

/-- Off the finitely many roots of `D`, each entry of `K(c)` is the rational function
`N_{ab}(c)/D(c)` built from `K(1)`. -/
theorem apply_eq_div
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e)
    {c : ℝ} (hc : 0 < c) (hD : (denom (K 1)).eval c ≠ 0) (a b : n) :
    K c a b = (numer (K 1) a b).eval c / (denom (K 1)).eval c := by
  rw [eq_div_iff hD, eval_numer, eval_denom]
  have h := congrFun (congrFun (det_smul_eq hres hc) a) b
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  rw [mul_comm]
  exact h

/-- A family satisfying `markov:eq:same-scale` agrees with a real rational matrix function
outside a finite set: `K(c)_{ab} = N_{ab}(c)/D(c)` for every `c > 0` with `D(c) ≠ 0`, where
`D ≠ 0` has finitely many roots. -/
theorem exists_rational
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e) :
    ∃ (N : n → n → Polynomial ℝ) (D : Polynomial ℝ), D ≠ 0 ∧ {c : ℝ | D.eval c = 0}.Finite ∧
      ∀ c : ℝ, 0 < c → D.eval c ≠ 0 → ∀ a b, K c a b = (N a b).eval c / D.eval c :=
  ⟨numer (K 1), denom (K 1), denom_ne_zero _, finite_setOf_eval_denom_eq_zero _,
    fun _ hc hD a b => apply_eq_div hres hc hD a b⟩

/-- A bounded family satisfying `markov:eq:same-scale` converges as `c → ∞`. -/
theorem exists_tendsto_atTop
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e)
    {B : ℝ} (hB : ∀ c : ℝ, 0 < c → ∀ a b, |K c a b| ≤ B) :
    ∃ P, Tendsto K atTop (𝓝 P) := by
  have hev : ∀ᶠ c in atTop, 0 < c ∧ (denom (K 1)).eval c ≠ 0 :=
    (eventually_gt_atTop 0).and (Polynomial.eventually_atTop_not_isRoot _ (denom_ne_zero (K 1)))
  have hent : ∀ a b, ∃ l, Tendsto (fun c => K c a b) atTop (𝓝 l) := by
    intro a b
    obtain ⟨l, hl⟩ := exists_tendsto_atTop_div (p := numer (K 1) a b) (denom_ne_zero (K 1))
      (B := B) (by
        filter_upwards [hev] with c hc
        rw [← apply_eq_div hres hc.1 hc.2]
        exact hB c hc.1 a b)
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [hev] with c hc
    exact (apply_eq_div hres hc.1 hc.2 a b).symm
  choose l hl using hent
  exact ⟨Matrix.of l, tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hl a b⟩

/-- The reflected family `M(c) = I - K(c⁻¹)` again satisfies `markov:eq:same-scale`. -/
theorem sameScale_reflect
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e) :
    ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e →
      (e - c) • ((1 - K c⁻¹) * (1 - K e⁻¹)) = e • (1 - K c⁻¹) - c • (1 - K e⁻¹) := by
  intro c e hc he hce
  have h := hres c⁻¹ e⁻¹ (inv_pos.2 hc) (inv_pos.2 he) (fun h => hce (inv_inj.1 h))
  have h1 : -(c * e) * e⁻¹ = -c := by rw [neg_mul, mul_assoc, mul_inv_cancel₀ he.ne', mul_one]
  have h2 : -(c * e) * c⁻¹ = -e := by
    rw [neg_mul, mul_comm c e, mul_assoc, mul_inv_cancel₀ hc.ne', mul_one]
  have hs : e - c = -(c * e) * (e⁻¹ - c⁻¹) := by
    rw [mul_sub, h1, h2]
    ring
  have h3 : (e - c) • (K c⁻¹ * K e⁻¹) = e • K e⁻¹ - c • K c⁻¹ := by
    rw [hs, mul_smul, h, smul_sub, smul_smul, smul_smul, h1, h2]
    module
  rw [sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  linear_combination (norm := module) h3

/-- A bounded family satisfying `markov:eq:same-scale` converges as `c → 0⁺`. -/
theorem exists_tendsto_zero
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e)
    {B : ℝ} (hB : ∀ c : ℝ, 0 < c → ∀ a b, |K c a b| ≤ B) :
    ∃ Q, Tendsto K (𝓝[>] 0) (𝓝 Q) := by
  obtain ⟨L, hL⟩ := exists_tendsto_atTop (K := fun c => 1 - K c⁻¹) (sameScale_reflect hres)
    (B := 1 + B) (by
      intro c hc a b
      have hK := hB c⁻¹ (inv_pos.2 hc) a b
      have h1 : |(1 : Matrix n n ℝ) a b| ≤ 1 := by
        rw [Matrix.one_apply]
        split_ifs <;> simp
      calc |(1 - K c⁻¹) a b| = |(1 : Matrix n n ℝ) a b - K c⁻¹ a b| := rfl
        _ ≤ |(1 : Matrix n n ℝ) a b| + |K c⁻¹ a b| := abs_sub _ _
        _ ≤ 1 + B := add_le_add h1 hK)
  refine ⟨1 - L, ?_⟩
  have h := (tendsto_const_nhds (x := (1 : Matrix n n ℝ))).sub (hL.comp tendsto_inv_nhdsGT_zero)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c _
  simp [inv_inv]

omit [DecidableEq n] in
/-- Two members of the family commute. -/
theorem mul_comm_of_sameScale
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e)
    {c e : ℝ} (hc : 0 < c) (he : 0 < e) : K c * K e = K e * K c := by
  rcases eq_or_ne c e with rfl | hce
  · rfl
  have h1 := hres c e hc he hce
  have h2 := hres e c he hc hce.symm
  apply smul_right_injective _ (sub_ne_zero.2 hce.symm)
  change (e - c) • (K c * K e) = (e - c) • (K e * K c)
  rw [h1]
  linear_combination (norm := module) h2

section Endpoints

variable
  (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e)
include hres

omit [DecidableEq n] in
/-- `markov:eq:endpoint-relations`: `K(c)P = K(c)` for the fast limit `P`. -/
theorem mul_fast {P : Matrix n n ℝ} (hP : Tendsto K atTop (𝓝 P)) {c : ℝ} (hc : 0 < c) :
    K c * P = K c := by
  have hce : Tendsto (fun e : ℝ => c * e⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul c
  have h1 : Tendsto (fun e => (1 - c * e⁻¹) • (K c * K e)) atTop
      (𝓝 ((1 - 0 : ℝ) • (K c * P))) :=
    (tendsto_const_nhds.sub hce).smul (hP.const_mul (K c))
  have h2 : Tendsto (fun e => K c - (c * e⁻¹) • K e) atTop (𝓝 (K c - (0 : ℝ) • P)) :=
    tendsto_const_nhds.sub (hce.smul hP)
  rw [sub_zero, one_smul] at h1
  rw [zero_smul, sub_zero] at h2
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [eventually_gt_atTop c] with e he
  have he0 : 0 < e := hc.trans he
  have h := congrArg (e⁻¹ • ·) (hres c e hc he0 he.ne)
  simp only [smul_smul, smul_sub] at h
  rw [mul_sub, inv_mul_cancel₀ he0.ne', one_smul, mul_comm e⁻¹ c] at h
  exact h.symm

omit [DecidableEq n] in
/-- `markov:eq:endpoint-relations`: `PK(c) = K(c)` for the fast limit `P`. -/
theorem fast_mul {P : Matrix n n ℝ} (hP : Tendsto K atTop (𝓝 P)) {c : ℝ} (hc : 0 < c) :
    P * K c = K c := by
  have h1 : Tendsto (fun e => K e * K c) atTop (𝓝 (P * K c)) := hP.mul_const (K c)
  have h2 : Tendsto (fun e => K e * K c) atTop (𝓝 (K c * P)) := by
    refine (hP.const_mul (K c)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with e he
    exact mul_comm_of_sameScale hres hc he
  rw [tendsto_nhds_unique h1 h2, mul_fast hres hP hc]

omit [DecidableEq n] in
/-- `markov:eq:endpoint-relations`: `K(c)Q = Q` for the slow limit `Q`. -/
theorem mul_slow {Q : Matrix n n ℝ} (hQ : Tendsto K (𝓝[>] 0) (𝓝 Q)) {c : ℝ} (hc : 0 < c) :
    K c * Q = Q := by
  have hid : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h1 : Tendsto (fun e => (e - c) • (K c * K e)) (𝓝[>] 0) (𝓝 ((0 - c) • (K c * Q))) :=
    (hid.sub tendsto_const_nhds).smul (hQ.const_mul (K c))
  have h2 : Tendsto (fun e => e • K c - c • K e) (𝓝[>] 0) (𝓝 ((0 : ℝ) • K c - c • Q)) :=
    (hid.smul tendsto_const_nhds).sub (hQ.const_smul c)
  have h := tendsto_nhds_unique h1 (h2.congr' ?_)
  · simp only [zero_sub, zero_smul, neg_smul, neg_inj] at h
    exact smul_right_injective _ hc.ne' h
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hc)]
      with e he hec
    exact (hres c e hc he (ne_of_gt hec)).symm

omit [DecidableEq n] in
/-- `markov:eq:endpoint-relations`: `QK(c) = Q` for the slow limit `Q`. -/
theorem slow_mul {Q : Matrix n n ℝ} (hQ : Tendsto K (𝓝[>] 0) (𝓝 Q)) {c : ℝ} (hc : 0 < c) :
    Q * K c = Q := by
  have h1 : Tendsto (fun e => K e * K c) (𝓝[>] 0) (𝓝 (Q * K c)) := hQ.mul_const (K c)
  have h2 : Tendsto (fun e => K e * K c) (𝓝[>] 0) (𝓝 (K c * Q)) := by
    refine (hQ.const_mul (K c)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    exact mul_comm_of_sameScale hres hc he
  rw [tendsto_nhds_unique h1 h2, mul_slow hres hQ hc]

end Endpoints

/-! ### Stochastic families -/

section Stochastic

open MarkovEffective StochasticIdempotent

/-- Entries of row-stochastic matrices lie in `[0, 1]`, so the family is bounded by `1`. -/
theorem abs_apply_le_one (hst : ∀ c : ℝ, 0 < c → K c ∈ rowStochastic ℝ n) :
    ∀ c : ℝ, 0 < c → ∀ a b, |K c a b| ≤ 1 := fun c hc a b =>
  abs_le.2 ⟨by linarith [nonneg_of_mem_rowStochastic (hst c hc) (i := a) (j := b)],
    le_one_of_mem_rowStochastic (hst c hc)⟩

/-- A family of row-stochastic matrices satisfying `markov:eq:same-scale`, together with its
limits `P` at `∞` and `Q` at `0⁺`, has all the crossover properties `IsCrossover`: the two
limits (the existence part of `markov:eq:fast-endpoint` and `markov:eq:slow-endpoint`, taken
here as hypotheses) and the four relations `markov:eq:endpoint-relations`. -/
theorem isCrossover (hst : ∀ c : ℝ, 0 < c → K c ∈ rowStochastic ℝ n)
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e)
    {P Q : Matrix n n ℝ} (hP : Tendsto K atTop (𝓝 P)) (hQ : Tendsto K (𝓝[>] 0) (𝓝 Q)) :
    IsCrossover K P Q where
  stochastic := hst
  resolvent_identity := hres
  tendsto_atTop := hP
  tendsto_zero := hQ
  fast_mul _ hc := fast_mul hres hP hc
  mul_fast _ hc := mul_fast hres hP hc
  mul_slow _ hc := mul_slow hres hQ hc
  slow_mul _ hc := slow_mul hres hQ hc

/-- Every family of real row-stochastic matrices satisfying `markov:eq:same-scale` has limits
`P` as `c → ∞` and `Q` as `c → 0⁺`, and satisfies `IsCrossover K P Q`. -/
theorem exists_isCrossover (hst : ∀ c : ℝ, 0 < c → K c ∈ rowStochastic ℝ n)
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e) :
    ∃ P Q : Matrix n n ℝ, Tendsto K atTop (𝓝 P) ∧ Tendsto K (𝓝[>] 0) (𝓝 Q) ∧
      IsCrossover K P Q := by
  obtain ⟨P, hP⟩ := exists_tendsto_atTop hres (abs_apply_le_one hst)
  obtain ⟨Q, hQ⟩ := exists_tendsto_zero hres (abs_apply_le_one hst)
  exact ⟨P, Q, hP, hQ, isCrossover hst hres hP hQ⟩

/-- `markov:thm:effective` for an arbitrary family `K(c)`, `c > 0`, of real row-stochastic
matrices satisfying `markov:eq:same-scale`, with its fast and slow limits `P` and `Q` (which
exist by `exists_isCrossover`). For the canonical splitting `P = UV` of
`markov:lem:splitting`, indexed by the closed classes of `P`, and `H(c) = VK(c)U`: the unique
`G` with `H(c) = c(cI + G)⁻¹` and `K(c) = Uc(cI + G)⁻¹V` for all `c > 0` is
`G = H(1)⁻¹ - I`; it is a real row Laplacian; `VQU` is its zero-eigenvalue projection and the
zero eigenvalue is semisimple; `dim ker G = rank Q`; and `rank G = p - rank Q`, where
`p = rank P` is the number of closed classes. `G` is indexed by the finset `closedClasses P`
itself, so no ordering of the classes is chosen. -/
theorem effective_of_sameScale (hst : ∀ c : ℝ, 0 < c → K c ∈ rowStochastic ℝ n)
    (hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e → (e - c) • (K c * K e) = e • K c - c • K e)
    {P Q : Matrix n n ℝ} (hP : Tendsto K atTop (𝓝 P)) (hQ : Tendsto K (𝓝[>] 0) (𝓝 Q)) :
    ∃ G : Matrix (closedClasses P) (closedClasses P) ℝ,
      G = (compress (splitV P) K (splitU P) 1)⁻¹ - 1 ∧
      (∀ G', (∀ c : ℝ, 0 < c → compress (splitV P) K (splitU P) c = Markov.resolvent G' c ∧
          K c = splitU P * Markov.resolvent G' c * splitV P) ↔ G' = G) ∧
      IsRowLaplacian G ∧
      Tendsto (compress (splitV P) K (splitU P)) (𝓝[>] 0) (𝓝 (splitV P * Q * splitU P)) ∧
      (splitV P * Q * splitU P) * (splitV P * Q * splitU P) = splitV P * Q * splitU P ∧
      G * (splitV P * Q * splitU P) = 0 ∧ (splitV P * Q * splitU P) * G = 0 ∧
      LinearMap.ker G.mulVecLin = LinearMap.range (splitV P * Q * splitU P).mulVecLin ∧
      LinearMap.ker (splitV P * Q * splitU P).mulVecLin = LinearMap.range G.mulVecLin ∧
      (∀ y, G *ᵥ (G *ᵥ y) = 0 → G *ᵥ y = 0) ∧
      splitU P * (splitV P * Q * splitU P) * splitV P = Q ∧
      (splitV P * Q * splitU P).rank = Q.rank ∧
      Module.finrank ℝ (LinearMap.ker G.mulVecLin) = Q.rank ∧
      G.rank + Q.rank = P.rank ∧ P.rank = (closedClasses P).card ∧
      G.rank = (closedClasses P).card - Q.rank := by
  obtain ⟨G, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    effective_reconstruction_canonical (isCrossover hst hres hP hQ)
  exact ⟨G, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, by omega⟩

end Stochastic

end Family

/-! ### The actual shadow -/

section Shadow

open MarkovEffective StochasticIdempotent MarkovShadow MarkovForest

variable {n : Type*} [Fintype n] [DecidableEq n]
  {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {q : n → n → Lex (_root_.HahnSeries Γ ℝ)}

/-- The shadow `c ↦ K_α(c)` agrees with a real rational matrix function outside a finite set:
`K_α(c)_{ab} = N_{ab}(c)/D(c)` for every `c > 0` with `D(c) ≠ 0`, where `D ≠ 0` has finitely
many roots (`exists_rational` applied through `MarkovShadow.shadow_same_scale`). The `N_{ab}`
and `D` come from `K_α(1)` alone; this is not the leading-forest formula
`markov:eq:shadow-formula` of `markov:thm:leading`, which remains pending. -/
theorem exists_rational_shadow (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (α : Γ) :
    ∃ (N : n → n → Polynomial ℝ) (D : Polynomial ℝ), D ≠ 0 ∧ {c : ℝ | D.eval c = 0}.Finite ∧
      ∀ c : ℝ, 0 < c → D.eval c ≠ 0 → ∀ a b,
        shadow (rowLaplacian q) α c a b = (N a b).eval c / D.eval c :=
  exists_rational fun _ _ hc he _ => shadow_same_scale hq α hc he

/-- For every scale `α`, the shadow `K_α(c) = res R_L(ct^α)` has a limit `P` as `c → ∞` and a
limit `Q` as `c → 0⁺`, and these limits satisfy `IsCrossover`, in particular
`markov:eq:endpoint-relations`. This is the existence part of `markov:eq:fast-endpoint` and
`markov:eq:slow-endpoint`; the closed forms `B_{k₋}/b_{k₋}` and `B_{k₊}/b_{k₊}` belong to
`markov:thm:flag` and are pending. -/
theorem exists_isCrossover_shadow (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (α : Γ) :
    ∃ P Q : Matrix n n ℝ, Tendsto (shadow (rowLaplacian q) α) atTop (𝓝 P) ∧
      Tendsto (shadow (rowLaplacian q) α) (𝓝[>] 0) (𝓝 Q) ∧
      IsCrossover (shadow (rowLaplacian q) α) P Q :=
  exists_isCrossover (fun _ hc => shadow_mem_rowStochastic hq α hc)
    (fun _ _ hc he _ => shadow_same_scale hq α hc he)

/-- `markov:thm:effective` for the actual shadow `K_α(c) = res R_L(ct^α)` at every scale `α`,
critical or not, where `L` is the row Laplacian of rates with nonnegative off-diagonal
entries in `ℝ((t^Γ))`. The fast and slow endpoints `P = lim_{c → ∞} K_α(c)` and
`Q = lim_{c → 0⁺} K_α(c)` exist (the existence part of `markov:eq:fast-endpoint` and
`markov:eq:slow-endpoint`; the closed forms belong to `markov:thm:flag` and are pending). For
the canonical splitting `P = UV` of `markov:lem:splitting` and `H(c) = VK_α(c)U`, exactly one
`G` satisfies `H(c) = c(cI + G)⁻¹` and `K_α(c) = Uc(cI + G)⁻¹V` for every `c > 0`, namely
`G = H(1)⁻¹ - I`. It is a real row Laplacian, its zero eigenvalue is semisimple with
projection `VQU`, its kernel has dimension `rank Q`, and `rank G = p - rank Q` with
`p = rank P` the number of closed classes. `G` is indexed by the finset `closedClasses P`
itself, so no ordering of the classes is chosen. The source's remark that reordering the
classes only permutes `G` is not part of this statement; it is
`MarkovEffective.effectiveGenerator_compress_submatrix` with
`MarkovEffective.IsSplitting.submatrix`, which apply to the shadow unchanged. -/
theorem effective_shadow (hq : ∀ i j, i ≠ j → 0 ≤ q i j) (α : Γ) :
    ∃ P Q : Matrix n n ℝ, Tendsto (shadow (rowLaplacian q) α) atTop (𝓝 P) ∧
      Tendsto (shadow (rowLaplacian q) α) (𝓝[>] 0) (𝓝 Q) ∧
      ∃ G : Matrix (closedClasses P) (closedClasses P) ℝ,
        G = (compress (splitV P) (shadow (rowLaplacian q) α) (splitU P) 1)⁻¹ - 1 ∧
        (∀ G', (∀ c : ℝ, 0 < c →
            compress (splitV P) (shadow (rowLaplacian q) α) (splitU P) c =
              Markov.resolvent G' c ∧
            shadow (rowLaplacian q) α c = splitU P * Markov.resolvent G' c * splitV P) ↔
          G' = G) ∧
        IsRowLaplacian G ∧
        Tendsto (compress (splitV P) (shadow (rowLaplacian q) α) (splitU P)) (𝓝[>] 0)
          (𝓝 (splitV P * Q * splitU P)) ∧
        (splitV P * Q * splitU P) * (splitV P * Q * splitU P) = splitV P * Q * splitU P ∧
        G * (splitV P * Q * splitU P) = 0 ∧ (splitV P * Q * splitU P) * G = 0 ∧
        LinearMap.ker G.mulVecLin = LinearMap.range (splitV P * Q * splitU P).mulVecLin ∧
        LinearMap.ker (splitV P * Q * splitU P).mulVecLin = LinearMap.range G.mulVecLin ∧
        (∀ y, G *ᵥ (G *ᵥ y) = 0 → G *ᵥ y = 0) ∧
        splitU P * (splitV P * Q * splitU P) * splitV P = Q ∧
        (splitV P * Q * splitU P).rank = Q.rank ∧
        Module.finrank ℝ (LinearMap.ker G.mulVecLin) = Q.rank ∧
        G.rank + Q.rank = P.rank ∧ P.rank = (closedClasses P).card ∧
        G.rank = (closedClasses P).card - Q.rank := by
  have hst : ∀ c : ℝ, 0 < c → shadow (rowLaplacian q) α c ∈ rowStochastic ℝ n :=
    fun _ hc => shadow_mem_rowStochastic hq α hc
  have hres : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e →
      (e - c) • (shadow (rowLaplacian q) α c * shadow (rowLaplacian q) α e) =
        e • shadow (rowLaplacian q) α c - c • shadow (rowLaplacian q) α e :=
    fun _ _ hc he _ => shadow_same_scale hq α hc he
  obtain ⟨P, Q, hP, hQ, -⟩ := exists_isCrossover hst hres
  exact ⟨P, Q, hP, hQ, effective_of_sameScale hst hres hP hQ⟩

end Shadow

end

end Surreal.PseudoResolventLimits
