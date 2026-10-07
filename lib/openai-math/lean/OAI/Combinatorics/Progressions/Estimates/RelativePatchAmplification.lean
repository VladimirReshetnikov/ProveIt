import OAI.Combinatorics.Progressions.Lattices.CRTProgressionVanishing
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialAffineDegree
import OAI.Combinatorics.Progressions.Probability.LowDensityAmplification
import OAI.Combinatorics.Progressions.Probability.RecursiveDensityDiscount

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def relativePatchComplexity {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : ℝ :=
  (d : ℝ) + Real.log (1 + (A.kernel.lip : ℝ))

noncomputable def relativePatchDistinctWeights {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : ℕ :=
  (Finset.univ.image A.weight).card

noncomputable def relativePatchBoxScore {X : Type*} [Fintype X] [DecidableEq X]
    {s d : ℕ} (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) : ℝ :=
  𝔼 x ∈ integerBox N, (f x - a) * A.value (fun i => (x i : ℝ))

noncomputable def relativePatchSliceScore {X : Type*} [Fintype X] {s d q : ℕ}
    {N : X → ℕ} (S : ResidueBoxSlice N q) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) : ℝ :=
  𝔼 x : ∀ i, Fin (S.length i),
    (f (fun i => ((S.point x i).val : ℤ)) - a) * A.value (fun i => ((x i).val : ℝ))

def RelativePatchSliceConclusion {X : Type*} [Fintype X] (s : ℕ)
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ) (rankBound : ℕ) (cost : ℝ) : Prop :=
  ∃ (q : ℕ), 0 < q ∧ ∃ (S : ResidueBoxSlice N q) (d : ℕ)
    (A : PolynomialPatch X s d),
    (∀ i, Real.exp (-cost) * (N i : ℝ) ≤ (S.length i : ℝ)) ∧
    d ≤ rankBound ∧ relativePatchComplexity A ≤ cost ∧
    Real.exp (-cost) ≤ relativePatchSliceScore S f target A

def RelativePatchAbsoluteRule (s n₀ : ℕ) (p a Λ : ℝ) (d₀ : ℕ) : Prop :=
  ∀ (N : Fin n₀ → ℕ),
    (∀ i, (N i).Prime) → Function.Injective N →
    (∀ i j, N i ≤ 2 ^ (n₀ + 1) * N j) →
    (∀ i, Real.exp p ≤ (N i : ℝ)) →
    ∀ (f : (Fin n₀ → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a ≤ (𝔼 x ∈ integerBox N, f x) →
      RelativePatchSliceConclusion s N f Λ d₀ p

def RelativePatchInductionRule (s n₀ stage : ℕ) (τ : ℝ)
    (cutoff cost : ℝ → ℝ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X],
      (Fintype.card X : ℝ) ≤ p →
      ∀ (N : X → ℕ), (∀ i, Real.exp (cutoff p) ≤ (N i : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
        (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        ∀ (d : ℕ) (A : PolynomialPatch X s d),
          relativePatchComplexity A ≤ p → relativePatchDistinctWeights A ≤ stage →
          Real.exp (-p) ≤ relativePatchBoxScore N f a A →
          RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage + 1) * Λ)
            (d₀ + s * d) (cost p)

def RelativePatchPowerInductionRule (s n₀ stage : ℕ) (τ : ℝ) (E : ℕ) : Prop :=
  RelativePatchInductionRule s n₀ stage τ (fun p => (p + 2) ^ E) (fun p => (p + 2) ^ E)

theorem relativePatchComplexity_rank_le {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : (d : ℝ) ≤ relativePatchComplexity A := by
  have hlog : 0 ≤ Real.log (1 + (A.kernel.lip : ℝ)) :=
    Real.log_nonneg (by linarith [A.kernel.lip.coe_nonneg])
  exact le_add_of_nonneg_right hlog

theorem relativePatchDistinctWeights_eq_zero_iff {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : relativePatchDistinctWeights A = 0 ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have hm : A.weight i ∈ Finset.univ.image A.weight :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have he : Finset.univ.image A.weight = ∅ := Finset.card_eq_zero.mp h
    simp only [he, Finset.notMem_empty] at hm
  · rintro rfl
    simp [relativePatchDistinctWeights]

theorem RelativePatchSliceConclusion.mono {X : Type*} [Fintype X] {s : ℕ}
    {N : X → ℕ} {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound rankBound' : ℕ}
    {cost cost' : ℝ} (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hrank : rankBound ≤ rankBound') (hcost : cost ≤ cost') :
    RelativePatchSliceConclusion s N f target rankBound' cost' := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  have he : Real.exp (-cost') ≤ Real.exp (-cost) :=
    Real.exp_le_exp.mpr (neg_le_neg hcost)
  exact ⟨q, hq, S, d, A, fun i =>
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)).trans (hlength i),
    hd.trans hrank, hcomplexity.trans hcost, he.trans hscore⟩

theorem RelativePatchInductionRule.mono {s n₀ stage : ℕ} {τ : ℝ}
    {cutoff cost cutoff' cost' : ℝ → ℝ}
    (h : RelativePatchInductionRule s n₀ stage τ cutoff cost)
    (hcutoff : ∀ p, 2 ≤ p → cutoff p ≤ cutoff' p)
    (hcost : ∀ p, 2 ≤ p → cost p ≤ cost' p) :
    RelativePatchInductionRule s n₀ stage τ cutoff' cost' := by
  intro p a Λ d₀ hp ha haΛ hΛ habsolute X _ _ _ hX N hN f hf hfree d A hA hstage hscore
  have hN' : ∀ i, Real.exp (cutoff p) ≤ (N i : ℝ) :=
    fun i => (Real.exp_le_exp.mpr (hcutoff p hp)).trans (hN i)
  exact (h p a Λ d₀ hp ha haΛ hΛ habsolute X hX N hN' f hf hfree d A hA hstage hscore).mono
    (le_refl _) (hcost p hp)

end Erdos3

end

section

namespace Erdos3

theorem recursive_discount_target_mem_Icc {discount Λ : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1) (hΛ : Λ ∈ Set.Icc (0 : ℝ) 1)
    (stage : ℕ) : (1 - discount) ^ (stage + 1) * Λ ∈ Set.Icc (0 : ℝ) 1 := by
  have hbase : 0 ≤ 1 - discount := sub_nonneg.mpr hdiscount.2
  have hbase1 : 1 - discount ≤ 1 := by linarith only [hdiscount.1]
  have hpow : (1 - discount) ^ (stage + 1) ≤ 1 := pow_le_one₀ hbase hbase1
  exact ⟨mul_nonneg (pow_nonneg hbase _) hΛ.1,
    (mul_le_mul hpow hΛ.2 hΛ.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem RelativePatchSliceConclusion.cost_nonneg {X : Type*} [Fintype X]
    {s rank : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target cost : ℝ}
    (h : RelativePatchSliceConclusion s N f target rank cost) : 0 ≤ cost := by
  obtain ⟨q, hq, slice, d, patch, hlength, hrank, hcomplexity, hscore⟩ := h
  exact (Nat.cast_nonneg d).trans ((relativePatchComplexity_rank_le patch).trans hcomplexity)

theorem frozen_side_le_exp_of_keep_threshold {ι : Type*}
    (sides : ι → ℕ) (keep : ι → Prop) (H : ℕ) {cost : ℝ}
    (hkeep : ∀ i, keep i ↔ H ≤ sides i) (hH : (H : ℝ) ≤ Real.exp cost) :
    ∀ i : {i // ¬keep i}, (sides i.val : ℝ) ≤ Real.exp cost := by
  intro i
  have hside : sides i.val < H := Nat.lt_of_not_ge (fun h => i.property ((hkeep i.val).mpr h))
  exact (Nat.cast_le.mpr hside.le).trans hH

end Erdos3

end

section

namespace Erdos3

theorem RelativePatchAbsoluteRule.mono {s n₀ d₀ : ℕ} {p p' a Λ : ℝ}
    (h : RelativePatchAbsoluteRule s n₀ p a Λ d₀) (hpp : p ≤ p') :
    RelativePatchAbsoluteRule s n₀ p' a Λ d₀ := by
  intro N hprime hinj hratio hsize f hf hfree hmean
  exact (h N hprime hinj hratio
    (fun i => (Real.exp_le_exp.mpr hpp).trans (hsize i)) f hf hfree hmean).mono le_rfl hpp

end Erdos3

end

section

namespace Erdos3

theorem exists_relativePatch_finite_stage_power_assembly (s n₀ b₀ c : ℕ) (τ : ℝ) :
    ∃ E : ℕ, 2 ≤ E ∧
      let budget := fun q p => (relativeInductionBudgetPolynomial b₀ c q).eval₂
        (Nat.castRingHom ℝ) p
      RelativePatchInductionRule s n₀ 0 τ (budget 0) (budget 0) →
      (∀ q < s,
        RelativePatchInductionRule s n₀ q τ (budget q) (budget q) →
        RelativePatchInductionRule s n₀ (q+1) τ (budget (q+1)) (budget (q+1))) →
      ∀ q ≤ s, RelativePatchPowerInductionRule s n₀ q τ E := by
  obtain ⟨E, hE, hbound⟩ := exists_relativeInductionPolynomialBudget b₀ c s
  refine ⟨E, hE, ?_⟩
  intro budget hbase hstep
  have hstages : ∀ q ≤ s,
      RelativePatchInductionRule s n₀ q τ (budget q) (budget q) := by
    intro q
    induction q with
    | zero => intro _; exact hbase
    | succ q ih =>
      intro hq
      exact hstep q (by omega) (ih (by omega))
  intro q hq
  apply (hstages q hq).mono
  · intro p hp
    exact (hbound q hq p (by linarith)).2
  · intro p hp
    exact (hbound q hq p (by linarith)).2

theorem exists_relativePatch_majorized_stage_power_assembly (s n₀ b₀ c : ℕ) (τ : ℝ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ budget : ℕ → ℝ → ℝ,
      (∀ q p, 0 ≤ p → 0 ≤ budget q p) →
      (∀ p, 0 ≤ p → budget 0 p ≤ (p+2)^b₀) →
      (∀ q < s, ∀ p, 0 ≤ p →
        budget (q+1) p ≤ (2+(2+p+budget q ((p+2)^c))^c)^c) →
      RelativePatchInductionRule s n₀ 0 τ (budget 0) (budget 0) →
      (∀ q < s,
        RelativePatchInductionRule s n₀ q τ (budget q) (budget q) →
        RelativePatchInductionRule s n₀ (q+1) τ (budget (q+1)) (budget (q+1))) →
      ∀ q ≤ s, RelativePatchPowerInductionRule s n₀ q τ E := by
  obtain ⟨E,hE,hbound⟩ := exists_relativeInductionBudget_majorization b₀ c s
  refine ⟨E,hE,?_⟩
  intro budget hnonneg hbasecost hstepcost hbase hstep
  have hstages : ∀ q ≤ s,
      RelativePatchInductionRule s n₀ q τ (budget q) (budget q) := by
    intro q
    induction q with
    | zero => intro _; exact hbase
    | succ q ih => intro hq; exact hstep q (by omega) (ih (by omega))
  intro q hq
  apply (hstages q hq).mono
  · intro p hp
    exact hbound budget hnonneg hbasecost hstepcost q hq p (by linarith)
  · intro p hp
    exact hbound budget hnonneg hbasecost hstepcost q hq p (by linarith)

end Erdos3

end

section

namespace Erdos3

theorem relativePatchComplexity_kernel_bound {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) {U : ℝ} (hA : relativePatchComplexity A ≤ U) :
    (A.kernel.lip : ℝ) + 1 ≤ Real.exp U := by
  have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ U := by
    unfold relativePatchComplexity at hA
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hpos : 0 < 1 + (A.kernel.lip : ℝ) := by positivity
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hpos] at h
  linarith

theorem log_length_lower_of_exp_slice {N M : ℕ} {U : ℝ}
    (hN : 0 < N) (hM : Real.exp (-U) * (N : ℝ) ≤ M) :
    0 < M ∧ Real.log (N : ℝ) - U ≤ Real.log (M : ℝ) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod := mul_pos (Real.exp_pos (-U)) hNreal
  have hMreal : (0 : ℝ) < M := hprod.trans_le hM
  refine ⟨by exact_mod_cast hMreal, ?_⟩
  have h := Real.log_le_log hprod hM
  rw [Real.log_mul (Real.exp_pos _).ne' hNreal.ne', Real.log_exp] at h
  linarith

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchBoxScore_rank_zero {X : Type*} [Fintype X] [DecidableEq X]
    {s : ℕ} (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s 0) :
    relativePatchBoxScore N f a A = (𝔼 x ∈ integerBox N, (f x - a)) * A.kernel.value 0 := by
  simp only [relativePatchBoxScore, PolynomialPatch.value_rank_zero, ← Finset.expect_mul]

theorem relativePatch_mean_increment_of_zero_weights
    {X : Type*} [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) (hweights : relativePatchDistinctWeights A ≤ 0)
    {gain : ℝ} (hgain : 0 < gain) (hscore : gain ≤ relativePatchBoxScore N f a A) :
    gain ≤ 𝔼 x ∈ integerBox N, (f x - a) := by
  have hd : d = 0 := (relativePatchDistinctWeights_eq_zero_iff A).mp (by omega)
  subst d
  rw [relativePatchBoxScore_rank_zero] at hscore
  have hmean : 0 ≤ 𝔼 x ∈ integerBox N, (f x - a) := by
    by_contra! hneg
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg hneg.le (A.kernel.nonneg 0)
    linarith only [hgain, hscore, hnonpos]
  exact hscore.trans (mul_le_of_le_one_right hmean (A.kernel.le_one 0))

theorem relativePatch_density_increment_of_zero_weights
    {X : Type*} [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) (hweights : relativePatchDistinctWeights A ≤ 0)
    {gain : ℝ} (hgain : 0 < gain) (hscore : gain ≤ relativePatchBoxScore N f a A) :
    a + gain ≤ 𝔼 x ∈ integerBox N, f x := by
  have h := relativePatch_mean_increment_of_zero_weights N f a A hweights hgain hscore
  rw [Finset.expect_sub_distrib, Finset.expect_const hbox] at h
  linarith only [h]

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

def identity (N : I → ℕ) : ResidueBoxSlice N 1 where
  start _ := 0
  length := N
  inside _ _ hj := by simpa using hj

def comp (S : ResidueBoxSlice N q) {r : ℕ} (T : ResidueBoxSlice S.length r) :
    ResidueBoxSlice N (q * r) where
  start i := S.start i + q * T.start i
  length := T.length
  inside i j hj := by
    have h := S.inside i (T.start i + r * j) (T.inside i j hj)
    simpa only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using h

@[simp] theorem comp_point (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (x : ∀ i, Fin (T.length i)) :
    (S.comp T).point x = S.point (T.point x) := by
  ext i
  simp [comp, point, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

noncomputable def polynomial (S : ResidueBoxSlice N q) (i : I) : MvPolynomial I ℝ :=
  MvPolynomial.C (S.start i : ℝ) + MvPolynomial.C (q : ℝ) * MvPolynomial.X i

theorem polynomial_degree (S : ResidueBoxSlice N q) (i : I) :
    (S.polynomial i).totalDegree ≤ 1 := by
  dsimp only [polynomial]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C, zero_le]
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl])

@[simp] theorem polynomial_eval (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) (i : I) :
    MvPolynomial.aeval (R := ℝ) (fun i => ((x i).val : ℝ)) (S.polynomial i) =
      ((S.point x i).val : ℝ) := by
  simp [polynomial, point, Nat.cast_add, Nat.cast_mul]

end ResidueBoxSlice

namespace VectorPolynomial

theorem coefficients_substitute_mem {I K V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : Submodule ℝ V) (f : I → MvPolynomial K ℝ) (p : VectorPolynomial I ℝ V)
    (hp : ∀ α, coefficients p α ∈ W) :
    ∀ α, coefficients (substitute f p) α ∈ W := by
  intro α
  rw [coefficients_substitute]
  exact W.sum_mem (fun β _ => W.smul_mem _ (hp β))

theorem eval_slice_substitute {I V : Type*} [AddCommGroup V] [Module ℝ V]
    {N : I → ℕ} {q : ℕ} (S : ResidueBoxSlice N q) (p : VectorPolynomial I ℝ V)
    (x : ∀ i, Fin (S.length i)) :
    eval (fun i => ((x i).val : ℝ)) (substitute S.polynomial p) =
      eval (fun i => ((S.point x i).val : ℝ)) p := by
  simp only [eval_substitute, ResidueBoxSlice.polynomial_eval]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

theorem comp_length_exp_lower
    (A : ResidueBoxSlice N q) (B : ResidueBoxSlice A.length r) {u v : ℝ}
    (hA : ∀ i, Real.exp (-u) * (N i : ℝ) ≤ A.length i)
    (hB : ∀ i, Real.exp (-v) * (A.length i : ℝ) ≤ B.length i) :
    ∀ i, Real.exp (-(u + v)) * (N i : ℝ) ≤ (A.comp B).length i := by
  intro i
  change Real.exp (-(u + v)) * (N i : ℝ) ≤ (B.length i : ℝ)
  calc
    Real.exp (-(u + v)) * (N i : ℝ) =
        Real.exp (-v) * (Real.exp (-u) * (N i : ℝ)) := by
      rw [neg_add, Real.exp_add]
      ring
    _ ≤ Real.exp (-v) * (A.length i : ℝ) :=
      mul_le_mul_of_nonneg_left (hA i) (Real.exp_pos _).le
    _ ≤ (B.length i : ℝ) := hB i

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} {N : X → ℕ} {q : ℕ}

def integerAffine (S : ResidueBoxSlice N q) (x : X → ℤ) : X → ℤ :=
  fun i => (S.start i : ℤ) + (q : ℤ) * x i

def integerPullback (S : ResidueBoxSlice N q) (f : (X → ℤ) → ℝ) :
    (X → ℤ) → ℝ := fun x => f (S.integerAffine x)

@[simp] theorem integerAffine_finPoint (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) :
    S.integerAffine (fun i => ((x i).val : ℤ)) =
      fun i => ((S.point x i).val : ℤ) := by
  funext i
  simp [integerAffine, point, Nat.cast_add, Nat.cast_mul]

theorem integerAffine_mem_integerBox [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) {x : X → ℤ} (hx : x ∈ integerBox S.length) :
    S.integerAffine x ∈ integerBox N := by
  have hx' := (mem_integerBox S.length x).mp hx
  apply (mem_integerBox N _).mpr
  intro i
  have hnat : (x i).toNat < S.length i := by
    have := hx' i
    omega
  have hin := S.inside i (x i).toNat hnat
  have hcast : (S.start i : ℤ) + (q : ℤ) * ((x i).toNat : ℤ) < (N i : ℤ) := by
    exact_mod_cast hin
  rw [Int.toNat_of_nonneg (hx' i).1] at hcast
  exact ⟨add_nonneg (Int.natCast_nonneg _) (mul_nonneg (Int.natCast_nonneg _) (hx' i).1),
    hcast⟩

theorem pullback_mem_Icc [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) {f : (X → ℤ) → ℝ}
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x ∈ integerBox S.length, S.integerPullback f x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  exact hf _ (S.integerAffine_mem_integerBox hx)

theorem pullback_apFree [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) (hq : 0 < q) {f : (X → ℤ) → ℝ} {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {x | x ∈ integerBox S.length ∧ S.integerPullback f x ≠ 0} k := by
  intro a d hd
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hstep : (fun j => (q : ℤ) * d j) ≠ 0 := by
    intro he
    apply hd
    funext j
    exact (mul_eq_zero.mp (congrFun he j)).resolve_left hq0
  obtain ⟨i, hi⟩ := hfree (S.integerAffine a) (fun j => (q : ℤ) * d j) hstep
  refine ⟨i, ?_⟩
  rintro ⟨hx, hf⟩
  apply hi
  have he : S.integerAffine a + (i.val : ℤ) • (fun j => (q : ℤ) * d j) =
      S.integerAffine (a + (i.val : ℤ) • d) := by
    funext j
    simp only [integerAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact ⟨S.integerAffine_mem_integerBox hx, hf⟩

@[simp] theorem integerAffine_comp (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (x : X → ℤ) :
    (S.comp T).integerAffine x = S.integerAffine (T.integerAffine x) := by
  funext i
  simp only [integerAffine, comp, Nat.cast_add, Nat.cast_mul]
  ring

@[simp] theorem integerPullback_comp (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (f : (X → ℤ) → ℝ) :
    (S.comp T).integerPullback f = T.integerPullback (S.integerPullback f) := by
  funext x
  simp only [integerPullback, integerAffine_comp]

end ResidueBoxSlice

theorem relativePatchBoxScore_pullback {X : Type*} [Fintype X] [DecidableEq X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore S.length (S.integerPullback f) a A =
      relativePatchSliceScore S f a A := by
  classical
  symm
  unfold relativePatchSliceScore relativePatchBoxScore
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    exact (mem_integerBox S.length _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩)
  · intro t _
    simp only [ResidueBoxSlice.integerPullback, ResidueBoxSlice.integerAffine_finPoint,
      Int.cast_natCast]
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox S.length x).mp hx
    refine ⟨fun i => ⟨(x i).toNat, by have := hx' i; omega⟩, by simp only [Finset.mem_univ], ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hx' i).1

theorem relativePatchSliceScore_comp {X : Type*} [Fintype X]
    {s d q r : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (f : (X → ℤ) → ℝ)
    (a : ℝ) (A : PolynomialPatch X s d) :
    relativePatchSliceScore T (S.integerPullback f) a A =
      relativePatchSliceScore (S.comp T) f a A := by
  unfold relativePatchSliceScore
  apply Finset.expect_congr rfl
  intro x _
  simp only [ResidueBoxSlice.integerPullback, ResidueBoxSlice.integerAffine_finPoint,
    ResidueBoxSlice.comp_point]

theorem RelativePatchSliceConclusion.comp {X : Type*} [Fintype X]
    {s q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q) (hq : 0 < q)
    {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound : ℕ} {u v : ℝ}
    (hu : 0 ≤ u)
    (hlength : ∀ i, Real.exp (-u) * (N i : ℝ) ≤ S.length i)
    (h : RelativePatchSliceConclusion s S.length (S.integerPullback f)
      target rankBound v) :
    RelativePatchSliceConclusion s N f target rankBound (u + v) := by
  obtain ⟨r, hr, T, d, A, hT, hd, hcomplexity, hscore⟩ := h
  refine ⟨q * r, Nat.mul_pos hq hr, S.comp T, d, A,
    S.comp_length_exp_lower T hlength hT, hd, ?_, ?_⟩
  · exact hcomplexity.trans (by linarith)
  · rw [← relativePatchSliceScore_comp]
    exact (Real.exp_le_exp.mpr (by linarith : -(u + v) ≤ -v)).trans hscore

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchDistinctWeights_le_degree {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : relativePatchDistinctWeights A ≤ s := by
  have hsub : Finset.univ.image A.weight ⊆ Finset.Icc 1 s := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_Icc.mpr ⟨A.weight_pos i, A.weight_le i⟩
  have h := Finset.card_le_card hsub
  simpa only [relativePatchDistinctWeights, Nat.card_Icc, Nat.add_sub_cancel] using h

def LowDensityRelativeAbsoluteRule (s n₀ : ℕ) (p H : ℝ) (D : ℕ) (x : ℝ) : Prop :=
  ∀ a : ℝ, Real.exp (-p) ≤ a → LowDensityThreshold H a →
    RelativePatchAbsoluteRule s n₀ x a (H * a) D

theorem RelativePatchPowerInductionRule.amplify
    {s n₀ E D : ℕ} [NeZero n₀] {τ x H a : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hx : 2 ≤ x) (hn : (n₀ : ℝ) ≤ x) (hH : 1 ≤ H)
    (ha : Real.exp (-x) ≤ a) (hraw : H * (H * a) ≤ 1)
    (hfirst : RelativePatchAbsoluteRule s n₀ x a (H * a) D)
    (hsecond : RelativePatchAbsoluteRule s n₀ x (H * a) (H * (H * a)) D) :
    RelativePatchAbsoluteRule s n₀ (x + (x + 2) ^ E) a
      (((1 - τ) ^ (s + 1) * H ^ 2) * a) ((s + 1) * D) := by
  intro N hprime hinj hratio hsize f hf hfree hmean
  have hx0 : 0 ≤ x := by linarith
  have hcost : 0 ≤ (x + 2) ^ E := pow_nonneg (by linarith) _
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ :=
    hfirst N hprime hinj hratio
      (fun i => (Real.exp_le_exp.mpr (le_add_of_nonneg_right hcost)).trans (hsize i))
      f hf hfree hmean
  have hlength' : ∀ i, Real.exp ((x + 2) ^ E) ≤ (S.length i : ℝ) := by
    intro i
    calc
      Real.exp ((x + 2) ^ E) = Real.exp (-x) * Real.exp (x + (x + 2) ^ E) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-x) * (N i : ℝ) :=
        mul_le_mul_of_nonneg_left (hsize i) (Real.exp_pos _).le
      _ ≤ (S.length i : ℝ) := hlength i
  have ha0 : 0 ≤ a := (Real.exp_pos _).le.trans ha
  have hab : a ≤ H * a := by nlinarith
  have hbb : H * a ≤ H * (H * a) := by
    exact mul_le_mul_of_nonneg_left hab (by linarith)
  have hnew := hrelative x (H * a) (H * (H * a)) D hx (ha.trans hab) hbb hraw
    hsecond (Fin n₀) (by simpa using hn) S.length hlength'
    (S.integerPullback f) (S.pullback_mem_Icc hf) (S.pullback_apFree hq hfree)
    d A hcomplexity (relativePatchDistinctWeights_le_degree A)
    (by rw [relativePatchBoxScore_pullback]; exact hscore)
  have hcomposed := hnew.comp S hq hx0 hlength
  have hrank : D + s * d ≤ (s + 1) * D := by nlinarith
  convert hcomposed.mono hrank le_rfl using 1
  ring

theorem LowDensityRelativeAbsoluteRule.amplify
    {s n₀ E D : ℕ} [NeZero n₀] {τ p x H : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hprevious : LowDensityRelativeAbsoluteRule s n₀ p H D x)
    (hx : 2 ≤ x) (hn : (n₀ : ℝ) ≤ x) (hpx : p ≤ x) (hH : 1 < H)
    (hdiscount : 1 ≤ ((1 - τ) ^ (s + 1)) ^ 2 * H) :
    LowDensityRelativeAbsoluteRule s n₀ p ((1 - τ) ^ (s + 1) * H ^ 2)
      ((s + 1) * D) (x + (x + 2) ^ E) := by
  intro a ha hlow
  obtain ⟨hlow₁, hab⟩ := hlow.of_next hH hdiscount
  have hlow₂ := hlow.mul_of_next hH hdiscount
  exact hrelative.amplify hx hn hH.le
    ((Real.exp_le_exp.mpr (neg_le_neg hpx)).trans ha)
    (hlow₂.raw_target_lt_one hH).le
    (hprevious a ha hlow₁) (hprevious (H * a) (ha.trans hab) hlow₂)

theorem LowDensityRelativeAbsoluteRule.amplify_power
    {s n₀ E D : ℕ} [NeZero n₀] {τ p x H : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hprevious : LowDensityRelativeAbsoluteRule s n₀ p H D x)
    (hx : 2 ≤ x) (hn : (n₀ : ℝ) ≤ x) (hpx : p ≤ x) (hH : 1 < H)
    (hdiscount : 1 ≤ ((1 - τ) ^ (s + 1)) ^ 2 * H) :
    LowDensityRelativeAbsoluteRule s n₀ p ((1 - τ) ^ (s + 1) * H ^ 2)
      ((s + 1) * D) ((2 + x) ^ (E + 1)) := by
  intro a ha hlow
  exact ((LowDensityRelativeAbsoluteRule.amplify hrelative hprevious hx hn hpx hH hdiscount) a ha hlow).mono
    (by simpa only [add_comm x 2] using amplificationResource_room (by linarith : 0 ≤ x) E)

end Erdos3

end

end OAI
