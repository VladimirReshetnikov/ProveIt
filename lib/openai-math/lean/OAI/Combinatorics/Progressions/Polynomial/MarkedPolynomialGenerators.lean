/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Combinatorics.Progressions.Estimates.CommonDependentIntegralModel

namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_le_markedDegree {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedLieSpan v w marked d k l ≤ F.layer k l := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, _, hk, hl, rfl⟩
  have hweight := hk.trans
    ((lieTreeMarkedCount_le_length marked a).trans (lieTree_length_le_weight w hw a))
  exact F.degree_antitone l hweight
    (F.rank_antitone (lieTreeWeight w a) hl (F.lieTreeEval_mem_length v w hv a))

noncomputable def markedPolynomialLayer (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (d k l : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈
    markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (markedLieSpan v w marked _ _ _).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (markedLieSpan v w marked _ _ _).smul_mem c (hp α)

theorem markedPolynomialLayer_antitone (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    markedPolynomialLayer (σ := σ) v w marked e m n ≤ markedPolynomialLayer v w marked d k l := by
  intro p hp α
  exact markedLieSpan_antitone v w marked hde (Nat.add_le_add_right hkm _) hln (hp α)

theorem monomial_mem_markedPolynomialLayer (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (d k l : ℕ) (α : σ →₀ ℕ) {x : L}
    (hx : x ∈ markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l) :
    monomial (R := ℚ) α x ∈ markedPolynomialLayer v w marked d k l := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp only [coefficients_monomial, Finsupp.single_eq_of_ne (Ne.symm h), Submodule.zero_mem]

theorem markedPolynomialLayer_lie_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ markedPolynomialLayer v w marked d k l)
    (hq : q ∈ markedPolynomialLayer v w marked e m n) :
    ⁅p, q⁆ ∈ markedPolynomialLayer v w marked (d + e) (k + m) (l + n) := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, sum_lie_sum]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  apply monomial_mem_markedPolynomialLayer
  simpa only [map_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    markedLieSpan_lie_mem v w marked (hp α) (hq β)

theorem markedPolynomialLayer_directionalDerivative [Fintype σ]
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (h : σ → ℚ)
    {d k l : ℕ} {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    directionalDerivative h p ∈ markedPolynomialLayer v w marked d (k + 1) l := by
  intro α
  change coefficients (directionalDerivative h p) α ∈
    markedLieSpan v w marked d (k + 1 + Finsupp.weight (fun _ : σ => 1) α) l
  rw [coefficients_directionalDerivative]
  apply (markedLieSpan v w marked d (k + 1 + Finsupp.weight (fun _ : σ => 1) α) l).sum_mem
  intro i _
  have he : k + Finsupp.weight (fun _ : σ => 1) (α + Finsupp.single i 1) =
      k + 1 + Finsupp.weight (fun _ : σ => 1) α := by
    rw [map_add, Finsupp.weight_single, one_smul]
    omega
  have hi := hp (α + Finsupp.single i 1)
  rw [he] at hi
  exact (markedLieSpan v w marked _ _ _).smul_mem _
    ((markedLieSpan v w marked _ _ _).smul_mem _ hi)

noncomputable def markedPolynomialAlgebra (v : I → L) (w : I → ℕ) (marked : I → Bool) :
    LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { markedPolynomialLayer (σ := σ) v w marked 0 0 0 with
    lie_mem' := by
      intro p q hp hq
      change ⁅p, q⁆ ∈ markedPolynomialLayer v w marked 0 0 0
      exact markedPolynomialLayer_lie_mem v w marked
        (d := 0) (e := 0) (k := 0) (m := 0) (l := 0) (n := 0) hp hq }

theorem markedPolynomialAlgebra_le_adapted {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) :
    markedPolynomialAlgebra (σ := σ) v w marked ≤ F.associatedDegree.adaptedLieSubalgebra (fun _ => 1) := by
  intro p hp α
  have ha := hp α
  rw [Nat.zero_add] at ha
  exact markedLieSpan_le_markedDegree F v w marked hw hv 0 _ 0 ha

theorem markedPolynomialLayer_terminal {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked d (s + 1) l = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply coefficients.injective
  ext α
  have h := markedLieSpan_antitone v w marked le_rfl
    (Nat.le_add_right (s + 1) _) le_rfl (hp α)
  simpa only [markedLieSpan_marked_terminal F v w marked hw hv, Submodule.mem_bot,
    map_zero, Finsupp.zero_apply] using h

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_degree_zero_eq_one (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (k l : ℕ) :
    markedLieSpan v w marked 0 k l = markedLieSpan v w marked 1 k l := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro x ⟨a, _, hk, hl, rfl⟩
    exact ⟨a, a.length_pos.trans_le (lieTree_length_le_weight w hw a), hk, hl, rfl⟩
  · exact markedLieSpan_antitone v w marked (Nat.zero_le 1) le_rfl le_rfl

theorem markedPolynomialLayer_degree_zero_eq_one (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (k l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked 0 k l = markedPolynomialLayer v w marked 1 k l := by
  ext p
  change (∀ α, coefficients p α ∈ markedLieSpan v w marked 0
    (k + Finsupp.weight (fun _ : σ => 1) α) l) ↔ _
  simp only [markedLieSpan_degree_zero_eq_one v w marked hw]
  rfl

theorem markedPolynomialLayer_degree_terminal {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (k l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked (s + 1) k l = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply coefficients.injective
  ext α
  have h := markedLieSpan_le_layer F v w marked hv (s + 1) _ l (hp α)
  rw [F.layer_eq_bot_of_past_top (Or.inl (Nat.lt_succ_self s)), Submodule.mem_bot] at h
  simpa only [map_zero, Finsupp.zero_apply] using h

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedPolynomialLayer_eval_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d k l : ℕ} {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l)
    (t : σ → ℚ) : eval t p ∈ markedLieSpan v w marked d k l := by
  apply (eval_mem_iff_coefficients (markedLieSpan v w marked d k l) p).mpr _ t
  intro α
  exact markedLieSpan_antitone v w marked le_rfl (Nat.le_add_right k _) le_rfl (hp α)

theorem markedPolynomialLayer_eval_frequency_zero {A : Type*} [AddCommGroup A] [Module ℚ A]
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (η : L →ₗ[ℚ] A)
    {d k l : ℕ} (hη : markedLieSpan v w marked d k l ≤ η.ker)
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l)
    (t : σ → ℚ) : η (eval t p) = 0 :=
  hη (markedPolynomialLayer_eval_mem v w marked hp t)

theorem markedPolynomialLayer_constant (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d k l : ℕ} {x : L} (hx : x ∈ markedLieSpan v w marked d k l) :
    monomial (R := ℚ) (0 : σ →₀ ℕ) x ∈ markedPolynomialLayer v w marked d k l := by
  apply monomial_mem_markedPolynomialLayer
  simpa only [map_zero, Nat.add_zero] using hx

theorem markedPolynomialLayer_linear (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d k l : ℕ} {x : L} (hx : x ∈ markedLieSpan v w marked d (k + 1) l) (i : σ) :
    monomial (R := ℚ) (Finsupp.single i 1) x ∈ markedPolynomialLayer v w marked d k l := by
  apply monomial_mem_markedPolynomialLayer
  simpa only [Finsupp.weight_single, one_smul] using hx

noncomputable def markedAffinePolynomial [Fintype σ] (x : L) (y : σ → L) : VectorPolynomial σ ℚ L :=
  monomial 0 x + ∑ i, monomial (Finsupp.single i 1) (y i)

theorem markedAffinePolynomial_mem [Fintype σ]
    (v : I → L) (w : I → ℕ) (marked : I → Bool) {d k l : ℕ}
    {x : L} {y : σ → L} (hx : x ∈ markedLieSpan v w marked d k l)
    (hy : ∀ i, y i ∈ markedLieSpan v w marked d (k + 1) l) :
    markedAffinePolynomial x y ∈ markedPolynomialLayer v w marked d k l :=
  (markedPolynomialLayer v w marked d k l).add_mem
    (markedPolynomialLayer_constant v w marked hx)
    ((markedPolynomialLayer v w marked d k l).sum_mem
      (fun i _ => markedPolynomialLayer_linear v w marked (hy i) i))

theorem markedAffinePolynomial_eval [Fintype σ] (x : L) (y : σ → L) (t : σ → ℚ) :
    eval t (markedAffinePolynomial x y) = x + ∑ i, t i • y i := by
  classical
  simp [markedAffinePolynomial, eval_monomial]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (v : I → L) (w : I → ℕ) (marked : I → Bool)

theorem markedPolynomialLayer_translate (h : σ → ℚ) {d k l : ℕ}
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    translate h p ∈ markedPolynomialLayer v w marked d k l := by
  intro α
  rw [coefficients_translate]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    have hd := polynomialDegreeGap_translate_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 0 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    exact markedLieSpan_antitone v w marked le_rfl (by omega) le_rfl (hp β)

theorem markedPolynomialLayer_translate_sub (h : σ → ℚ) {d k l : ℕ}
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    translate h p - p ∈ markedPolynomialLayer v w marked d (k + 1) l := by
  intro α
  rw [coefficients_translate_sub]
  apply Submodule.sum_mem
  intro β _
  by_cases hc :
      (polynomialTranslate h (MvPolynomial.monomial β 1) - MvPolynomial.monomial β 1).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    have hd := polynomialDegreeGap_translate_sub_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 1 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    exact markedLieSpan_antitone v w marked le_rfl (by omega) le_rfl (hp β)

theorem markedPolynomialLayer_taylorRemainder [Fintype σ] (h : σ → ℚ) {d k l : ℕ}
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    translate h p - p - directionalDerivative h p ∈
      markedPolynomialLayer v w marked d (k + 2) l := by
  rw [← taylorRemainder_apply]
  intro α
  rw [coefficients_taylorRemainder]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (scalarTaylorRemainder h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    have hd := scalarTaylorRemainder_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 2 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    exact markedLieSpan_antitone v w marked le_rfl (by omega) le_rfl (hp β)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

noncomputable def markedParameterExponents (σ : Type*) [Fintype σ] (s : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_nat_weight_le (fun _ : σ => 1) (by simp) s).toFinset

@[simp] theorem mem_markedParameterExponents {σ : Type*} [Fintype σ] (s : ℕ) (α : σ →₀ ℕ) :
    α ∈ markedParameterExponents σ s ↔ Finsupp.weight (fun _ : σ => 1) α ≤ s := by
  classical
  simp only [markedParameterExponents, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

theorem markedParameterExponents_card_le (σ : Type*) [Fintype σ] (s : ℕ) :
    (markedParameterExponents σ s).card ≤ (Fintype.card σ + 1) ^ s := by
  apply boundedExponentSet_card_le
  intro α hα
  have h := (mem_markedParameterExponents s α).mp hα
  simpa only [Finsupp.weight_apply, smul_eq_mul, mul_one] using h

variable {I σ L : Type*} [Fintype I] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def finiteMarkedPolynomialValues (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) : Finset (VectorPolynomial σ ℚ L) := by
  classical
  exact (markedParameterExponents σ s).biUnion (fun α =>
    (finiteMarkedLieValues v w marked s d (k + Finsupp.weight (fun _ : σ => 1) α) l).image
      (monomial (R := ℚ) α))

theorem finiteMarkedPolynomialValues_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ finiteMarkedPolynomialValues v w marked s d k l) :
    p ∈ markedPolynomialLayer v w marked d k l := by
  classical
  obtain ⟨α, _, hα⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hα
  exact monomial_mem_markedPolynomialLayer v w marked d k l α
    (finiteMarkedLieValues_mem v w marked s d _ l hx)

omit [Fintype I] [Fintype σ] in
theorem markedPolynomialLayer_degreeLE {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) {d k l : ℕ} {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ markedPolynomialLayer v w marked d k l) : DegreeLE (fun _ : σ => 1) s p := by
  intro α hα
  have hm := markedLieSpan_antitone v w marked le_rfl
    (by omega : s + 1 ≤ k + Finsupp.weight (fun _ : σ => 1) α) le_rfl (hp α)
  simpa only [markedLieSpan_marked_terminal F v w marked hw hv, Submodule.mem_bot] using hm

theorem monomial_mem_span_finiteMarkedPolynomialValues {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
    (d k l : ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight (fun _ : σ => 1) α ≤ s)
    {x : L} (hx : x ∈ markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l) :
    monomial (R := ℚ) α x ∈
      Submodule.span ℚ (finiteMarkedPolynomialValues (σ := σ) v w marked s d k l : Set (VectorPolynomial σ ℚ L)) := by
  classical
  rw [markedLieSpan_eq_finite_span F v w marked hw hv] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact Submodule.subset_span (Finset.mem_biUnion.mpr
      ⟨α, (mem_markedParameterExponents s α).mpr hα, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩)
  | zero => simp only [monomial, TensorProduct.tmul_zero, Submodule.zero_mem]
  | add y z _ _ hy hz =>
    simpa only [monomial, TensorProduct.tmul_add] using Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    simpa only [monomial, TensorProduct.tmul_smul] using Submodule.smul_mem _ c hy

theorem markedPolynomialLayer_eq_finite_span {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked d k l =
      Submodule.span ℚ (finiteMarkedPolynomialValues (σ := σ) v w marked s d k l : Set (VectorPolynomial σ ℚ L)) := by
  classical
  apply le_antisymm
  · intro p hp
    have hdeg := (degreeLE_iff (fun _ : σ => 1) s p).mp
      (markedPolynomialLayer_degreeLE F v w marked hw hv hp)
    rw [← sum_monomial_coefficients p]
    simp only [Finsupp.sum]
    apply Submodule.sum_mem
    intro α hα
    exact monomial_mem_span_finiteMarkedPolynomialValues F v w marked hw hv d k l α
      (hdeg α hα) (hp α)
  · exact Submodule.span_le.mpr
      (fun _ hp => finiteMarkedPolynomialValues_mem v w marked s d k l hp)

theorem finiteMarkedPolynomialValues_card_le (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) :
    (finiteMarkedPolynomialValues (σ := σ) v w marked s d k l).card ≤
      (Fintype.card σ + 1) ^ s * (Fintype.card I + 2) ^ (3 ^ s) := by
  classical
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _α ∈ markedParameterExponents σ s, (Fintype.card I + 2) ^ (3 ^ s) := by
      apply Finset.sum_le_sum
      intro α _
      exact Finset.card_image_le.trans (finiteMarkedLieValues_card_le v w marked s d _ l)
    _ = (markedParameterExponents σ s).card * (Fintype.card I + 2) ^ (3 ^ s) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (markedParameterExponents_card_le σ s)

end Erdos3

end

end OAI
