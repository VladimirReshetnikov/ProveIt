import OAI.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
import OAI.Combinatorics.Progressions.Estimates.SigmaAxisOperator
import OAI.Combinatorics.Progressions.Polynomial.MonomialArrayJet

namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

noncomputable def sigmaAxisSampler (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (x : (Σ d, I d) → ℝ) (s : Σ d, O d) : ℝ :=
  U s.1 (sigmaAxisProjection I s.1 x) s.2

theorem sigmaAxisSampler_contDiff (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (hU : ∀ d, ContDiff ℝ ∞ (U d)) : ContDiff ℝ ∞ (sigmaAxisSampler U) :=
  contDiff_pi.mpr (fun s => ((contDiff_apply ℝ ℝ s.2).comp (hU s.1)).comp
    (sigmaAxisProjection I s.1).contDiff)

theorem sigmaAxisSampler_hasFDerivAt (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x)) :
    HasFDerivAt (sigmaAxisSampler U)
      (sigmaAxisOperator (fun d => fderiv ℝ (U d) (sigmaAxisProjection I d x))) x := by
  apply hasFDerivAt_pi.mpr
  intro s
  exact (hasFDerivAt_apply s.2 _).comp x
    ((hU s.1).hasFDerivAt.comp x (sigmaAxisProjection I s.1).hasFDerivAt)

theorem sigmaAxisSampler_fderiv (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x)) :
    fderiv ℝ (sigmaAxisSampler U) x =
      sigmaAxisOperator (fun d => fderiv ℝ (U d) (sigmaAxisProjection I d x)) :=
  (sigmaAxisSampler_hasFDerivAt U x hU).fderiv

theorem sigmaAxisSampler_selectedDerivative (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (J : ∀ d, (O d → ℝ) →L[ℝ] (I d → ℝ)) (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x)) :
    selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) x =
      sigmaAxisOperator (fun d => selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)) := by
  unfold selectedDerivative
  rw [sigmaAxisSampler_fderiv U x hU, sigmaAxisOperator_comp]

theorem sigmaAxisSampler_inverse_bound (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (J : ∀ d, (O d → ℝ) →L[ℝ] (I d → ℝ)) (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x))
    (hinv : ∀ d, (selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)).IsInvertible)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ d, ‖(selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)).inverse‖ ≤ K) :
    (selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) x).IsInvertible ∧
      ‖(selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) x).inverse‖ ≤ K := by
  rw [sigmaAxisSampler_selectedDerivative U J x hU]
  exact sigmaAxisOperator_inverse_norm_le _ hinv hK hbound

theorem sigmaAxisSampler_perturbed_inverse_bound
    (U : ∀ d, (I d → ℝ) → (O d → ℝ)) (J : ∀ d, (O d → ℝ) →L[ℝ] (I d → ℝ))
    (V : ((Σ d, I d) → ℝ) → ((Σ d, O d) → ℝ)) (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x))
    (hinv : ∀ d, (selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)).IsInvertible)
    (K : ℝ≥0)
    (hbound : ∀ d, ‖(selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)).inverse‖ ≤ K)
    (hJ : ∀ d, ‖J d‖ ≤ 1)
    (hsmall : (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ (sigmaAxisSampler U) x‖ ≤ 1 / 2) :
    (selectedDerivative V (sigmaAxisOperator J) x).IsInvertible ∧
      ‖(selectedDerivative V (sigmaAxisOperator J) x).inverse‖ ≤ 2 * K := by
  obtain ⟨hi, hb⟩ := sigmaAxisSampler_inverse_bound U J x hU hinv K.coe_nonneg hbound
  apply selected_inverse_perturbation (sigmaAxisSampler U) V (sigmaAxisOperator J) x hi K hb
  have hJn := sigmaAxisOperator_norm_le J zero_le_one hJ
  have hprod := mul_le_mul_of_nonneg_left hJn (norm_nonneg (fderiv ℝ V x - fderiv ℝ (sigmaAxisSampler U) x))
  rw [mul_one] at hprod
  exact (mul_le_mul_of_nonneg_left hprod K.coe_nonneg).trans hsmall

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

abbrev JointBlockParameter {D : Type*} (B : D → Type*) (h : D → ℕ) (α : Type*) :=
  Σ d, BlockParameter (B d) (Fin (h d)) α

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

noncomputable def jointBooleanSampler (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) :
    (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ) :=
  sigmaAxisSampler (fun d => booleanSamplerMap (F := Fin (h d)) (c d) (sets d))

noncomputable def jointBooleanInjection {h : D → ℕ}
    (block : ∀ d, O d → B d) (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) :
    ((Σ d, O d) → ℝ) →L[ℝ] (JointBlockParameter B h α → ℝ) :=
  sigmaAxisOperator (fun d => booleanSelectedInjection (block d) (v d) (sel d))

omit [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] in
theorem jointBooleanSampler_contDiff (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) : ContDiff ℝ ∞ (jointBooleanSampler h c sets) :=
  sigmaAxisSampler_contDiff _ (fun d => booleanSamplerMap_contDiff (c d) (sets d))

omit [∀ d, DecidableEq (O d)] in
theorem jointBooleanInjection_norm_le {h : D → ℕ}
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) :
    ‖jointBooleanInjection block v sel‖ ≤ 1 :=
  sigmaAxisOperator_norm_le _ zero_le_one
    (fun d => booleanSelectedInjection_norm_le (block d) (hblock d) (v d) (sel d))

theorem jointBoolean_selectedDerivative_eq {h : D → ℕ} (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (x : JointBlockParameter B h α → ℝ) :
    selectedDerivative (jointBooleanSampler h c sets) (jointBooleanInjection block v sel) x =
      sigmaAxisOperator (fun d => matrixSupCLM
        ((booleanSelectedMinor (c d) (sets d) (block d) (v d) (sel d)).map
          (MvPolynomial.eval (sigmaAxisProjection (fun d => BlockParameter (B d) (Fin (h d)) α) d x)))) := by
  change selectedDerivative (sigmaAxisSampler _) (sigmaAxisOperator _) x = _
  rw [sigmaAxisSampler_selectedDerivative _ _ x
    (fun d => (booleanSamplerMap_contDiff (c d) (sets d)).differentiable (by norm_num) _)]
  congr 1
  funext d
  exact booleanSelectedDerivative_eq (c d) (sets d) (block d) (v d) (sel d) _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_coeff_abs_le {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (m : K →₀ ℕ) :
    |(monomialArrayPolynomial e a).coeff m| ≤ ∑ j, |a j| := by
  apply (realPolynomialMass_coeff_le _ m).trans
  exact (realPolynomialMass_sum_le Finset.univ (fun j => MvPolynomial.monomial (e j) (a j))).trans
    (Finset.sum_le_sum (fun j _ => (realPolynomialMass_monomial (e j) (a j)).le))

theorem jointBooleanSampler_coordinate_abs_le {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (x : JointBlockParameter B h α → ℝ) (hx : ‖x‖ ≤ 1) (o : Σ d, O d) :
    |jointBooleanSampler h c sets x o| ≤
      (2 : ℝ)^(sets o.1 o.2).card*((∑ b, |c o.1 b|)*((Fintype.card α : ℝ)+1)^h o.1) := by
  apply (mvPolynomial_eval_abs_le_sum_coeff _ _ ?_).trans
  · simpa only [Fintype.card_fin, realPolynomialMass] using
      booleanSamplerPolynomial_mass_le (F := Fin (h o.1)) (c o.1) (sets o.1 o.2)
  · intro j
    change |x ⟨o.1, j⟩| ≤ 1
    exact (Real.norm_eq_abs _).symm.trans_le ((norm_le_pi_norm x _).trans hx)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev PrincipalTupleIndex {D : Type*} (B : D → Type*) (h : D → ℕ) :=
  Σ d, B d × Fin (h d)

abbrev SamplerTupleIndex {D : Type*} (G : Type*) (B : D → Type*) (h : D → ℕ) :=
  G ⊕ PrincipalTupleIndex B h

def canonicalTupleInput {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (extra : G → Option α → Z) : SamplerTupleIndex G B h → Option α → Z ⊕ JointBlockParameter B h α
  | .inl g, r => .inl (extra g r)
  | .inr ⟨d, b, v⟩, r => .inr ⟨d, b, v, r⟩

theorem canonicalTupleInput_principal {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (extra : G → Option α → Z) (d : D) (b : B d) (v : Fin (h d)) (r : Option α) :
    canonicalTupleInput extra (.inr ⟨d, b, v⟩) r = .inr ⟨d, b, v, r⟩ := rfl

theorem samplerTupleIndex_card {D G : Type*} [Fintype D] [Fintype G]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) :
    Fintype.card (SamplerTupleIndex G B h) = Fintype.card G + ∑ d, Fintype.card (B d) * h d := by
  simp only [SamplerTupleIndex, PrincipalTupleIndex, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin]

noncomputable def normalizedCubeTuple {K Z I α : Type*} [Fintype α] [DecidableEq α]
    (input : K → Option α → Z ⊕ I) (z : Z → ℝ) (x : I → ℝ) (vertex : Finset α) (k : K) : ℝ :=
  ∑ r : Option α, (booleanFeature r vertex : ℝ) * Sum.elim z x (input k r)

theorem normalizedCubeTuple_principal {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B : D → Type*} {h : D → ℕ} (extra : G → Option α → Z)
    (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) (vertex : Finset α)
    (d : D) (b : B d) (v : Fin (h d)) :
    normalizedCubeTuple (canonicalTupleInput extra) z x vertex (.inr ⟨d, b, v⟩) =
      ∑ r : Option α, (booleanFeature r vertex : ℝ) * x ⟨d, b, v, r⟩ := rfl

end Erdos3

end

end OAI
