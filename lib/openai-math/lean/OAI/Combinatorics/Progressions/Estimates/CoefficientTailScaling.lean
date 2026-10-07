import OAI.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialPerturbation
import OAI.Combinatorics.Progressions.Probability.BooleanJetMassBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D K Z α : Type*} [Fintype α] [DecidableEq α]
  {B O T : D → Type*} [∀ d, Fintype (B d)]

noncomputable def jointCoefficientTail (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) (o : Σ d, O d) :
    MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ :=
  normalizedCoefficientTail (terms o.1) (weight o.1) (exponent o.1) (coefficientIndex o.1)
    inputIndex (sets o.1 o.2)

noncomputable def coefficientArraySampler (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (T d))
    (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) : ℝ :=
  jointBooleanSampler h c sets x o + t * normalizedCoefficientTailValue
    (terms o.1) (weight o.1) (exponent o.1) (coefficientIndex o.1) inputIndex z x (sets o.1 o.2)

theorem coefficientArraySampler_polynomial [Fintype D] [Fintype Z] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) (t : ℝ) (z : Z → ℝ) :
    coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t z =
      parameterPolynomialMap (jointBooleanPerturbedPolynomial h c sets
        (jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex)) t z := by
  funext x o
  symm
  change MvPolynomial.eval _ _ = _
  rw [jointBooleanPerturbedPolynomial_eval]
  unfold jointCoefficientTail
  rw [normalizedCoefficientTail_eval]
  rfl

theorem coefficientArraySampler_zero (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (T d))
    (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) (z : Z → ℝ) :
    coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex 0 z =
      jointBooleanSampler h c sets := by
  funext x o
  simp only [coefficientArraySampler, zero_mul, add_zero]

omit [∀ d, Fintype (B d)] in
theorem jointCoefficientTail_degree (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) {H : ℕ}
    (hdegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ H) (o : Σ d, O d) :
    (jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex o).totalDegree ≤ H + 1 :=
  normalizedCoefficientTail_totalDegree_le _ _ _ _ _ _ (hdegree o.1)

omit [∀ d, Fintype (B d)] in
theorem jointCoefficientTail_mass (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) {H : ℕ}
    (hdegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ H)
    {W : ℝ} (hW : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ W) (o : Σ d, O d) :
    realPolynomialMass (jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex o) ≤
      booleanJetMassBudget (Fintype.card α) H W :=
  (normalizedCoefficientTail_mass_le _ _ _ _ _ _ (hdegree o.1)).trans
    (booleanJetMassBudget_bound _ le_rfl (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (hW o.1))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem coefficientArraySampler_polynomial_bounds
    {D K Z α : Type*} [Fintype α] [DecidableEq α]
    {B O T : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {H : ℕ} (hh : ∀ d, h d ≤ H)
    (hdegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ H)
    {C W : ℝ} (hc : ∀ d, (∑ b, |c d b|) ≤ C) (hw : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ W) :
    let p := jointBooleanPerturbedPolynomial h c sets
      (jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex)
    (∀ o i, (p o).degreeOf i ≤ H + 2) ∧
      (∀ o m, |(p o).coeff m| ≤
        booleanJetMassBudget (Fintype.card α) H C + booleanJetMassBudget (Fintype.card α) H W) := by
  have hrdeg := jointCoefficientTail_degree h sets terms weight exponent coefficientIndex inputIndex hdegree
  have hrmass := jointCoefficientTail_mass h sets terms weight exponent coefficientIndex inputIndex hdegree hw
  have hc' (o : Σ d, O d) := booleanJetMassBudget_bound (sets o.1 o.2) (hh o.1)
    (Finset.sum_nonneg (fun b (_ : b ∈ (Finset.univ : Finset (B o.1))) => abs_nonneg (c o.1 b))) (hc o.1)
  have he := jointBooleanPerturbedPolynomial_bounds h c sets _ hh hrdeg hc' hrmass
  have hmax : max H (1 + (H + 1)) = H + 2 := by omega
  simpa only [hmax] using he

theorem coefficientArraySampler_c2_error
    {D K Z α : Type*} [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z]
    [Fintype α] [DecidableEq α] {B O T : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {H : ℕ} (hh : ∀ d, h d ≤ H)
    (hdegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ H)
    {C W : ℝ} (hC0 : 0 ≤ C) (hW0 : 0 ≤ W)
    (hc : ∀ d, (∑ b, |c d b|) ≤ C) (hw : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ W)
    {t : ℝ} (ht : |t| ≤ 1) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (x : JointBlockParameter B h α → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let V := coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t z
    let U := jointBooleanSampler h c sets
    let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
      (H + 2) (booleanJetMassBudget (Fintype.card α) H C + booleanJetMassBudget (Fintype.card α) H W)
    ‖V x - U x‖ ≤ |t| * M ∧
      ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ |t| * M := by
  let r := jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex
  have hrdeg : ∀ o, (r o).totalDegree ≤ H + 1 :=
    jointCoefficientTail_degree h sets terms weight exponent coefficientIndex inputIndex hdegree
  have hrmass : ∀ o, realPolynomialMass (r o) ≤ booleanJetMassBudget (Fintype.card α) H W :=
    jointCoefficientTail_mass h sets terms weight exponent coefficientIndex inputIndex hdegree hw
  have hc' (o : Σ d, O d) : (2 : ℝ) ^ (sets o.1 o.2).card *
      ((∑ b, |c o.1 b|) * ((Fintype.card α : ℝ) + 1) ^ h o.1) ≤
        booleanJetMassBudget (Fintype.card α) H C :=
    booleanJetMassBudget_bound _ (hh o.1) (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (hc o.1)
  have he := jointBooleanPerturbedPolynomial_c2_error h c sets r hh hrdeg
    (booleanJetMassBudget_nonneg _ _ hC0) (booleanJetMassBudget_nonneg _ _ hW0)
    hc' hrmass ht z hz x hx
  have hmax : max H (1 + (H + 1)) = H + 2 := by omega
  dsimp only [r] at he
  rw [hmax, ← coefficientArraySampler_polynomial] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem normalizedCoefficientTailValue_scale_weight
    {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I)
    (a : ℝ) (z : Z → ℝ) (x : I → ℝ) (s : Finset α) :
    normalizedCoefficientTailValue terms (fun n => a * weight n) exponent coefficientIndex inputIndex z x s =
      a * normalizedCoefficientTailValue terms weight exponent coefficientIndex inputIndex z x s := by
  unfold normalizedCoefficientTailValue
  rw [← booleanCoefficient_const_mul]
  congr 1
  funext v
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem coefficientArraySampler_scale_weight
    {D K Z α : Type*} [Fintype α] [DecidableEq α]
    {B O T : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ)
    (exponent : ∀ d, T d → K →₀ ℕ) (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    (a t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) :
    coefficientArraySampler h c sets terms (fun d n => a * weight d n) exponent
        coefficientIndex inputIndex t z x =
      coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex (t * a) z x := by
  funext o
  simp only [coefficientArraySampler, normalizedCoefficientTailValue_scale_weight, mul_assoc]

theorem coefficientTailWeightSum_scale_le {T : Type*}
    (terms : Finset T) (weight : T → ℝ) {a W : ℝ}
    (ha : |a| ≤ 1) (hW : (∑ n ∈ terms, |weight n|) ≤ W) :
    (∑ n ∈ terms, |a * weight n|) ≤ W := by
  apply le_trans (Finset.sum_le_sum (fun n _ => ?_)) hW
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans_eq (one_mul _)

end Erdos3

end

end OAI
