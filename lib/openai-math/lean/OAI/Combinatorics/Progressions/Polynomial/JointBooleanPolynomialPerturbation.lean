import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.Combinatorics.Progressions.Estimates.FactoredC2Difference
import OAI.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple

namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {Z I O : Type*} [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

theorem parameterPolynomialMap_c2_bounds
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) {t : ℝ} (ht : |t| ≤ 1)
    (z : Z → ℝ) (hz : ∀ i, |z i| ≤ 1) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let N := Fintype.card (PolynomialParameter Z I)
    ‖parameterPolynomialMap p t z x‖ ≤ (d + 1 : ℝ) ^ N * C ∧
      ‖fderiv ℝ (parameterPolynomialMap p t z) x‖ ≤
        N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C)) ∧
      ‖fderiv ℝ (fderiv ℝ (parameterPolynomialMap p t z)) x‖ ≤
        N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C)))) := by
  have hb := polynomialParameterPoint_unit_box ht hz hx
  have he : parameterPolynomialMap p t z =
      fun y => polynomialVectorMap p (polynomialParameterPoint t z 0 + polynomialParameterInjection Z I y) :=
    funext (fun y => congrArg (polynomialVectorMap p) (polynomialParameterPoint_affine t z y))
  refine ⟨polynomialVectorMap_norm_bound p hd hC hc _ hb, ?_, ?_⟩
  · rw [he]
    apply affineSlice_fderiv_norm_le _ _ _ x
      ((polynomialVectorMap_contDiff p).differentiable (by norm_num) _)
      (polynomialParameterInjection_norm_le Z I)
    rw [← polynomialParameterPoint_affine]
    exact polynomialVectorMap_fderiv_bound p hd hC hc _ hb
  · rw [he]
    apply affineSlice_second_fderiv_norm_le _ ((polynomialVectorMap_contDiff p).of_le (by norm_num))
      _ _ x (polynomialParameterInjection_norm_le Z I)
    rw [← polynomialParameterPoint_affine]
    exact polynomialVectorMap_second_fderiv_bound p hd hC hc _ hb

theorem parameterPolynomialMap_perturbation_bounds
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) {t : ℝ} (ht : |t| ≤ 1)
    (z : Z → ℝ) (hz : ∀ i, |z i| ≤ 1) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let N := Fintype.card (PolynomialParameter Z I)
    ‖parameterPolynomialMap p t z x - parameterPolynomialMap p 0 z x‖ ≤
      |t| * ((d + 1 : ℝ) ^ N * C) ∧
      ‖fderiv ℝ (parameterPolynomialMap p t z) x - fderiv ℝ (parameterPolynomialMap p 0 z) x‖ ≤
        |t| * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C))) ∧
      ‖fderiv ℝ (fderiv ℝ (parameterPolynomialMap p t z)) x -
          fderiv ℝ (fderiv ℝ (parameterPolynomialMap p 0 z)) x‖ ≤
        |t| * (N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C))))) := by
  let q := fun o => (p o).divMonomial (Finsupp.single none 1)
  have hq := parameterPolynomialMap_c2_bounds q
    (fun o i => mvPolynomial_div_single_degreeOf_le (p o) none i (hd o i)) hC
    (fun o m => mvPolynomial_div_single_coeff_bound (p o) none (hc o) m) ht z hz x hx
  exact factoredDifference_c2_bounds (parameterPolynomialMap p t z) (parameterPolynomialMap p 0 z)
    (parameterPolynomialMap q t z) t
    ((parameterPolynomialMap_contDiff p t z).of_le (by norm_num))
    ((parameterPolynomialMap_contDiff p 0 z).of_le (by norm_num))
    ((parameterPolynomialMap_contDiff q t z).of_le (by norm_num))
    (parameterPolynomialMap_sub_zero p t z) x hq.1 hq.2.1 hq.2.2

end Erdos3

end

section

namespace Erdos3

noncomputable def scalePerturbedPolynomial {Z I : Type*}
    (p : MvPolynomial I ℝ) (r : MvPolynomial (PolynomialParameter Z I) ℝ) :
    MvPolynomial (PolynomialParameter Z I) ℝ :=
  MvPolynomial.rename (fun i => some (Sum.inr i)) p + MvPolynomial.X none * r

theorem scalePerturbedPolynomial_eval {Z I : Type*}
    (p : MvPolynomial I ℝ) (r : MvPolynomial (PolynomialParameter Z I) ℝ)
    (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    MvPolynomial.eval (polynomialParameterPoint t z x) (scalePerturbedPolynomial p r) =
      MvPolynomial.eval x p + t * MvPolynomial.eval (polynomialParameterPoint t z x) r := by
  simp only [scalePerturbedPolynomial, map_add, map_mul, MvPolynomial.eval_rename, MvPolynomial.eval_X]
  rfl

theorem scalePerturbedPolynomial_mass_le {Z I : Type*}
    (p : MvPolynomial I ℝ) (r : MvPolynomial (PolynomialParameter Z I) ℝ) :
    realPolynomialMass (scalePerturbedPolynomial p r) ≤ realPolynomialMass p + realPolynomialMass r := by
  apply (realPolynomialMass_add_le _ _).trans
  apply add_le_add (realPolynomialMass_rename_le _ _)
  exact (realPolynomialMass_mul_le _ _).trans (by simp only [realPolynomialMass_X, one_mul, le_refl])

theorem scalePerturbedPolynomial_totalDegree_le {Z I : Type*}
    (p : MvPolynomial I ℝ) (r : MvPolynomial (PolynomialParameter Z I) ℝ) :
    (scalePerturbedPolynomial p r).totalDegree ≤ max p.totalDegree (1 + r.totalDegree) := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le_max (MvPolynomial.totalDegree_rename_le _ _)
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp only [MvPolynomial.totalDegree_X, le_refl])

theorem scalePerturbedPolynomial_map_zero {Z I O : Type*} [Fintype Z] [Fintype I] [Fintype O]
    (p : O → MvPolynomial I ℝ) (r : O → MvPolynomial (PolynomialParameter Z I) ℝ)
    (z : Z → ℝ) :
    parameterPolynomialMap (fun o => scalePerturbedPolynomial (p o) (r o)) 0 z = polynomialVectorMap p := by
  funext x
  funext o
  change MvPolynomial.eval _ _ = MvPolynomial.eval _ _
  rw [scalePerturbedPolynomial_eval, zero_mul, add_zero]

end Erdos3

end

section

namespace Erdos3

noncomputable def polynomialC2BoxBudget (N d : ℕ) (C : ℝ) : ℝ :=
  (1 + (N : ℝ) * d) ^ 2 * (d + 1 : ℝ) ^ N * C

theorem polynomialC2BoxBudget_nonneg (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ polynomialC2BoxBudget N d C := by unfold polynomialC2BoxBudget; positivity

theorem polynomialC2BoxBudget_dominates (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    (d + 1 : ℝ) ^ N * C ≤ polynomialC2BoxBudget N d C ∧
      N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C)) ≤ polynomialC2BoxBudget N d C ∧
      N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C)))) ≤ polynomialC2BoxBudget N d C := by
  let x : ℝ := (N : ℝ) * d
  let a : ℝ := (d + 1 : ℝ) ^ N * C
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h0 : 1 ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have h1 : x ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have h2 : x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
  have hb : polynomialC2BoxBudget N d C = (1 + x) ^ 2 * a := by dsimp [polynomialC2BoxBudget, x, a]; ring
  rw [hb]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right h0 ha
  · have he : N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * C)) = x * a := by dsimp [x, a]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right h1 ha
  · have he : N * (N * ((d + 1 : ℝ) ^ N * ((d : ℝ) * ((d : ℝ) * C)))) = x ^ 2 * a := by
      dsimp [x, a]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right h2 ha

theorem parameterPolynomialMap_uniform_c2_error
    {Z I O : Type*} [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) {t : ℝ} (ht : |t| ≤ 1)
    (z : Z → ℝ) (hz : ∀ i, |z i| ≤ 1) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z I)) d C
    ‖parameterPolynomialMap p t z x - parameterPolynomialMap p 0 z x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (parameterPolynomialMap p t z) x - fderiv ℝ (parameterPolynomialMap p 0 z) x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (fderiv ℝ (parameterPolynomialMap p t z)) x -
        fderiv ℝ (fderiv ℝ (parameterPolynomialMap p 0 z)) x‖ ≤ |t| * M := by
  have h := parameterPolynomialMap_perturbation_bounds p hd hC hc ht z hz x hx
  have hb := polynomialC2BoxBudget_dominates (Fintype.card (PolynomialParameter Z I)) d hC
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_left hb.1 (abs_nonneg t)),
    h.2.1.trans (mul_le_mul_of_nonneg_left hb.2.1 (abs_nonneg t)),
    h.2.2.trans (mul_le_mul_of_nonneg_left hb.2.2 (abs_nonneg t))⟩

end Erdos3

end

section

namespace Erdos3

theorem polynomialC2BoxBudget_le_exp (N d : ℕ) {C p : ℝ} (hC : 0 ≤ C) (hCp : C ≤ Real.exp p) :
    polynomialC2BoxBudget N d C ≤ Real.exp (3 * (N : ℝ) * d + p) := by
  have hbase : 1 + (N : ℝ) * d ≤ Real.exp ((N : ℝ) * d) := by
    simpa only [add_comm] using Real.add_one_le_exp ((N : ℝ) * d)
  have hdegree : (d + 1 : ℝ) ≤ Real.exp (d : ℝ) := Real.add_one_le_exp _
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + (N : ℝ) * d) hbase 2
  have hterms := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (d + 1 : ℝ)) hdegree N
  calc
    _ ≤ (Real.exp ((N : ℝ) * d)) ^ 2 * (Real.exp (d : ℝ)) ^ N * Real.exp p :=
      mul_le_mul (mul_le_mul hpow hterms (by positivity) (by positivity)) hCp hC (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      norm_num
      ring

theorem polynomialC2BoxBudget_log_le (N d : ℕ) {C p : ℝ} (hC : 0 < C) (hCp : C ≤ Real.exp p) :
    Real.log (polynomialC2BoxBudget N d C) ≤ 3 * (N : ℝ) * d + p := by
  have hpos : 0 < polynomialC2BoxBudget N d C := by unfold polynomialC2BoxBudget; positivity
  exact (Real.log_le_log hpos (polynomialC2BoxBudget_le_exp N d hC.le hCp)).trans_eq (Real.log_exp _)

end Erdos3

end

section

namespace Erdos3

theorem centeredPolynomialC2Budget_le_exp (N d : ℕ) {A B a b : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAe : A + 1 ≤ Real.exp a) (hBe : B ≤ Real.exp b) :
    polynomialC2BoxBudget N (d * 2) (B * (A + 1) ^ d) ≤
      Real.exp (6 * (N : ℝ) * d + b + d * a) := by
  have hc : B * (A + 1) ^ d ≤ Real.exp (b + d * a) := by
    calc
      _ ≤ Real.exp b * Real.exp a ^ d :=
        mul_le_mul hBe (pow_le_pow_left₀ (by positivity) hAe _) (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  have he := polynomialC2BoxBudget_le_exp N (d * 2) (by positivity : 0 ≤ B * (A + 1) ^ d) hc
  convert he using 1
  push_cast
  ring_nf

theorem centeredPolynomial_uniform_c2_error
    {Z I O : Type*} [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (p : O → MvPolynomial (Z ⊕ I) ℝ) (center : Z → ℝ)
    {d : ℕ} (hd : ∀ o, (p o).totalDegree ≤ d)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcenter : ∀ j, |center j| ≤ A) (hp : ∀ o, realPolynomialMass (p o) ≤ B)
    {t : ℝ} (ht : |t| ≤ 1) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let F := parameterPolynomialMap (fun o => centeredPolynomial center (p o))
    let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z I)) (d * 2)
      (B * (A + 1) ^ d)
    ‖F t z x - F 0 z x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (F t z) x - fderiv ℝ (F 0 z) x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (fderiv ℝ (F t z)) x - fderiv ℝ (fderiv ℝ (F 0 z)) x‖ ≤ |t| * M := by
  apply parameterPolynomialMap_uniform_c2_error
  · intro o i
    exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      (centeredPolynomial_totalDegree_le center (p o) (hd o))
  · positivity
  · intro o m
    exact (realPolynomialMass_coeff_le _ _).trans
      ((centeredPolynomial_mass_le center (p o) hA hcenter (hd o)).trans
        (mul_le_mul_of_nonneg_right (hp o) (by positivity)))
  · exact ht
  · exact hz
  · exact hx

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)]

noncomputable def jointBooleanPolynomial (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (o : Σ d, O d) :
    MvPolynomial (JointBlockParameter B h α) ℝ :=
  MvPolynomial.rename (Sigma.mk o.1)
    (booleanSamplerPolynomial (F := Fin (h o.1)) (c o.1) (sets o.1 o.2))

theorem jointBooleanPolynomial_eval (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) :
    MvPolynomial.eval x (jointBooleanPolynomial h c sets o) = jointBooleanSampler h c sets x o := by
  rw [jointBooleanPolynomial, MvPolynomial.eval_rename]
  rfl

theorem jointBooleanPolynomial_mass_le (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (o : Σ d, O d) :
    realPolynomialMass (jointBooleanPolynomial h c sets o) ≤
      (2 : ℝ) ^ (sets o.1 o.2).card *
        ((∑ b, |c o.1 b|) * ((Fintype.card α : ℝ) + 1) ^ h o.1) := by
  apply (realPolynomialMass_rename_le _ _).trans
  simpa only [Fintype.card_fin] using
    booleanSamplerPolynomial_mass_le (F := Fin (h o.1)) (c o.1) (sets o.1 o.2)

theorem jointBooleanPolynomial_totalDegree_le (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (o : Σ d, O d) :
    (jointBooleanPolynomial h c sets o).totalDegree ≤ h o.1 := by
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  simpa only [Fintype.card_fin] using
    booleanSamplerPolynomial_totalDegree_le (F := Fin (h o.1)) (c o.1) (sets o.1 o.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α Z : Type*} [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)]

noncomputable def jointBooleanPerturbedPolynomial (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    (o : Σ d, O d) : MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ :=
  scalePerturbedPolynomial (jointBooleanPolynomial h c sets o) (r o)

theorem jointBooleanPerturbedPolynomial_eval (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) :
    MvPolynomial.eval (polynomialParameterPoint t z x) (jointBooleanPerturbedPolynomial h c sets r o) =
      jointBooleanSampler h c sets x o + t * MvPolynomial.eval (polynomialParameterPoint t z x) (r o) := by
  rw [jointBooleanPerturbedPolynomial, scalePerturbedPolynomial_eval, jointBooleanPolynomial_eval]

theorem jointBooleanPerturbedPolynomial_zero [Fintype D] [Fintype Z] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    (z : Z → ℝ) :
    parameterPolynomialMap (jointBooleanPerturbedPolynomial h c sets r) 0 z = jointBooleanSampler h c sets := by
  funext x o
  change MvPolynomial.eval _ _ = _
  rw [jointBooleanPerturbedPolynomial_eval, zero_mul, add_zero]

theorem jointBooleanPerturbedPolynomial_bounds
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    {H e : ℕ} (hh : ∀ d, h d ≤ H) (hrdeg : ∀ o, (r o).totalDegree ≤ e)
    {C R : ℝ}
    (hC : ∀ o : Σ d, O d, (2 : ℝ) ^ (sets o.1 o.2).card *
      ((∑ b, |c o.1 b|) * ((Fintype.card α : ℝ) + 1) ^ h o.1) ≤ C)
    (hrmass : ∀ o, realPolynomialMass (r o) ≤ R) :
    (∀ o i, (jointBooleanPerturbedPolynomial h c sets r o).degreeOf i ≤ max H (1 + e)) ∧
      (∀ o m, |(jointBooleanPerturbedPolynomial h c sets r o).coeff m| ≤ C + R) := by
  constructor
  · intro o i
    apply (MvPolynomial.degreeOf_le_totalDegree _ _).trans
    apply (scalePerturbedPolynomial_totalDegree_le _ _).trans
    exact max_le_max ((jointBooleanPolynomial_totalDegree_le h c sets o).trans (hh o.1))
      (Nat.add_le_add_left (hrdeg o) 1)
  · intro o m
    apply (realPolynomialMass_coeff_le _ _).trans
    apply (scalePerturbedPolynomial_mass_le _ _).trans
    exact add_le_add ((jointBooleanPolynomial_mass_le h c sets o).trans (hC o)) (hrmass o)

theorem jointBooleanPerturbedPolynomial_c2_error
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    {H e : ℕ} (hh : ∀ d, h d ≤ H) (hrdeg : ∀ o, (r o).totalDegree ≤ e)
    {C R : ℝ} (hC0 : 0 ≤ C) (hR0 : 0 ≤ R)
    (hC : ∀ o : Σ d, O d, (2 : ℝ) ^ (sets o.1 o.2).card *
      ((∑ b, |c o.1 b|) * ((Fintype.card α : ℝ) + 1) ^ h o.1) ≤ C)
    (hrmass : ∀ o, realPolynomialMass (r o) ≤ R)
    {t : ℝ} (ht : |t| ≤ 1) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (x : JointBlockParameter B h α → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let V := parameterPolynomialMap (jointBooleanPerturbedPolynomial h c sets r) t z
    let U := jointBooleanSampler h c sets
    let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
      (max H (1 + e)) (C + R)
    ‖V x - U x‖ ≤ |t| * M ∧
      ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ |t| * M := by
  have hb := jointBooleanPerturbedPolynomial_bounds h c sets r hh hrdeg hC hrmass
  have he := parameterPolynomialMap_uniform_c2_error (jointBooleanPerturbedPolynomial h c sets r)
    hb.1 (add_nonneg hC0 hR0) hb.2 ht z hz x hx
  rw [jointBooleanPerturbedPolynomial_zero] at he
  exact he

end Erdos3

end

end OAI
