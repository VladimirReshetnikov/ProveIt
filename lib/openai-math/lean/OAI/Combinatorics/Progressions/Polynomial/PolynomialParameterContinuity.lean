import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.MeanValue
import OAI.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
import OAI.Combinatorics.Progressions.Geometry.OperatorCoordinateBound
import OAI.Combinatorics.Progressions.Lattices.AffineSliceC2Difference
import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse
import OAI.Combinatorics.Progressions.Polynomial.PolynomialAnalyticDerivative
import OAI.Combinatorics.Progressions.Polynomial.PolynomialValueCoefficient
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_support_card_le_fintype {I : Type*} [Fintype I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d) :
    p.support.card ≤ (d + 1) ^ Fintype.card I := by
  classical
  let f : p.support → (I → Fin (d + 1)) := fun m i =>
    ⟨m.val i, Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_iff.mp (hd i)) m.val m.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg Fin.val (congrFun hab i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem mvPolynomial_unit_box_bound {I : Type*} [Fintype I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |MvPolynomial.eval x p| ≤ (d + 1 : ℝ) ^ Fintype.card I * C := by
  have hcard : (p.support.card : ℝ) ≤ (d + 1 : ℝ) ^ Fintype.card I := by
    exact_mod_cast mvPolynomial_support_card_le_fintype p hd
  calc
    _ ≤ ∑ m ∈ p.support, |p.coeff m| := mvPolynomial_eval_abs_le_sum_coeff p x hx
    _ ≤ ∑ _m ∈ p.support, C := Finset.sum_le_sum (fun m _ => hc m)
    _ = (p.support.card : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hC

theorem mvPolynomial_pderiv_degreeOf_le {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j i : I) {d : ℕ} (hd : p.degreeOf i ≤ d) :
    (MvPolynomial.pderiv j p).degreeOf i ≤ d := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  have hc : p.coeff (m + Finsupp.single j 1) ≠ 0 := by
    intro hz
    apply MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have hb := MvPolynomial.degreeOf_le_iff.mp hd _ (MvPolynomial.mem_support_iff.mpr hc)
  have hi : m i ≤ (m + Finsupp.single j 1 : I →₀ ℕ) i := by simp only [Finsupp.add_apply]; omega
  exact hi.trans hb

theorem mvPolynomial_pderiv_coeff_bound {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j : I) {d : ℕ} (hd : p.degreeOf j ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C) (m : I →₀ ℕ) :
    |(MvPolynomial.pderiv j p).coeff m| ≤ (d : ℝ) * C := by
  rw [MvPolynomial.coeff_pderiv]
  by_cases hz : p.coeff (m + Finsupp.single j 1) = 0
  · rw [hz, zero_mul, abs_zero]
    positivity
  · have hd' := MvPolynomial.degreeOf_le_iff.mp hd _ (MvPolynomial.mem_support_iff.mpr hz)
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hd'
    have hdR : (m j + 1 : ℝ) ≤ d := by exact_mod_cast hd'
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m j + 1)]
    exact (mul_le_mul (hc _) hdR (by positivity) hC).trans_eq (mul_comm C d)

theorem mvPolynomial_pderiv_unit_box_bound {I : Type*} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) (j : I) :
    |MvPolynomial.eval x (MvPolynomial.pderiv j p)| ≤
      (d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * C) :=
  mvPolynomial_unit_box_bound _ (fun i => mvPolynomial_pderiv_degreeOf_le p j i (hd i))
    (by positivity) (mvPolynomial_pderiv_coeff_bound p j (hd j) hC hc) x hx

theorem mvPolynomial_second_pderiv_unit_box_bound {I : Type*} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) (j k : I) :
    |MvPolynomial.eval x (MvPolynomial.pderiv k (MvPolynomial.pderiv j p))| ≤
      (d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * ((d : ℝ) * C)) :=
  mvPolynomial_pderiv_unit_box_bound _ (fun i => mvPolynomial_pderiv_degreeOf_le p j i (hd i))
    (by positivity) (mvPolynomial_pderiv_coeff_bound p j (hd j) hC hc) x hx k

end Erdos3

end

section

namespace Erdos3

theorem polynomialOperator_fderiv_entry {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) (j : I) (row : O) (col : J) :
    (fderiv ℝ A x (Pi.single j 1)) (Pi.single col 1) row =
      MvPolynomial.eval x (MvPolynomial.pderiv j (p row col)) := by
  have hscalar : (fun y => A y (Pi.single col 1) row) =
      (fun y => MvPolynomial.eval y (p row col)) := funext (fun y => hentry y row col)
  have hB : DifferentiableAt ℝ (fun y => A y (Pi.single col 1)) x :=
    hA.clm_apply (differentiableAt_const _)
  have hp := mvPolynomial_fderiv_coordinate (p row col) x j
  rw [← hscalar, fderiv_apply hB row, fderiv_clm_apply hA (differentiableAt_const _)] at hp
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply] at hp
  exact hp

theorem polynomialOperator_fderiv_norm_le {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ row col j, |MvPolynomial.eval x (MvPolynomial.pderiv j (p row col))| ≤ M) :
    ‖fderiv ℝ A x‖ ≤ Fintype.card I * (Fintype.card J * M) := by
  apply clm_norm_le_card_mul_of_basis _ (mul_nonneg (Nat.cast_nonneg _) hM)
  intro j
  apply clm_norm_le_card_mul_of_entries _ hM
  intro col row
  rw [polynomialOperator_fderiv_entry A p hentry x hA j row col]
  exact hp row col j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_mod_single_support {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j : I) {m : I →₀ ℕ}
    (hm : m ∈ (p.modMonomial (Finsupp.single j 1)).support) : m j = 0 := by
  by_contra hz
  have hle : Finsupp.single j 1 ≤ m := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hz)
  exact MvPolynomial.mem_support_iff.mp hm (MvPolynomial.coeff_modMonomial_of_le p hle)

theorem mvPolynomial_eval_update_of_support_zero {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j : I) (hp : ∀ m ∈ p.support, m j = 0)
    (x : I → ℝ) (t : ℝ) : MvPolynomial.eval (Function.update x j t) p = MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = j
  · subst i
    rw [hp m hm, pow_zero, pow_zero]
  · rw [Function.update_of_ne hi]

theorem mvPolynomial_eval_sub_zero_coordinate {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j : I) (x : I → ℝ) :
    MvPolynomial.eval x p - MvPolynomial.eval (Function.update x j 0) p =
      x j * MvPolynomial.eval x (p.divMonomial (Finsupp.single j 1)) := by
  have h := congrArg (MvPolynomial.eval x) (p.divMonomial_add_modMonomial_single j)
  have h0 := congrArg (MvPolynomial.eval (Function.update x j 0))
    (p.divMonomial_add_modMonomial_single j)
  simp only [map_add, map_mul, MvPolynomial.eval_X, Function.update_self, zero_mul, zero_add] at h h0
  rw [mvPolynomial_eval_update_of_support_zero _ j
    (fun m hm => mvPolynomial_mod_single_support p j hm) x 0] at h0
  linarith

theorem mvPolynomial_div_single_degreeOf_le {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j i : I) {d : ℕ} (hd : p.degreeOf i ≤ d) :
    (p.divMonomial (Finsupp.single j 1)).degreeOf i ≤ d := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  have hc : p.coeff (Finsupp.single j 1 + m) ≠ 0 := by
    simpa only [MvPolynomial.coeff_divMonomial] using MvPolynomial.mem_support_iff.mp hm
  have hb := MvPolynomial.degreeOf_le_iff.mp hd _ (MvPolynomial.mem_support_iff.mpr hc)
  have hi : m i ≤ (Finsupp.single j 1 + m : I →₀ ℕ) i := by simp only [Finsupp.add_apply]; omega
  exact hi.trans hb

theorem mvPolynomial_div_single_coeff_bound {I : Type*}
    (p : MvPolynomial I ℝ) (j : I) {C : ℝ} (hc : ∀ m, |p.coeff m| ≤ C) (m : I →₀ ℕ) :
    |(p.divMonomial (Finsupp.single j 1)).coeff m| ≤ C := by
  rw [MvPolynomial.coeff_divMonomial]
  exact hc _

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

noncomputable def polynomialVectorMap (p : O → MvPolynomial I ℝ) (x : I → ℝ) (o : O) : ℝ :=
  MvPolynomial.eval x (p o)

omit [DecidableEq I] in
theorem polynomialVectorMap_contDiff (p : O → MvPolynomial I ℝ) :
    ContDiff ℝ ∞ (polynomialVectorMap p) := contDiff_pi.mpr (fun o => mvPolynomial_contDiff_eval (p o))

theorem polynomialVectorMap_fderiv_entry (p : O → MvPolynomial I ℝ) (x : I → ℝ) (i : I) (o : O) :
    fderiv ℝ (polynomialVectorMap p) x (Pi.single i 1) o =
      MvPolynomial.eval x (MvPolynomial.pderiv i (p o)) := by
  have hd := (polynomialVectorMap_contDiff p).differentiable (by norm_num) x
  have he := mvPolynomial_fderiv_coordinate (p o) x i
  change fderiv ℝ (fun y => polynomialVectorMap p y o) x (Pi.single i 1) = _ at he
  rw [fderiv_apply hd o] at he
  exact he

omit [DecidableEq I] in
theorem polynomialVectorMap_norm_bound (p : O → MvPolynomial I ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖polynomialVectorMap p x‖ ≤ (d + 1 : ℝ) ^ Fintype.card I * C := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro o
  exact mvPolynomial_unit_box_bound (p o) (hd o) hC (hc o) x hx

theorem polynomialVectorMap_fderiv_bound (p : O → MvPolynomial I ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖fderiv ℝ (polynomialVectorMap p) x‖ ≤
      Fintype.card I * ((d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * C)) := by
  apply clm_norm_le_card_mul_of_entries _ (by positivity)
  intro i o
  rw [polynomialVectorMap_fderiv_entry]
  exact mvPolynomial_pderiv_unit_box_bound (p o) (hd o) hC (hc o) x hx i

theorem polynomialVectorMap_second_fderiv_bound [DecidableEq O]
    (p : O → MvPolynomial I ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (polynomialVectorMap p)) x‖ ≤
      Fintype.card I * (Fintype.card I *
        ((d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * ((d : ℝ) * C)))) := by
  have hs : ContDiff ℝ 2 (polynomialVectorMap p) := (polynomialVectorMap_contDiff p).of_le (by norm_num)
  have hs' : ContDiff ℝ 1 (fderiv ℝ (polynomialVectorMap p)) := hs.fderiv_right (by norm_num)
  have hA := hs'.differentiable one_ne_zero x
  exact polynomialOperator_fderiv_norm_le _ (fun o i => MvPolynomial.pderiv i (p o))
    (fun y o i => polynomialVectorMap_fderiv_entry p y i o) x hA (by positivity)
    (fun o i j => mvPolynomial_second_pderiv_unit_box_bound (p o) (hd o) hC (hc o) x hx i j)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def polynomialBoxLip (n d : ℕ) (C : ℝ≥0) : ℝ≥0 :=
  n * ((d+1 : ℝ≥0)^n * (d*C))

theorem polynomialVectorMap_lipschitzOn_box {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (p : O → MvPolynomial I ℝ) {d : ℕ} (hd : ∀ o, (p o).totalDegree ≤ d)
    (C : ℝ≥0) (hc : ∀ o, realPolynomialMass (p o) ≤ C) :
    LipschitzOnWith (polynomialBoxLip (Fintype.card I) d C) (polynomialVectorMap p)
      (Metric.closedBall 0 1) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (polynomialVectorMap_contDiff p).differentiable (by norm_num) x) _ (convex_closedBall 0 1)
  intro x hx
  have hx' : ∀ i, |x i| ≤ 1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    intro i
    exact (norm_le_pi_norm x i).trans hx
  have he := polynomialVectorMap_fderiv_bound p
    (fun o i => (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hd o)) C.coe_nonneg
    (fun o m => (realPolynomialMass_coeff_le (p o) m).trans (hc o)) x hx'
  change ‖fderiv ℝ (polynomialVectorMap p) x‖ ≤ (polynomialBoxLip (Fintype.card I) d C : ℝ)
  simpa only [polynomialBoxLip, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
    NNReal.coe_add, NNReal.coe_one] using he

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

abbrev PolynomialParameter (Z I : Type*) := Option (Z ⊕ I)

def polynomialParameterPoint {Z I : Type*} (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    PolynomialParameter Z I → ℝ := fun s => match s with
  | none => t
  | some (.inl j) => z j
  | some (.inr i) => x i

noncomputable def polynomialParameterInjection (Z I : Type*) [Fintype I] :
    (I → ℝ) →L[ℝ] (PolynomialParameter Z I → ℝ) :=
  ContinuousLinearMap.pi (fun s => match s with
    | none => 0
    | some (.inl _) => 0
    | some (.inr i) => ContinuousLinearMap.proj i)

theorem polynomialParameterPoint_affine {Z I : Type*} [Fintype I]
    (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    polynomialParameterPoint t z x = polynomialParameterPoint t z 0 + polynomialParameterInjection Z I x := by
  ext s
  rcases s with _ | (j | i) <;> simp [polynomialParameterPoint, polynomialParameterInjection]

theorem polynomialParameterInjection_norm_le (Z I : Type*) [Fintype Z] [Fintype I] :
    ‖polynomialParameterInjection Z I‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro s
  rcases s with _ | (j | i)
  · simp [polynomialParameterInjection]
  · simp [polynomialParameterInjection]
  · simpa [polynomialParameterInjection] using norm_le_pi_norm x i

theorem polynomialParameterPoint_unit_box {Z I : Type*} {t : ℝ} (ht : |t| ≤ 1)
    {z : Z → ℝ} (hz : ∀ i, |z i| ≤ 1) {x : I → ℝ} (hx : ∀ i, |x i| ≤ 1)
    (s : PolynomialParameter Z I) : |polynomialParameterPoint t z x s| ≤ 1 := by
  rcases s with _ | (j | i)
  · exact ht
  · exact hz j
  · exact hx i

noncomputable def parameterPolynomialMap {Z I O : Type*} [Fintype Z] [Fintype I] [Fintype O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) (t : ℝ) (z : Z → ℝ) (x : I → ℝ) : O → ℝ :=
  polynomialVectorMap p (polynomialParameterPoint t z x)

theorem parameterPolynomialMap_contDiff {Z I O : Type*} [Fintype Z] [Fintype I] [Fintype O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) (t : ℝ) (z : Z → ℝ) :
    ContDiff ℝ ∞ (parameterPolynomialMap p t z) := by
  have he : parameterPolynomialMap p t z =
      fun x => polynomialVectorMap p (polynomialParameterPoint t z 0 + polynomialParameterInjection Z I x) :=
    funext (fun x => congrArg (polynomialVectorMap p) (polynomialParameterPoint_affine t z x))
  rw [he]
  exact (polynomialVectorMap_contDiff p).comp (contDiff_const.add (polynomialParameterInjection Z I).contDiff)

theorem parameterPolynomialMap_sub_zero {Z I O : Type*} [Fintype Z] [DecidableEq Z]
    [Fintype I] [DecidableEq I] [Fintype O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    parameterPolynomialMap p t z x - parameterPolynomialMap p 0 z x =
      t • parameterPolynomialMap (fun o => (p o).divMonomial (Finsupp.single none 1)) t z x := by
  ext o
  have he : Function.update (polynomialParameterPoint t z x) none 0 = polynomialParameterPoint 0 z x := by
    funext s
    rcases s with _ | (j | i) <;> simp [polynomialParameterPoint]
  have ht := mvPolynomial_eval_sub_zero_coordinate (p o) none (polynomialParameterPoint t z x)
  rw [he] at ht
  exact ht

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators ContDiff

theorem realPolynomialMass_pderiv_degreeOf {I : Type*} (p : MvPolynomial I ℝ)
    (i : I) {d : ℕ} (hd : p.degreeOf i ≤ d) :
    realPolynomialMass (pderiv i p) ≤ (d : ℝ) * realPolynomialMass p := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff, map_sum]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ p.support, (d : ℝ) * |p.coeff m| := by
      apply Finset.sum_le_sum
      intro m hm
      rw [pderiv_monomial, realPolynomialMass_monomial, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (m i : ℝ) from Nat.cast_nonneg _)]
      have hmi : (m i : ℝ) ≤ d := by exact_mod_cast (monomial_le_degreeOf i hm).trans hd
      nlinarith [abs_nonneg (p.coeff m)]
    _ = _ := by rw [realPolynomialMass, Finset.mul_sum]

theorem polynomialVectorMap_mass_c2_bounds {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (p : O → MvPolynomial I ℝ) {d : ℕ} (hd : ∀ o i, (p o).degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hmass : ∀ o, realPolynomialMass (p o) ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖polynomialVectorMap p x‖ ≤ C ∧
      ‖fderiv ℝ (polynomialVectorMap p) x‖ ≤ Fintype.card I * ((d : ℝ) * C) ∧
      ‖fderiv ℝ (fderiv ℝ (polynomialVectorMap p)) x‖ ≤
        Fintype.card I * (Fintype.card I * ((d : ℝ) * ((d : ℝ) * C))) := by
  have hfirst (o : O) (i : I) : realPolynomialMass (pderiv i (p o)) ≤ (d : ℝ) * C :=
    (realPolynomialMass_pderiv_degreeOf (p o) i (hd o i)).trans
      (mul_le_mul_of_nonneg_left (hmass o) (Nat.cast_nonneg _))
  have hsecond (o : O) (i j : I) :
      realPolynomialMass (pderiv j (pderiv i (p o))) ≤ (d : ℝ) * ((d : ℝ) * C) :=
    (realPolynomialMass_pderiv_degreeOf (pderiv i (p o)) j
      (mvPolynomial_pderiv_degreeOf_le (p o) i j (hd o j))).trans
      (mul_le_mul_of_nonneg_left (hfirst o i) (Nat.cast_nonneg _))
  refine ⟨?_, ?_, ?_⟩
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro o
    exact (mvPolynomial_eval_abs_le_sum_coeff (p o) x hx).trans (hmass o)
  · apply clm_norm_le_card_mul_of_entries _ (mul_nonneg (Nat.cast_nonneg _) hC)
    intro i o
    rw [polynomialVectorMap_fderiv_entry]
    exact (mvPolynomial_eval_abs_le_sum_coeff (pderiv i (p o)) x hx).trans (hfirst o i)
  · have hs : ContDiff ℝ 2 (polynomialVectorMap p) :=
      (polynomialVectorMap_contDiff p).of_le (by norm_num)
    have hs' : ContDiff ℝ 1 (fderiv ℝ (polynomialVectorMap p)) := hs.fderiv_right (by norm_num)
    exact polynomialOperator_fderiv_norm_le _ (fun o i => pderiv i (p o))
      (fun y o i => polynomialVectorMap_fderiv_entry p y i o) x (hs'.differentiable one_ne_zero x)
      (by positivity) (fun o i j =>
        (mvPolynomial_eval_abs_le_sum_coeff (pderiv j (pderiv i (p o))) x hx).trans (hsecond o i j))

noncomputable def polynomialMassC2Budget (N d : ℕ) (C : ℝ) : ℝ :=
  (1 + (N : ℝ) * d) ^ 2 * C

theorem polynomialMassC2Budget_nonneg (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ polynomialMassC2Budget N d C := by unfold polynomialMassC2Budget; positivity

theorem polynomialMassC2Budget_dominates (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    C ≤ polynomialMassC2Budget N d C ∧
      N * ((d : ℝ) * C) ≤ polynomialMassC2Budget N d C ∧
      N * (N * ((d : ℝ) * ((d : ℝ) * C))) ≤ polynomialMassC2Budget N d C := by
  have hx : 0 ≤ (N : ℝ) * d := by positivity
  have h0 : 1 ≤ (1 + (N : ℝ) * d)^2 := by nlinarith [sq_nonneg ((N : ℝ) * d)]
  have h1 : (N : ℝ) * d ≤ (1 + (N : ℝ) * d)^2 := by nlinarith [sq_nonneg ((N : ℝ) * d)]
  have h2 : ((N : ℝ) * d)^2 ≤ (1 + (N : ℝ) * d)^2 := by nlinarith
  unfold polynomialMassC2Budget
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right h0 hC
  · nlinarith [mul_le_mul_of_nonneg_right h1 hC]
  · nlinarith [mul_le_mul_of_nonneg_right h2 hC]

theorem polynomialMassC2Budget_le_exp (N d : ℕ) {C P Q : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hN : (N : ℝ) ≤ Real.exp P) (hCQ : C ≤ Real.exp Q) :
    polynomialMassC2Budget N d C ≤ Real.exp (2 * P + 2 * d + Q + 2) := by
  have hN1 := one_add_le_exp_succ hP hN
  have hd1 : (d : ℝ) + 1 ≤ Real.exp d := Real.add_one_le_exp _
  have hb : 1 + (N : ℝ) * d ≤ Real.exp (P + d + 1) := by
    calc
      _ ≤ (1 + (N : ℝ)) * ((d : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) d]
      _ ≤ Real.exp (P + 1) * Real.exp d := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (Real.exp (P + d + 1))^2 * Real.exp Q := by
      unfold polynomialMassC2Budget
      gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem matrixSupCLM_sub {I J : Type*} [Fintype I] [Fintype J] (A B : Matrix I J ℝ) :
    matrixSupCLM (A-B) = matrixSupCLM A-matrixSupCLM B := by
  ext x i
  exact congrFun (Matrix.sub_mulVec A B x) i

noncomputable def polynomialColumns {P I J : Type*} [Fintype I] [Fintype J]
    (p : I → J → MvPolynomial P ℝ) (x : P → ℝ) : (J → ℝ) →L[ℝ] (I → ℝ) :=
  matrixSupCLM (fun i j => MvPolynomial.eval x (p i j))

theorem polynomialColumns_lipschitzOn_box {P I J : Type*} [Fintype P] [DecidableEq P]
    [Fintype I] [Fintype J] (p : I → J → MvPolynomial P ℝ) {d : ℕ}
    (hd : ∀ i j, (p i j).totalDegree ≤ d) (C : ℝ≥0) (hc : ∀ i j, realPolynomialMass (p i j) ≤ C) :
    LipschitzOnWith (Fintype.card J * polynomialBoxLip (Fintype.card P) d C)
      (polynomialColumns p) (Metric.closedBall 0 1) := by
  have hp := polynomialVectorMap_lipschitzOn_box (fun ij : I × J => p ij.1 ij.2)
    (fun ij => hd ij.1 ij.2) C (fun ij => hc ij.1 ij.2)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hE : 0 ≤ (polynomialBoxLip (Fintype.card P) d C : ℝ)*dist x y := by positivity
  have he (i) (j) : |MvPolynomial.eval x (p i j)-MvPolynomial.eval y (p i j)| ≤
      (polynomialBoxLip (Fintype.card P) d C : ℝ)*dist x y :=
    (dist_le_pi_dist (polynomialVectorMap (fun ij : I × J => p ij.1 ij.2) x)
      (polynomialVectorMap (fun ij : I × J => p ij.1 ij.2) y) (i,j)).trans (hp.dist_le_mul x hx y hy)
  let A : Matrix I J ℝ := fun i j => MvPolynomial.eval x (p i j)
  let B : Matrix I J ℝ := fun i j => MvPolynomial.eval y (p i j)
  rw [dist_eq_norm]
  change ‖matrixSupCLM A-matrixSupCLM B‖ ≤ _
  rw [← matrixSupCLM_sub]
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_assoc] using
    matrixSupCLM_norm_le (A-B) hE he

end Erdos3

end

section

namespace Erdos3

noncomputable def centeredPolynomialVariable {Z I : Type*} (center : Z → ℝ) :
    Z ⊕ I → MvPolynomial (PolynomialParameter Z I) ℝ
  | .inl z => MvPolynomial.C (center z) +
      MvPolynomial.X none * MvPolynomial.X (some (.inl z))
  | .inr i => MvPolynomial.X (some (.inr i))

noncomputable def centeredPolynomial {Z I : Type*} (center : Z → ℝ)
    (p : MvPolynomial (Z ⊕ I) ℝ) : MvPolynomial (PolynomialParameter Z I) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (centeredPolynomialVariable center) p

theorem centeredPolynomialVariable_eval {Z I : Type*} (center : Z → ℝ)
    (t : ℝ) (z : Z → ℝ) (x : I → ℝ) (j : Z ⊕ I) :
    MvPolynomial.eval (polynomialParameterPoint t z x) (centeredPolynomialVariable center j) =
      Sum.elim (fun i => center i + t * z i) x j := by
  cases j <;> simp [centeredPolynomialVariable, polynomialParameterPoint]

theorem centeredPolynomial_eval {Z I : Type*} (center : Z → ℝ)
    (p : MvPolynomial (Z ⊕ I) ℝ) (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    MvPolynomial.eval (polynomialParameterPoint t z x) (centeredPolynomial center p) =
      MvPolynomial.eval (Sum.elim (fun i => center i + t * z i) x) p := by
  unfold centeredPolynomial
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (MvPolynomial.eval (polynomialParameterPoint t z x)).comp MvPolynomial.C =
      RingHom.id ℝ := by ext a; simp
  rw [hc]
  congr 2
  funext j
  exact centeredPolynomialVariable_eval center t z x j

theorem centeredPolynomial_eval_zero {Z I : Type*} (center : Z → ℝ)
    (p : MvPolynomial (Z ⊕ I) ℝ) (z : Z → ℝ) (x : I → ℝ) :
    MvPolynomial.eval (polynomialParameterPoint 0 z x) (centeredPolynomial center p) =
      MvPolynomial.eval (Sum.elim center x) p := by
  simpa only [zero_mul, add_zero] using centeredPolynomial_eval center p 0 z x

theorem centeredPolynomialVariable_mass_le {Z I : Type*} (center : Z → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hc : ∀ z, |center z| ≤ A) (j : Z ⊕ I) :
    realPolynomialMass (centeredPolynomialVariable center j) ≤ A + 1 := by
  cases j with
  | inl z =>
    apply (realPolynomialMass_add_le _ _).trans
    apply add_le_add
    · simpa only [realPolynomialMass_C] using hc z
    · exact (realPolynomialMass_mul_le _ _).trans (by simp only [realPolynomialMass_X, one_mul, le_refl])
  | inr i => simpa only [centeredPolynomialVariable, realPolynomialMass_X] using (le_add_of_nonneg_left hA : (1 : ℝ) ≤ A + 1)

theorem centeredPolynomialVariable_totalDegree_le {Z I : Type*} (center : Z → ℝ) (j : Z ⊕ I) :
    (centeredPolynomialVariable center j).totalDegree ≤ 2 := by
  cases j with
  | inl z =>
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  | inr i => simp [centeredPolynomialVariable]

theorem centeredPolynomial_mass_le {Z I : Type*} (center : Z → ℝ)
    (p : MvPolynomial (Z ⊕ I) ℝ) {A : ℝ} (hA : 0 ≤ A) (hc : ∀ z, |center z| ≤ A)
    {d : ℕ} (hd : p.totalDegree ≤ d) :
    realPolynomialMass (centeredPolynomial center p) ≤ realPolynomialMass p * (A + 1) ^ d :=
  realPolynomialMass_substitution_le p _ (by linarith)
    (centeredPolynomialVariable_mass_le center hA hc) hd

theorem centeredPolynomial_totalDegree_le {Z I : Type*} (center : Z → ℝ)
    (p : MvPolynomial (Z ⊕ I) ℝ) {d : ℕ} (hd : p.totalDegree ≤ d) :
    (centeredPolynomial center p).totalDegree ≤ d * 2 :=
  polynomial_substitution_totalDegree_le p _ (centeredPolynomialVariable_totalDegree_le center) hd

end Erdos3

end

section

namespace Erdos3

theorem polynomialParameterPoint_continuous {Z I : Type*} (t : ℝ) :
    Continuous (fun p : (Z → ℝ) × (I → ℝ) => polynomialParameterPoint t p.1 p.2) := by
  apply continuous_pi
  intro s
  rcases s with _ | (j | i)
  · exact continuous_const
  · exact (continuous_apply j).comp continuous_fst
  · exact (continuous_apply i).comp continuous_snd

theorem parameterPolynomialMap_joint_continuous {Z I O : Type*}
    [Fintype Z] [Fintype I] [Fintype O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) (t : ℝ) :
    Continuous (fun y : (Z → ℝ) × (I → ℝ) => parameterPolynomialMap p t y.1 y.2) :=
  (polynomialVectorMap_contDiff p).continuous.comp (polynomialParameterPoint_continuous t)

end Erdos3

end

end OAI
