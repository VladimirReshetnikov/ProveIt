import IPRADerivations.Analysis.Polynomials.Taylor.GaussianPolynomialPerturbation
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianProductNorm

/-!
# Finite root-product stability for Gaussian integer presentations

The integer-root presentation of finite-demand source04
`lem:product-stability`. The radius `A/B` is rational. The source condition is
exactly `B^N N R^(N-1) δ ≤ A^N`; coefficient errors and point bounds concern
actual runtime lists and actual constructed product coefficients.

Both bounded squared-distance covers, a true nearest-point selector and the
actual bounded close checker are derived. Evaluation bounds, polynomial
factorization and successful searches are conclusions, not premises.
No separation, distinct-root or positive-tolerance hypothesis is used.

The general Gaussian-rational coefficient/point presentation still requires
its independently denominated rational-Horner adapter. The theorem here
does not replace that remaining rational frontend.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianProductStability

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im normSq bounded normSq_eval)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (sub equal re_sub im_sub)
open LeanProofs.IPRA.Analysis.GaussianRootProduct (coefficients evaluate)
open LeanProofs.IPRA.Analysis.GaussianPolynomialPerturbation (coefficientErrors)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientBudget (N R δ : PTm n) : PTm n := N*pw R (pred N)*δ
def sourceCondition (N R δ A B : PTm n) : Fm PTm n :=
  le (pw B N*coefficientBudget N R δ) (pw A N)

ipra_subst coefficientBudget
ipra_subst sourceCondition

theorem power_product (a b N : PTm n) : Γ ⊢[PRAAx] pw (a*b) N ≐ pw a N*pw b N :=
  pw_mul_bases a b N

theorem difference_norm_symmetric (a b : PTm n) : Γ ⊢[PRAAx]
    normSq (sub a b) ≐ normSq (sub b a) := by
  apply deriveNat
  rw [normSq_eval,normSq_eval]
  simp only [re_sub,im_sub]
  ring

theorem coefficient_errors_reverse (F G N δ : PTm n)
    (h : Γ ⊢[PRAAx] coefficientErrors F G N δ) : Γ ⊢[PRAAx] coefficientErrors G F N δ := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have errors : Δ ⊢[PRAAx] coefficientErrors (Syn.shift F) (Syn.shift G) (Syn.shift N) (Syn.shift δ) := by
    simpa only [Δ,Fm.shift,GaussianPolynomialPerturbation.subst_coefficientErrors,Syn.shift] using h.shift.wk
  have point := GaussianPolynomialPerturbation.coefficient_error_at _ _ _ _ (var 0) errors Prf.hyp0
  exact le_congr (difference_norm_symmetric _ _) (.eqRefl _) point

/-- The source coefficient condition gives the actual evaluation product
bound. Its derivation uses the actual listed-root zero theorem. -/
theorem evaluation_bound_from_coefficients (S T N j R δ A B : PTm n)
    (hj : Γ ⊢[PRAAx] lt j N) (hz : Γ ⊢[PRAAx] bounded (entry S j) R)
    (hR : Γ ⊢[PRAAx] le one R)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors (coefficients S N) (coefficients T N) N δ)
    (hCondition : Γ ⊢[PRAAx] sourceCondition N R δ A B) : Γ ⊢[PRAAx]
    GaussianProductNorm.evaluationBound T (entry S j) N A B one := by
  have eval := GaussianPolynomialPerturbation.root_evaluation_bound S T N j R δ hj hz hR hErrors
  have scaled := le_mul_mono (le_refl (pw (B*B) N)) eval
  have squared := le_mul_mono hCondition hCondition
  have left : Γ ⊢[PRAAx]
      (pw B N*coefficientBudget N R δ)*(pw B N*coefficientBudget N R δ) ≐
        pw (B*B) N*(coefficientBudget N R δ*coefficientBudget N R δ) := by
    have p := natEq (power_product (Γ := Γ) B B N)
    apply deriveNat; ipra_simps; rw [p]; ring
  have right : Γ ⊢[PRAAx] pw A N*pw A N ≐ pw (A*A) N*pw (one*one) N := by
    have p := natEq (power_product (Γ := Γ) A A N)
    have q := natEq ((congrAp2 powF (.eqRefl N) (one_mul one)).eqTrans
      (GaussianPolynomialPerturbation.one_power (Γ := Γ) N))
    apply deriveNat; ipra_simps; rw [p,q]; ring
  exact le_trans scaled (le_congr left right squared)

def witness (S T N j A B : PTm n) : PTm n := GaussianProductNorm.selected T (entry S j) N A B one

ipra_subst witness

theorem witness_range (S T N j R δ A B : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] lt j N)
    (hz : Γ ⊢[PRAAx] bounded (entry S j) R) (hR : Γ ⊢[PRAAx] le one R)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors (coefficients S N) (coefficients T N) N δ)
    (hCondition : Γ ⊢[PRAAx] sourceCondition N R δ A B) : Γ ⊢[PRAAx] lt (witness S T N j A B) N :=
  GaussianProductNorm.selected_range _ _ _ _ _ _ hN
    (evaluation_bound_from_coefficients S T N j R δ A B hj hz hR hErrors hCondition)

theorem witness_distance (S T N j R δ A B : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] lt j N)
    (hz : Γ ⊢[PRAAx] bounded (entry S j) R) (hR : Γ ⊢[PRAAx] le one R)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors (coefficients S N) (coefficients T N) N δ)
    (hCondition : Γ ⊢[PRAAx] sourceCondition N R δ A B) : Γ ⊢[PRAAx]
    le ((B*B)*normSq (sub (entry S j) (entry T (witness S T N j A B)))) (A*A) :=
  le_congr (.eqRefl _) (by ipra_ring)
    (GaussianProductNorm.selected_squared_distance _ _ _ _ _ _ hN
      (evaluation_bound_from_coefficients S T N j R δ A B hj hz hR hErrors hCondition))

def pointsBounded (S N R : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ bounded (entry (Syn.shift S) (var 0)) (Syn.shift R))

ipra_subst pointsBounded [Syn.subst_shift, Syn.shift_subst]

theorem point_bound (S N R j : PTm n) (h : Γ ⊢[PRAAx] pointsBounded S N R) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] bounded (entry S j) R := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ bounded (entry S j) R := by
    simpa only [pointsBounded,Fm.subst_imp,subst_lt,ComplexLogarithmRemainder.subst_bounded,subst_entry,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j h
  exact .impE rule hj

/-- The actual finite metric score is the denominator-cleared squared
Gaussian norm; no abstract distance code is a parameter to this theorem. -/
def score (x y B : PTm n) : PTm n := (B*B)*normSq (sub x y)
ipra_subst score
def squaredDistanceF : PR 3 := PTm.toPR (score (var 0) (var 1) (var 2))

theorem squared_distance_at (x y B : PTm n) : Γ ⊢[PRAAx]
    Foundations.FiniteHausdorff.distance squaredDistanceF x y B ≐ (B*B)*normSq (sub x y) := by
  change Γ ⊢[PRAAx] Foundations.FiniteHausdorff.distance squaredDistanceF x y B ≐ score x y B
  simpa [Foundations.FiniteHausdorff.distance,squaredDistanceF,ap3] using toPR_eq (Γ := Γ)
    (score (var 0) (var 1) (var 2) : PTm 3) ![x,y,B]

def cover (S T A B : PTm n) : Fm PTm n := Foundations.FiniteHausdorff.cover squaredDistanceF S T (A*A) B
def close (S T A B : PTm n) : Fm PTm n := Foundations.FiniteHausdorff.close squaredDistanceF S T (A*A) B

ipra_subst cover
ipra_subst close [Foundations.FiniteHausdorff.close]

def directionInput (S T N R δ A B : PTm n) : Fm PTm n :=
  le one N ⋏ (le one R ⋏ (length S ≐ N ⋏ (length T ≐ N ⋏
    (pointsBounded S N R ⋏ (coefficientErrors (coefficients S N) (coefficients T N) N δ ⋏
      sourceCondition N R δ A B)))))

ipra_subst directionInput

theorem direction_hit (S T N R δ A B i : PTm n)
    (h : Γ ⊢[PRAAx] directionInput S T N R δ A B) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] Foundations.FiniteHausdorff.hit squaredDistanceF (entry S i) T (A*A) B := by
  have hN := Prf.andE₁ h
  have h1 := Prf.andE₂ h
  have hR := Prf.andE₁ h1
  have h2 := Prf.andE₂ h1
  have hS := Prf.andE₁ h2
  have h3 := Prf.andE₂ h2
  have hT := Prf.andE₁ h3
  have h4 := Prf.andE₂ h3
  have hz := Prf.andE₁ h4
  have h5 := Prf.andE₂ h4
  have hErrors := Prf.andE₁ h5
  have hCondition := Prf.andE₂ h5
  have index := lt_congr (.eqRefl _) hS hi
  have point := point_bound S N R i hz index
  have range := witness_range S T N i R δ A B hN index point hR hErrors hCondition
  have bound := witness_distance S T N i R δ A B hN index point hR hErrors hCondition
  exact Foundations.FiniteHausdorff.hit_intro _ _ _ _ _ (witness S T N i A B)
    (lt_congr (.eqRefl _) hT.eqSymm range)
    (le_congr (squared_distance_at _ _ _).eqSymm (.eqRefl _) bound)

theorem directed_cover (S T N R δ A B : PTm n)
    (h : Γ ⊢[PRAAx] directionInput S T N R δ A B) : Γ ⊢[PRAAx] cover S T A B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift S)) :: Γ.map Fm.shift
  have input : Δ ⊢[PRAAx] directionInput (Syn.shift S) (Syn.shift T) (Syn.shift N)
      (Syn.shift R) (Syn.shift δ) (Syn.shift A) (Syn.shift B) := by
    simpa only [Δ,Fm.shift,subst_directionInput,Syn.shift] using h.shift.wk
  have hit := direction_hit _ _ _ _ _ _ _ (var 0) input Prf.hyp0
  simpa only [Δ,Foundations.FiniteHausdorff.hit,Syn.shift,subst_entry,PTm.subst_mul,
    Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one] using hit

def stabilityInput (S T N R δ A B : PTm n) : Fm PTm n :=
  le one B ⋏ (directionInput S T N R δ A B ⋏ pointsBounded T N R)

ipra_subst stabilityInput

theorem reverse_input (S T N R δ A B : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R δ A B) : Γ ⊢[PRAAx] directionInput T S N R δ A B := by
  have forward := Prf.andE₁ (Prf.andE₂ h)
  have hN := Prf.andE₁ forward
  have h1 := Prf.andE₂ forward
  have hR := Prf.andE₁ h1
  have h2 := Prf.andE₂ h1
  have hS := Prf.andE₁ h2
  have h3 := Prf.andE₂ h2
  have hT := Prf.andE₁ h3
  have h4 := Prf.andE₂ h3
  have h5 := Prf.andE₂ h4
  have hErrors := Prf.andE₁ h5
  have hCondition := Prf.andE₂ h5
  exact .andI hN (.andI hR (.andI hT (.andI hS
    (.andI (Prf.andE₂ (Prf.andE₂ h)) (.andI (coefficient_errors_reverse _ _ _ _ hErrors) hCondition)))))

/-- Both covers are proved by the actual finite searches. Symmetry of the
coefficient norm is derived, with no increase in the source budget. -/
theorem product_stability (S T N R δ A B : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R δ A B) : Γ ⊢[PRAAx] close S T A B :=
  .andI (directed_cover S T N R δ A B (Prf.andE₁ (Prf.andE₂ h)))
    (directed_cover T S N R δ A B (reverse_input S T N R δ A B h))

def nearest (S T i B : PTm n) : PTm n :=
  Foundations.FiniteHausdorff.nearest squaredDistanceF (entry S i) T B

ipra_subst nearest

/-- The existing actual argmin, with deterministic ties, satisfies the
same rational radius; the output is a true nearest point. -/
theorem nearest_certificate (S T N R δ A B i : PTm n)
    (h : Γ ⊢[PRAAx] directionInput S T N R δ A B) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] lt (nearest S T i B) (length T) ⋏
      le ((B*B)*normSq (sub (entry S i) (entry T (nearest S T i B)))) (A*A) := by
  have hN := Prf.andE₁ h
  have lenT := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have positive := le_congr (.eqRefl _) lenT.eqSymm hN
  have spec := Foundations.FiniteHausdorff.nearest_spec squaredDistanceF (entry S i) T B positive
  have hit := direction_hit S T N R δ A B i h hi
  have minimum := Foundations.FiniteHausdorff.minimum_of_hit squaredDistanceF hit
  have bound := le_congr (Prf.andE₂ spec).eqSymm (.eqRefl _) minimum
  exact .andI (Prf.andE₁ spec) (le_congr (squared_distance_at _ _ _) (.eqRefl _) bound)

private alias cancel_positive := Common.mul_cancel_le

/-- With the legitimate positive rational denominator, the actual selected
point minimizes the unscaled Gaussian squared norm as well. -/
theorem nearest_minimal (S T j B i : PTm n) (hT : Γ ⊢[PRAAx] le one (length T))
    (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] lt i (length T)) : Γ ⊢[PRAAx]
    le (normSq (sub (entry S j) (entry T (nearest S T j B)))) (normSq (sub (entry S j) (entry T i))) := by
  have spec := Foundations.FiniteHausdorff.nearest_spec squaredDistanceF (entry S j) T B hT
  have bound := le_congr (Prf.andE₂ spec).eqSymm (.eqRefl _)
    (Foundations.FiniteHausdorff.distanceTo_le squaredDistanceF (entry S j) T B i hi)
  exact cancel_positive (GaussianProductNorm.square_positive B hB)
    (le_congr (squared_distance_at _ _ _) (squared_distance_at _ _ _) bound)

theorem zero_tolerance_root (S T N R δ B i : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R δ zero B) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] equal (entry S i) (entry T (nearest S T i B)) := by
  have near := nearest_certificate S T N R δ zero B i (Prf.andE₁ (Prf.andE₂ h)) hi
  have zp : Γ ⊢[PRAAx] (B*B)*normSq (sub (entry S i) (entry T (nearest S T i B))) ≐ zero :=
    le_antisymm (le_congr (.eqRefl _) (zero_mul zero) (Prf.andE₂ near)) (zero_le _)
  have positive : Γ ⊢[PRAAx] B*B ≐ succ (monus (B*B) one) :=
    (eq_add_of_le (GaussianProductNorm.square_positive B (Prf.andE₁ h))).eqTrans (by ipra_ring)
  exact GaussianProductNorm.equal_of_difference_norm_zero _ _
    (eq_zero_of_succ_mul ((congrMul positive (.eqRefl _)).eqSymm.eqTrans zp))

def checker (S T A B : PTm n) : PTm n := Foundations.FiniteQueryDemand.apply4
  (Foundations.FiniteHausdorff.closeF squaredDistanceF) S T (A*A) B

theorem checker_reflection (S T A B : PTm n) : Γ ⊢[PRAAx] Fm.iff (checker S T A B ≐ one) (close S T A B) :=
  Foundations.FiniteHausdorff.close_reflection _ _ _ _ _

theorem checker_accepts (S T N R δ A B : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R δ A B) : Γ ⊢[PRAAx] checker S T A B ≐ one :=
  (checker_reflection S T A B).iffMpr (product_stability S T N R δ A B h)

/-! Actual nearest-point output program and its original-list certificate. -/

def output (S T i B : PTm n) : PTm n := pairT (nearest S T i B) (entry T (nearest S T i B))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (S T i B : PTm n) : PTm n := ConciseIPRA.PTm.app outputF ![S,T,i,B]

ipra_subst output

theorem output_at (S T i B : PTm n) : Γ ⊢[PRAAx] run S T i B ≐ output S T i B := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![S,T,i,B]
theorem output_index (S T i B : PTm n) : Γ ⊢[PRAAx] fstT (run S T i B) ≐ nearest S T i B :=
  (output_at S T i B).fstE
theorem output_point (S T i B : PTm n) : Γ ⊢[PRAAx] sndT (run S T i B) ≐ entry T (nearest S T i B) :=
  (output_at S T i B).sndE
theorem output_lookup (S T i B : PTm n) : Γ ⊢[PRAAx] sndT (run S T i B) ≐ entry T (fstT (run S T i B)) :=
  (output_point S T i B).eqTrans (entry_congr (.eqRefl _) (output_index S T i B).eqSymm)

def outputCorrect (S T i A B : PTm n) : Fm PTm n :=
  lt (fstT (run S T i B)) (length T) ⋏
    (sndT (run S T i B) ≐ entry T (fstT (run S T i B)) ⋏
      le ((B*B)*normSq (sub (entry S i) (sndT (run S T i B)))) (A*A))

theorem output_correct (S T N R δ A B i : PTm n)
    (h : Γ ⊢[PRAAx] directionInput S T N R δ A B) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] outputCorrect S T i A B := by
  have cert := nearest_certificate S T N R δ A B i h hi
  have value := GaussianPolynomialPerturbation.sub_equal (GaussianRootAlgebra.equal_refl (entry S i))
    (GaussianRootAlgebra.equal_of_code (output_point (Γ := Γ) S T i B))
  exact .andI (lt_congr (output_index S T i B).eqSymm (.eqRefl _) (Prf.andE₁ cert))
    (.andI (output_lookup S T i B)
      (le_congr (congrMul (.eqRefl _) (GaussianRootAlgebra.normSq_equal value).eqSymm)
        (.eqRefl _) (Prf.andE₂ cert)))

/-! Closed ordinary-iPRA endpoints. All list, degree, error and radius data
are numerical variables, including N; the checker is one fixed PR program. -/

theorem power_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (pw (var 0*var 1) (var 2) ≐ pw (var 0) (var 2)*pw (var 1) (var 2)) :=
  closeUniv 3 (power_product _ _ _)

theorem difference_norm_symmetry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (normSq (sub (var 0) (var 1)) ≐ normSq (sub (var 1) (var 0))) :=
  closeUniv 2 (difference_norm_symmetric _ _)

theorem integer_product_stability_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      close (var 0) (var 1) (var 5) (var 6)) :=
  closeUniv 7 (.impI (product_stability _ _ _ _ _ _ _ Prf.hyp0))

theorem integer_product_stability_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      checker (var 0) (var 1) (var 5) (var 6) ≐ one) :=
  closeUniv 7 (.impI (checker_accepts _ _ _ _ _ _ _ Prf.hyp0))

theorem nearest_root_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (directionInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      lt (var 7) (length (var 0)) ⟶
      (lt (nearest (var 0) (var 1) (var 7) (var 6)) (length (var 1)) ⋏
        le ((var 6*var 6)*normSq (sub (entry (var 0) (var 7))
          (entry (var 1) (nearest (var 0) (var 1) (var 7) (var 6))))) (var 5*var 5))) :=
  closeUniv 8 (.impI (.impI (nearest_certificate _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem zero_tolerance_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) zero (var 5) ⟶
      lt (var 6) (length (var 0)) ⟶
      equal (entry (var 0) (var 6)) (entry (var 1) (nearest (var 0) (var 1) (var 6) (var 5)))) :=
  closeUniv 7 (.impI (.impI (zero_tolerance_root _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem nearest_program_metadata_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (output_at _ _ _ _)

theorem nearest_program_correct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (directionInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      lt (var 7) (length (var 0)) ⟶ outputCorrect (var 0) (var 1) (var 7) (var 5) (var 6)) :=
  closeUniv 8 (.impI (.impI (output_correct _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem close_checker_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (checker (var 0) (var 1) (var 2) (var 3) ≐ one) (close (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (checker_reflection _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianProductStability
