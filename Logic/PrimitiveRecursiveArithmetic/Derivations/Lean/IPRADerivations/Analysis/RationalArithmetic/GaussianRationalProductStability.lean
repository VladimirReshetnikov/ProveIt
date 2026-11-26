import IPRADerivations.Analysis.Polynomials.GaussianPolynomialScaling
import IPRADerivations.Analysis.Polynomials.GaussianRationalHorner
import IPRADerivations.Analysis.FiniteOperations.GaussianProductStability
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalMetric

/-!
# Common-denominator rational finite root-product stability

The common-positive-D presentation of finite-demand source04
`lem:product-stability`. Roots are the actual decoded Gaussian integers
divided by D, the point radius is R/D, the coefficient tolerance is A/B,
and the output radius is P/Q. All degrees and codes are numerical inputs.

The original coefficient comparisons concern the actual normalized
rational coefficient producer. Integer coefficient scaling and homogeneous
Horner linearity derive the evaluation bound; no residual or successful
factor-search premise is accepted.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalProductStability

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im scale normSq bounded)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (sub equal equal_of_values equal_re equal_im equal_of_code equal_trans equal_symm
    values_of_code re_scale im_scale re_sub im_sub re_zero im_zero normSq_equal)
open LeanProofs.IPRA.Analysis.GaussianPolynomialPerturbation (H)
open LeanProofs.IPRA.Analysis.GaussianPolynomialScaling (scaled crossErrors)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (scaledCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRootProduct (coefficients evaluate)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def sourceCondition (N D R A B P Q : PTm n) : Fm PTm n :=
  le (pw Q N*(N*pw R (pred N)*A)) (pw P N*B*pw D (pred N))

@[simp] theorem subst_sourceCondition {m : ℕ} (σ : Fin n → PTm m) (N D R A B P Q : PTm n) :
    (sourceCondition N D R A B P Q).subst σ = sourceCondition (Syn.subst σ N) (Syn.subst σ D)
      (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ P) (Syn.subst σ Q) := by simp [sourceCondition]

theorem coefficient_leading (S T N D : PTm n) : Γ ⊢[PRAAx]
    equal (entry (scaledCoefficients T N D) zero) (entry (scaledCoefficients S N D) zero) := by
  have s := values_of_code (GaussianRationalHorner.scaled_coefficients_lookup (Γ := Γ) S N D zero (zero_le N))
  have t := values_of_code (GaussianRationalHorner.scaled_coefficients_lookup (Γ := Γ) T N D zero (zero_le N))
  have sm := GaussianRootProduct.coefficients_monic (Γ := Γ) S N
  have tm := GaussianRootProduct.coefficients_monic (Γ := Γ) T N
  apply equal_of_values
  · rw [s.1,t.1]
    simp only [GaussianRationalRootProduct.scaledCoefficient,re_scale]
    rw [equal_re sm,equal_re tm]
  · rw [s.2,t.2]
    simp only [GaussianRationalRootProduct.scaledCoefficient,im_scale]
    rw [equal_im sm,equal_im tm]

/-- Actual scalar coefficient transformation followed by actual homogeneous
Horner is the scaled integer root-product evaluator. -/
theorem scaled_root_homogeneous (S N z D B : PTm n) : Γ ⊢[PRAAx]
    equal (H (scaled (scaledCoefficients S N D) B) z D (succ N))
      (scale (B*pw D N) (evaluate (coefficients S N) z)) := by
  have len := GaussianRationalHorner.scaled_coefficients_length (Γ := Γ) S N D
  have linear := GaussianPolynomialScaling.homogeneous_linearity (scaledCoefficients S N D) B z D (succ N)
    (le_congr (.eqRefl _) len.eqSymm (le_refl _))
  have root := GaussianRationalHorner.scaled_homogeneous (Γ := Γ) S N z D (succ N) (le_refl _)
  have eval : Γ ⊢[PRAAx] GaussianRootProduct.horner (coefficients S N) z (succ N) ≐ evaluate (coefficients S N) z :=
    congrAp3 GaussianRootProduct.hornerF (GaussianRootProduct.coefficients_length S N).eqSymm (.eqRefl _) (.eqRefl _)
  exact equal_trans linear (equal_trans (GaussianPolynomialScaling.scale_equal B root)
    (equal_trans (GaussianPolynomialScaling.scale_scale _ _ _)
      (GaussianPolynomialScaling.scale_equal _ (equal_of_code eval))))

theorem root_scaled_residual (S T N j D B : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    equal (sub (H (scaled (scaledCoefficients T N D) B) (entry S j) D (succ N))
      (H (scaled (scaledCoefficients S N D) B) (entry S j) D (succ N)))
      (scale (B*pw D N) (evaluate (coefficients T N) (entry S j))) := by
  have same := GaussianPolynomialPerturbation.sub_equal
    (scaled_root_homogeneous (Γ := Γ) T N (entry S j) D B)
    (scaled_root_homogeneous (Γ := Γ) S N (entry S j) D B)
  have root := GaussianRootProduct.listed_root_zero (Γ := Γ) S N j hj
  have diff : Γ ⊢[PRAAx] equal
      (sub (evaluate (coefficients T N) (entry S j)) (evaluate (coefficients S N) (entry S j)))
      (evaluate (coefficients T N) (entry S j)) := by
    apply equal_of_values
    · simp only [re_sub]; rw [equal_re root,re_zero]; ring
    · simp only [im_sub]; rw [equal_im root,im_zero]; ring
  exact equal_trans same (equal_trans (GaussianPolynomialPerturbation.scale_sub _ _ _)
    (GaussianPolynomialScaling.scale_equal _ diff))

/-- The only coefficient premise is the individual cleared comparison.
Its original normalized-rational producer is connected below. -/
theorem cleared_evaluation_bound (S T N j D R A B : PTm n)
    (hj : Γ ⊢[PRAAx] lt j N) (hD : Γ ⊢[PRAAx] le one D) (hDR : Γ ⊢[PRAAx] le D R)
    (hz : Γ ⊢[PRAAx] bounded (entry S j) R)
    (hErrors : Γ ⊢[PRAAx] crossErrors (scaledCoefficients S N D) (scaledCoefficients T N D) N A B (pw D N)) :
    Γ ⊢[PRAAx] le (((B*pw D N)*(B*pw D N))*normSq (evaluate (coefficients T N) (entry S j)))
      ((D*N*pw R (pred N)*(A*pw D N))*(D*N*pw R (pred N)*(A*pw D N))) := by
  have sl := GaussianRationalHorner.scaled_coefficients_length (Γ := Γ) S N D
  have tl := GaussianRationalHorner.scaled_coefficients_length (Γ := Γ) T N D
  have ss : Γ ⊢[PRAAx] le (succ N) (length (scaledCoefficients S N D)) := le_congr (.eqRefl _) sl.eqSymm (le_refl _)
  have ts : Γ ⊢[PRAAx] le (succ N) (length (scaledCoefficients T N D)) := le_congr (.eqRefl _) tl.eqSymm (le_refl _)
  have errors := GaussianPolynomialScaling.scaled_coefficient_errors _ _ N A B (pw D N) ss ts hErrors
  have leading := GaussianPolynomialScaling.scaled_leading _ _ B
    (le_trans (zero_lt_succ N) ss) (le_trans (zero_lt_succ N) ts) (coefficient_leading S T N D)
  have bound := GaussianPolynomialPerturbation.homogeneous_horner_bound
    (scaled (scaledCoefficients S N D) B) (scaled (scaledCoefficients T N D) B)
    (entry S j) N D R (A*pw D N)
    (le_congr (.eqRefl _) (GaussianPolynomialScaling.scaled_length _ _).eqSymm ss)
    (le_congr (.eqRefl _) (GaussianPolynomialScaling.scaled_length _ _).eqSymm ts)
    leading hz hDR (le_trans hD hDR) errors
  have eval := GaussianPolynomialPerturbation.bounded_of_equal
    (equal_symm (root_scaled_residual S T N j D B hj)) bound
  exact le_congr (ComplexLogarithmRemainder.normSq_scale _ _) (.eqRefl _) eval

theorem positive_degree_power (D N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pw D N ≐ pw D (pred N)*D :=
  (congrAp2 powF (Analysis.RationalIntegerNormalization.positive_form hN) (.eqRefl _)).eqTrans (pw_succ _ _)

theorem lifted_source_budget (N D R A B P Q E : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] sourceCondition N D R A B P Q) : Γ ⊢[PRAAx]
    le (pw Q N*(D*N*pw R (pred N)*(A*E))) (pw P N*B*pw D N*E) := by
  have scaled := mul_le_mul_right (D*E) h
  have left : Γ ⊢[PRAAx] (pw Q N*(N*pw R (pred N)*A))*(D*E) ≐
      pw Q N*(D*N*pw R (pred N)*(A*E)) := by ipra_ring
  have right : Γ ⊢[PRAAx] (pw P N*B*pw D (pred N))*(D*E) ≐ pw P N*B*pw D N*E := by
    have p := natEq (positive_degree_power (Γ := Γ) D N hN)
    apply deriveNat; ipra_simps; rw [p]; ring
  exact le_congr left right scaled

/-- Original coefficient bounds derive the precise norm-product bound used
by the actual least-factor search. Only positive B and D^N are cancelled. -/
theorem evaluation_bound_from_cross (S T N j D R A B P Q : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] lt j N)
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) (hDR : Γ ⊢[PRAAx] le D R)
    (hz : Γ ⊢[PRAAx] bounded (entry S j) R)
    (hErrors : Γ ⊢[PRAAx] crossErrors (scaledCoefficients S N D) (scaledCoefficients T N D) N A B (pw D N))
    (hCondition : Γ ⊢[PRAAx] sourceCondition N D R A B P Q) : Γ ⊢[PRAAx]
    GaussianProductNorm.evaluationBound T (entry S j) N P Q D := by
  have raw := cleared_evaluation_bound S T N j D R A B hj hD hDR hz hErrors
  have scaled := le_mul_mono (le_refl (pw (Q*Q) N)) raw
  have budget := lifted_source_budget N D R A B P Q (pw D N) hN hCondition
  have squared := le_mul_mono budget budget
  let K := (B*pw D N)*(B*pw D N)
  have left : Γ ⊢[PRAAx]
      pw (Q*Q) N*(K*normSq (evaluate (coefficients T N) (entry S j))) ≐
        K*(pw (Q*Q) N*normSq (evaluate (coefficients T N) (entry S j))) := by ipra_ring
  have middle : Γ ⊢[PRAAx]
      pw (Q*Q) N*((D*N*pw R (pred N)*(A*pw D N))*(D*N*pw R (pred N)*(A*pw D N))) ≐
        (pw Q N*(D*N*pw R (pred N)*(A*pw D N)))*(pw Q N*(D*N*pw R (pred N)*(A*pw D N))) := by
    have p := natEq (GaussianProductStability.power_product (Γ := Γ) Q Q N)
    apply deriveNat; ipra_simps; rw [p]; ring
  have right : Γ ⊢[PRAAx] (pw P N*B*pw D N*pw D N)*(pw P N*B*pw D N*pw D N) ≐
      K*(pw (P*P) N*pw (D*D) N) := by
    have p := natEq (GaussianProductStability.power_product (Γ := Γ) P P N)
    have d := natEq (GaussianProductStability.power_product (Γ := Γ) D D N)
    apply deriveNat; unfold K; ipra_simps; rw [p,d]; ring
  have comparison := le_trans (le_congr left middle scaled) (le_congr (.eqRefl _) right squared)
  have ePositive := GaussianRationalRootProduct.common_denominator_positive D N hD
  have bePositive := GaussianRationalHorner.positive_product B (pw D N) hB ePositive
  exact RationalValueBounds.positive_cancel (GaussianProductNorm.square_positive _ bePositive) comparison

/-! Original comparisons on the actual normalized rational coefficient list. -/

def coefficientBounds (S T N D A B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ GaussianRationalMetric.distanceBounded
    (entry (GaussianRationalRootProduct.rationalCoefficients (Syn.shift T) (Syn.shift N) (Syn.shift D)) (succ (var 0)))
    (entry (GaussianRationalRootProduct.rationalCoefficients (Syn.shift S) (Syn.shift N) (Syn.shift D)) (succ (var 0)))
    (Syn.shift A) (Syn.shift B))

@[simp] theorem subst_coefficientBounds {m : ℕ} (σ : Fin n → PTm m) (S T N D A B : PTm n) :
    (coefficientBounds S T N D A B).subst σ = coefficientBounds (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ B) := by simp [coefficientBounds,Syn.subst_shift,Syn.shift_subst]

theorem coefficient_bound_at (S T N D A B j : PTm n)
    (h : Γ ⊢[PRAAx] coefficientBounds S T N D A B) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded
      (entry (GaussianRationalRootProduct.rationalCoefficients T N D) (succ j))
      (entry (GaussianRationalRootProduct.rationalCoefficients S N D) (succ j)) A B := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ GaussianRationalMetric.distanceBounded
      (entry (GaussianRationalRootProduct.rationalCoefficients T N D) (succ j))
      (entry (GaussianRationalRootProduct.rationalCoefficients S N D) (succ j)) A B := by
    simpa only [coefficientBounds,Fm.subst_imp,subst_lt,GaussianRationalMetric.subst_distanceBounded,
      subst_entry,GaussianRationalRootProduct.subst_rationalCoefficients,ConciseIPRA.PTm.subst_succ,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j h
  exact .impE rule hj

/-- Independent normalized component denominators are retained by their
proved representations; no raw coefficient-bound premise is substituted. -/
theorem original_coefficient_cross (S T N D A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] coefficientBounds S T N D A B) : Γ ⊢[PRAAx]
    crossErrors (scaledCoefficients S N D) (scaledCoefficients T N D) N A B (pw D N) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have d : Δ ⊢[PRAAx] le one (Syn.shift D) := by
    simpa only [Δ,Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hD.shift.wk
  have b : Δ ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Δ,Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hB.shift.wk
  have bounds : Δ ⊢[PRAAx] coefficientBounds (Syn.shift S) (Syn.shift T) (Syn.shift N)
      (Syn.shift D) (Syn.shift A) (Syn.shift B) := by
    simpa only [Δ,Fm.shift,subst_coefficientBounds,Syn.shift] using h.shift.wk
  have index : Δ ⊢[PRAAx] lt (succ (var 0)) (succ (Syn.shift N)) :=
    (succ_monus_succ (succ (var 0)) (Syn.shift N)).eqTrans Prf.hyp0
  have sr := GaussianRationalHorner.coefficient_representation_at _ _ _ (succ (var 0))
    (GaussianRationalHorner.normalized_coefficients_represent (Syn.shift S) (Syn.shift N) (Syn.shift D) d)
    (lt_congr (.eqRefl _) (GaussianRationalHorner.scaled_coefficients_length _ _ _).eqSymm index)
  have tr := GaussianRationalHorner.coefficient_representation_at _ _ _ (succ (var 0))
    (GaussianRationalHorner.normalized_coefficients_represent (Syn.shift T) (Syn.shift N) (Syn.shift D) d)
    (lt_congr (.eqRefl _) (GaussianRationalHorner.scaled_coefficients_length _ _ _).eqSymm index)
  have original := coefficient_bound_at _ _ _ _ _ _ (var 0) bounds Prf.hyp0
  have ePositive := GaussianRationalRootProduct.common_denominator_positive (Syn.shift D) (Syn.shift N) d
  have cleared := (GaussianRationalMetric.bounded_difference_iff _ _ _ _ _ _ _ ePositive b tr sr).iffMp original
  simpa only [Δ,Syn.shift,GaussianRationalHorner.subst_scaledCoefficients,subst_ap2,
    GaussianRationalRootProduct.commonDenominator] using cleared

theorem cross_errors_reverse (F G N A B E : PTm n) (h : Γ ⊢[PRAAx] crossErrors F G N A B E) :
    Γ ⊢[PRAAx] crossErrors G F N A B E := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have errors : Δ ⊢[PRAAx] crossErrors (Syn.shift F) (Syn.shift G) (Syn.shift N)
      (Syn.shift A) (Syn.shift B) (Syn.shift E) := by
    simpa only [Δ,Fm.shift,GaussianPolynomialScaling.subst_crossErrors,Syn.shift] using h.shift.wk
  exact le_congr (congrMul (.eqRefl _) (GaussianProductStability.difference_norm_symmetric _ _))
    (.eqRefl _) (GaussianPolynomialScaling.cross_error_at _ _ _ _ _ _ (var 0) errors Prf.hyp0)

def basicInput (S T N D R A B P Q : PTm n) : Fm PTm n :=
  le one N ⋏ (le one D ⋏ (le one B ⋏ (le one Q ⋏ (le D R ⋏
    (length S ≐ N ⋏ (length T ≐ N ⋏ sourceCondition N D R A B P Q))))))

@[simp] theorem subst_basicInput {m : ℕ} (σ : Fin n → PTm m) (S T N D R A B P Q : PTm n) :
    (basicInput S T N D R A B P Q).subst σ = basicInput (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ P) (Syn.subst σ Q) := by
  simp [basicInput]

theorem reverse_basic (S T N D R A B P Q : PTm n) (h : Γ ⊢[PRAAx] basicInput S T N D R A B P Q) :
    Γ ⊢[PRAAx] basicInput T S N D R A B P Q := by
  have a := Prf.andE₂ h; have b := Prf.andE₂ a; have c := Prf.andE₂ b
  have d := Prf.andE₂ c; have e := Prf.andE₂ d; have f := Prf.andE₂ e
  exact .andI (Prf.andE₁ h) (.andI (Prf.andE₁ a) (.andI (Prf.andE₁ b)
    (.andI (Prf.andE₁ c) (.andI (Prf.andE₁ d) (.andI (Prf.andE₁ f)
      (.andI (Prf.andE₁ e) (Prf.andE₂ f)))))))

def clearedCover (S T D P Q : PTm n) : Fm PTm n := Foundations.FiniteHausdorff.cover
  GaussianProductStability.squaredDistanceF S T ((P*D)*(P*D)) Q
def clearedClose (S T D P Q : PTm n) : Fm PTm n := Foundations.FiniteHausdorff.close
  GaussianProductStability.squaredDistanceF S T ((P*D)*(P*D)) Q

theorem directed_hit (S T N D R A B P Q i : PTm n)
    (h : Γ ⊢[PRAAx] basicInput S T N D R A B P Q)
    (hPoints : Γ ⊢[PRAAx] GaussianProductStability.pointsBounded S N R)
    (hErrors : Γ ⊢[PRAAx] crossErrors (scaledCoefficients S N D) (scaledCoefficients T N D) N A B (pw D N))
    (hi : Γ ⊢[PRAAx] lt i (length S)) : Γ ⊢[PRAAx]
    Foundations.FiniteHausdorff.hit GaussianProductStability.squaredDistanceF (entry S i) T ((P*D)*(P*D)) Q := by
  have hN := Prf.andE₁ h
  have a := Prf.andE₂ h; have hD := Prf.andE₁ a
  have b := Prf.andE₂ a; have hB := Prf.andE₁ b
  have c := Prf.andE₂ b
  have d := Prf.andE₂ c; have hDR := Prf.andE₁ d
  have e := Prf.andE₂ d; have hS := Prf.andE₁ e
  have f := Prf.andE₂ e; have hT := Prf.andE₁ f
  have condition := Prf.andE₂ f
  have index := lt_congr (.eqRefl _) hS hi
  have point := GaussianProductStability.point_bound S N R i hPoints index
  have eval := evaluation_bound_from_cross S T N i D R A B P Q hN index hD hB hDR point hErrors condition
  let j := GaussianProductNorm.selected T (entry S i) N P Q D
  have range : Γ ⊢[PRAAx] lt j N := GaussianProductNorm.selected_range _ _ _ _ _ _ hN eval
  have bound := GaussianProductNorm.selected_squared_distance T (entry S i) N P Q D hN eval
  exact Foundations.FiniteHausdorff.hit_intro _ _ _ _ _ j
    (lt_congr (.eqRefl _) hT.eqSymm range)
    (le_congr (GaussianProductStability.squared_distance_at _ _ _).eqSymm (by ipra_ring) bound)

theorem directed_cover (S T N D R A B P Q : PTm n)
    (h : Γ ⊢[PRAAx] basicInput S T N D R A B P Q)
    (hPoints : Γ ⊢[PRAAx] GaussianProductStability.pointsBounded S N R)
    (hErrors : Γ ⊢[PRAAx] crossErrors (scaledCoefficients S N D) (scaledCoefficients T N D) N A B (pw D N)) :
    Γ ⊢[PRAAx] clearedCover S T D P Q := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift S)) :: Γ.map Fm.shift
  have input : Δ ⊢[PRAAx] basicInput (Syn.shift S) (Syn.shift T) (Syn.shift N) (Syn.shift D)
      (Syn.shift R) (Syn.shift A) (Syn.shift B) (Syn.shift P) (Syn.shift Q) := by
    simpa only [Δ,Fm.shift,subst_basicInput,Syn.shift] using h.shift.wk
  have points : Δ ⊢[PRAAx] GaussianProductStability.pointsBounded (Syn.shift S) (Syn.shift N) (Syn.shift R) := by
    simpa only [Δ,Fm.shift,GaussianProductStability.subst_pointsBounded,Syn.shift] using hPoints.shift.wk
  have errors : Δ ⊢[PRAAx] crossErrors (scaledCoefficients (Syn.shift S) (Syn.shift N) (Syn.shift D))
      (scaledCoefficients (Syn.shift T) (Syn.shift N) (Syn.shift D)) (Syn.shift N) (Syn.shift A) (Syn.shift B)
        (pw (Syn.shift D) (Syn.shift N)) := by
    simpa only [Δ,Fm.shift,GaussianPolynomialScaling.subst_crossErrors,GaussianRationalHorner.subst_scaledCoefficients,
      subst_ap2,Syn.shift] using hErrors.shift.wk
  have hit := directed_hit _ _ _ _ _ _ _ _ _ (var 0) input points errors Prf.hyp0
  simpa only [Δ,Foundations.FiniteHausdorff.hit,Syn.shift,subst_entry,PTm.subst_mul,
    Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one] using hit

def stabilityInput (S T N D R A B P Q : PTm n) : Fm PTm n :=
  basicInput S T N D R A B P Q ⋏
    (GaussianProductStability.pointsBounded S N R ⋏
      (GaussianProductStability.pointsBounded T N R ⋏ coefficientBounds S T N D A B))

@[simp] theorem subst_stabilityInput {m : ℕ} (σ : Fin n → PTm m) (S T N D R A B P Q : PTm n) :
    (stabilityInput S T N D R A B P Q).subst σ = stabilityInput (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ P) (Syn.subst σ Q) := by
  simp [stabilityInput]

/-- The full common-D source lemma: actual normalized coefficient bounds
give both covers with the exact source constant, including P=0 and repeats. -/
theorem product_stability (S T N D R A B P Q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N D R A B P Q) : Γ ⊢[PRAAx] clearedClose S T D P Q := by
  have basic := Prf.andE₁ h
  have sp := Prf.andE₁ (Prf.andE₂ h)
  have tp := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have coefficients := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have d := Prf.andE₁ (Prf.andE₂ basic)
  have b := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ basic))
  have errors := original_coefficient_cross S T N D A B d b coefficients
  exact .andI (directed_cover S T N D R A B P Q basic sp errors)
    (directed_cover T S N D R A B P Q (reverse_basic S T N D R A B P Q basic) tp
      (cross_errors_reverse _ _ _ _ _ _ errors))

def checker (S T D P Q : PTm n) : PTm n := Foundations.FiniteQueryDemand.apply4
  (Foundations.FiniteHausdorff.closeF GaussianProductStability.squaredDistanceF) S T ((P*D)*(P*D)) Q

theorem checker_reflection (S T D P Q : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (checker S T D P Q ≐ one) (clearedClose S T D P Q) :=
  Foundations.FiniteHausdorff.close_reflection _ _ _ _ _

theorem checker_accepts (S T N D R A B P Q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N D R A B P Q) : Γ ⊢[PRAAx] checker S T D P Q ≐ one :=
  (checker_reflection S T D P Q).iffMpr (product_stability S T N D R A B P Q h)

/-- The existing actual nearest-index program returns an original target
entry with the exact denominator-cleared rational distance bound. -/
theorem nearest_certificate (S T N D R A B P Q i : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N D R A B P Q) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] lt (GaussianProductStability.nearest S T i Q) (length T) ⋏
      le ((Q*Q)*normSq (sub (entry S i) (entry T (GaussianProductStability.nearest S T i Q)))) ((P*P)*(D*D)) := by
  have basic := Prf.andE₁ h
  have n := Prf.andE₁ basic
  have a := Prf.andE₂ basic; have b := Prf.andE₂ a; have c := Prf.andE₂ b
  have d := Prf.andE₂ c; have e := Prf.andE₂ d; have f := Prf.andE₂ e
  have lenT := Prf.andE₁ f
  have positiveT := le_congr (.eqRefl _) lenT.eqSymm n
  have covered := Prf.andE₁ (product_stability S T N D R A B P Q h)
  have hit := Foundations.FiniteHausdorff.cover_at GaussianProductStability.squaredDistanceF covered hi
  have minimum := Foundations.FiniteHausdorff.minimum_of_hit GaussianProductStability.squaredDistanceF hit
  have spec := Foundations.FiniteHausdorff.nearest_spec GaussianProductStability.squaredDistanceF (entry S i) T Q positiveT
  have bound := le_congr (Prf.andE₂ spec).eqSymm (.eqRefl _) minimum
  exact .andI (Prf.andE₁ spec)
    (le_congr (GaussianProductStability.squared_distance_at _ _ _) (by ipra_ring) bound)

/-- The same returned index has its literal normalized Gaussian-rational
distance bounded by P/Q, not just an unconnected raw integer comparison. -/
theorem nearest_rational_certificate (S T N D R A B P Q i : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N D R A B P Q) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (GaussianRationalHorner.ofGaussian (entry S i) D)
      (GaussianRationalHorner.ofGaussian (entry T (GaussianProductStability.nearest S T i Q)) D) P Q := by
  have basic := Prf.andE₁ h
  have d := Prf.andE₁ (Prf.andE₂ basic)
  have q := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ basic)))
  exact (GaussianRationalMetric.bounded_difference_iff _ _ _ _ _ _ _ d q
    (GaussianRationalHorner.ofGaussian_represents _ _ d)
    (GaussianRationalHorner.ofGaussian_represents _ _ d)).iffMpr
      (Prf.andE₂ (nearest_certificate S T N D R A B P Q i h hi))

theorem zero_tolerance_root (S T N D R A B Q i : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N D R A B zero Q) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] equal (entry S i) (entry T (GaussianProductStability.nearest S T i Q)) := by
  have cert := nearest_certificate S T N D R A B zero Q i h hi
  have q := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₁ h))))
  have z : Γ ⊢[PRAAx] (Q*Q)*normSq (sub (entry S i) (entry T (GaussianProductStability.nearest S T i Q))) ≐ zero :=
    le_antisymm (le_congr (.eqRefl _) ((congrMul (zero_mul zero) (.eqRefl _)).eqTrans (zero_mul _))
      (Prf.andE₂ cert)) (zero_le _)
  have positive : Γ ⊢[PRAAx] Q*Q ≐ succ (monus (Q*Q) one) :=
    (eq_add_of_le (GaussianProductNorm.square_positive Q q)).eqTrans (by ipra_ring)
  exact GaussianProductNorm.equal_of_difference_norm_zero _ _
    (eq_zero_of_succ_mul ((congrMul positive (.eqRefl _)).eqSymm.eqTrans z))

/-! Closed source-level and program endpoints, with all nine parameters
including the degree and every denominator quantified internally. -/

theorem normalized_coefficient_errors_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le one (var 5) ⟶ coefficientBounds (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossErrors (scaledCoefficients (var 0) (var 2) (var 3)) (scaledCoefficients (var 1) (var 2) (var 3))
        (var 2) (var 4) (var 5) (pw (var 3) (var 2))) :=
  closeUniv 6 (.impI (.impI (.impI (original_coefficient_cross _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem common_denominator_product_stability_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      clearedClose (var 0) (var 1) (var 3) (var 7) (var 8)) :=
  closeUniv 9 (.impI (product_stability _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem common_denominator_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      checker (var 0) (var 1) (var 3) (var 7) (var 8) ≐ one) :=
  closeUniv 9 (.impI (checker_accepts _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem nearest_root_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      lt (var 9) (length (var 0)) ⟶
      (lt (GaussianProductStability.nearest (var 0) (var 1) (var 9) (var 8)) (length (var 1)) ⋏
        le ((var 8*var 8)*normSq (sub (entry (var 0) (var 9))
          (entry (var 1) (GaussianProductStability.nearest (var 0) (var 1) (var 9) (var 8)))))
          ((var 7*var 7)*(var 3*var 3)))) :=
  closeUniv 10 (.impI (.impI (nearest_certificate _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem nearest_rational_root_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      lt (var 9) (length (var 0)) ⟶ GaussianRationalMetric.distanceBounded
        (GaussianRationalHorner.ofGaussian (entry (var 0) (var 9)) (var 3))
        (GaussianRationalHorner.ofGaussian (entry (var 1)
          (GaussianProductStability.nearest (var 0) (var 1) (var 9) (var 8))) (var 3)) (var 7) (var 8)) :=
  closeUniv 10 (.impI (.impI (nearest_rational_certificate _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem zero_tolerance_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) zero (var 7) ⟶
      lt (var 8) (length (var 0)) ⟶ equal (entry (var 0) (var 8))
        (entry (var 1) (GaussianProductStability.nearest (var 0) (var 1) (var 8) (var 7)))) :=
  closeUniv 9 (.impI (.impI (zero_tolerance_root _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem close_checker_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (Fm.iff (checker (var 0) (var 1) (var 2) (var 3) (var 4) ≐ one)
      (clearedClose (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (checker_reflection _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalProductStability
