import IPRADerivations.Analysis.GaussianInverseSquareProductGrowth
import IPRADerivations.Analysis.GaussianSineProductImaginaryFirstOrder
import IPRADerivations.Analysis.GaussianSineProductImaginaryLogDerivativeTail

/-!
# Uniform first-order error for the imaginary-axis sine product

The quadratic finite remainder satisfies an affine inverse-square
recurrence. The same explicit finite product majorant that bounds the
original sine product bounds this recurrence, after absorbing its
forcing term into the row factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryFirstOrderBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (bounded_radius_mono unit)
open GaussianGammaEulerReflectionHead (body square_factor_at)
open GaussianInverseSquareProductGrowth
  (prefixNumerator prefixDenominator rowNumerator rowDenominator row_positive row_growth
    prefix_power_identity prefix_power_positive prefix_power_upper)
open GaussianInverseSquareProductTail (factorBounds sine_factor_bound)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qadd qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum qone qone_bounded)
open GaussianRationalSyntheticDivision (qadd_sub_cancel)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianSineProductImaginaryFirstOrder
  (first_order linearRow quadraticRow remainder remainder_succ remainder_zero step)
open GaussianSineProductImaginaryLogDerivative
  (axisNumerator derivative factor factorDerivative finite_logarithmic_derivative product squareDenominator)
open GaussianSineProductImaginaryLogDerivativeTail (axis_norm rational_real_bound)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def productBound (R : PTm n) : PTm n := unit (two*(R*R))
def derivativeBound (R : PTm n) : PTm n := productBound R*(two*(two*R))
def forcingBound (R : PTm n) : PTm n := productBound R + derivativeBound R*(two*R+R)
def exponent (R : PTm n) : PTm n := R*R+forcingBound R
def bound (R : PTm n) : PTm n := unit (two*exponent R)

theorem axis_disk (A B R : PTm n) (h : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (axisNumerator A) (R*B) :=
  le_congr (axis_norm A).eqSymm (.eqRefl _) (le_mul_mono h h)

theorem product_bound (A B R N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] bounded (product A B N) (productBound R) one := by
  apply GaussianInverseSquareProductGrowth.uniform_bound body (pairT (axisNumerator A) B) (R*R) N
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let s (t : PTm n) := Syn.shift t
  have hd : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (axisNumerator (s A)) (s R*s B) := by
    simpa only [Δ, s, Fm.shift, Syn.shift, ComplexLogarithmRemainder.subst_bounded,
      GaussianSineProductImaginaryLogDerivative.subst_axisNumerator, PTm.subst_mul] using (axis_disk A B R hA).shift
  have hs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ, s, Fm.shift, Syn.shift, one] using hB.shift
  simpa only [factorBounds, Syn.shift, s, subst_pairT, GaussianSineProductImaginaryLogDerivative.subst_axisNumerator,
    PTm.subst_mul, ConciseIPRA.PTm.subst_zero, Δ] using
    distance_congr ((square_factor_at (var 0) (axisNumerator (s A)) (s B)).eqSymm.eqTrans
      (congrInst2 body (zero_add _).eqSymm (.eqRefl _)))
      (.eqRefl _) (.eqRefl _) (congrMul (congrSucc (zero_add _).eqSymm) (congrSucc (zero_add _).eqSymm))
      (sine_factor_bound (var 0) (axisNumerator (s A)) (s R) (s B) hs hd)

theorem derivative_bound (A B R N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] bounded (derivative A B N) (derivativeBound R) one :=
  bound_congr (finite_logarithmic_derivative A B N hB).eqSymm (.eqRefl _) (one_mul one)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) (product_bound A B R N hB hA)
      (GaussianSineProductImaginaryLogDerivativeTail.uniform_bound A B R N hB hA))

private theorem square_positive (i : PTm n) : Γ ⊢[PRAAx] le one (succ i*succ i) :=
  positive_product _ _ (zero_lt_succ _) (zero_lt_succ _)

private theorem denom_positive (i B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (squareDenominator i B) :=
  positive_product _ _ (positive_product _ _ hB (zero_lt_succ _)) (positive_product _ _ hB (zero_lt_succ _))

private theorem quadratic_bound (i B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (quadraticRow i B) one (succ i*succ i) :=
  rational_real_bound _ _ one _ (denom_positive i B hB) (square_positive i)
    (le_of_eq_add (d := zero) (by unfold squareDenominator; ipra_ring))

private theorem linear_bound (i A B C R : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hC : Γ ⊢[PRAAx] le C (R*B)) :
    Γ ⊢[PRAAx] bounded (linearRow i A B C) (two*R+R) (succ i*succ i) := by
  let D := succ i*succ i
  let E := squareDenominator i B
  have hD := square_positive (Γ := Γ) i
  have hd : Γ ⊢[PRAAx] bounded (factorDerivative i A B) (two*R) D :=
    rational_real_bound _ _ _ _ (denom_positive i B hB) hD (by
      dsimp only [D, E, squareDenominator]
      ipra_le 2*𝔞(B)*𝔞(succ i)^2*sl hA)
  have hc : Γ ⊢[PRAAx] bounded (step B C) R one :=
    rational_real_bound _ _ _ _ hB (le_refl one) (le_congr (one_mul _).eqSymm (.eqRefl _) hC)
  have second : Γ ⊢[PRAAx] bounded (qmul (step B C) (quadraticRow i B)) R D :=
    bound_congr (.eqRefl _) (by ipra_ring) (one_mul D)
      (bounded_product _ _ _ _ _ _ (le_refl one) hD hc (quadratic_bound i B hB))
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hD) hD
    (le_of_eq_add (d := zero) (by ipra_ring))
    (bounded_sum _ _ _ _ _ _ hD hD hd second)

private theorem factor_bound (i A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] bounded (factor i A B) (succ i*succ i+R*R) (succ i*succ i) := by
  have dist := sine_factor_bound i (axisNumerator A) R B hB (axis_disk A B R hA)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (norm_from_distance _ qone _ _ _ _ (square_positive i) (le_refl one) dist qone_bounded)

private theorem forcing_bound (i A B C R : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hC : Γ ⊢[PRAAx] le C (R*B)) :
    Γ ⊢[PRAAx] bounded
      (qadd (qmul (product A B i) (quadraticRow i B)) (qmul (derivative A B i) (linearRow i A B C)))
      (forcingBound R) (succ i*succ i) := by
  let D := succ i*succ i
  have hD := square_positive (Γ := Γ) i
  have first : Γ ⊢[PRAAx] bounded (qmul (product A B i) (quadraticRow i B)) (productBound R) D :=
    bound_congr (.eqRefl _) (by ipra_ring) (one_mul _)
      (bounded_product _ _ _ _ _ _ (le_refl one) hD (product_bound A B R i hB hA) (quadratic_bound i B hB))
  have second : Γ ⊢[PRAAx] bounded (qmul (derivative A B i) (linearRow i A B C)) (derivativeBound R*(two*R+R)) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
      (bounded_product _ _ _ _ _ _ (le_refl one) hD (derivative_bound A B R i hB hA) (linear_bound i A B C R hB hA hC))
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hD) hD
    (le_of_eq_add (d := zero) (by unfold forcingBound; ipra_ring)) (bounded_sum _ _ _ _ _ _ hD hD first second)

private theorem prefix_lower (j : PTm n) : Γ ⊢[PRAAx] le (prefixDenominator j) (prefixNumerator j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · let Δ := (j ≐ zero) :: Γ
    have e : Δ ⊢[PRAAx] j ≐ zero := Prf.hyp0
    have p : Δ ⊢[PRAAx] prefixNumerator j ≐ one :=
      (congrAdd (congrMul (.eqRefl _) e) (congrMonus (.eqRefl one) e)).eqTrans
        ((congrAdd (.eqRefl _) (monus_zero one)).eqTrans (by ipra_ring))
    exact le_congr (congrSucc e).eqSymm p.eqSymm (le_refl one)
  · have hj : (j ≐ succ (LeanProofs.IPRA.PTm.pred j)) :: Γ ⊢[PRAAx] le one j :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have lower : (j ≐ succ (LeanProofs.IPRA.PTm.pred j)) :: Γ ⊢[PRAAx] le (prefixDenominator j) (num 4*j) := by
      unfold prefixDenominator
      ipra_le sl hj+2*Groth.ι (Q.mk _ j)
    exact le_trans lower (le_add_right _ _)

private def prefixLaw (A B C R i : PTm n) : Fm PTm n :=
  bounded (remainder A B C i) (pw (prefixNumerator i) (exponent R)) (pw (prefixDenominator i) (exponent R))

@[simp] private theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (A B C R i : PTm n) :
    (prefixLaw A B C R i).subst σ = prefixLaw (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ R)
      (Syn.subst σ i) := by
  simp [prefixLaw, exponent, forcingBound, derivativeBound, productBound, two]

private theorem prefix_step (A B C R i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] le (A+C) (R*B)) (ih : Γ ⊢[PRAAx] prefixLaw A B C R i) :
    Γ ⊢[PRAAx] prefixLaw A B C R (succ i) := by
  let K := exponent R
  let J := forcingBound R
  let S := R*R
  let D := succ i*succ i
  let X := pw (prefixNumerator i) K
  let Y := pw (prefixDenominator i) K
  let V := remainder A B C i
  let F := factor i (A+C) B
  let T := qadd (qmul (product A B i) (quadraticRow i B)) (qmul (derivative A B i) (linearRow i A B C))
  let M := pw (rowNumerator i) K
  let P := pw (rowDenominator i) K
  let Z := qadd T (qmul V F)
  have hy : Γ ⊢[PRAAx] le one Y := prefix_power_positive K i
  have hd : Γ ⊢[PRAAx] le one D := square_positive i
  have hp : Γ ⊢[PRAAx] le one P := RationalNonnegativePowers.denominator_positive _ _ (row_positive i)
  have hYX : Γ ⊢[PRAAx] le Y X := pw_le_pw K (prefix_lower i)
  have f := factor_bound i (A+C) B R hB hh
  have t := forcing_bound i A B C R hB (le_trans (le_add_right _ _) hh) (le_trans (le_add_left _ _) hh)
  have raw := bounded_sum T (qmul V F) J D (X*(D+S)) (Y*D) hd (positive_product _ _ hy hd) t
    (bounded_product V F X Y (D+S) D hy hd ih f)
  have absorbed : Γ ⊢[PRAAx] bounded Z (X*(D+K)) (Y*D) := by
    refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ hd (positive_product _ _ hy hd))
      (positive_product _ _ hy hd) ?_ raw
    dsimp only [K, exponent, J, S]
    ipra_le 𝔞(forcingBound R)*𝔞(Y)*𝔞(D)^2*sl hYX
  have enlarged : Γ ⊢[PRAAx] bounded Z (X*M) (Y*P) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hy hd) (positive_product _ _ hy hp)
      (by dsimp only [D, M, P]; ipra_le 𝔞(X)*𝔞(Y)*sl (row_growth (Γ := Γ) K i)) absorbed
  exact bound_congr (remainder_succ A B C i).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hy hp) (prefix_power_positive K (succ i))
      (le_of_eq_add (d := zero) ((prefix_power_identity K i).eqSymm.eqTrans (add_zero _).eqSymm)) enlarged)

theorem uniform_remainder (A B C R N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le (A+C) (R*B)) : Γ ⊢[PRAAx] bounded (remainder A B C N) (bound R) one := by
  let K := exponent R
  let Δ := Γ.map Fm.shift
  let s (t : PTm n) := Syn.shift t
  have hs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ, s, Fm.shift, Syn.shift, one] using hB.shift
  have hr : Δ ⊢[PRAAx] le (s A+s C) (s R*s B) := by simpa [Δ, s, Fm.shift, Syn.shift] using h.shift
  have h0 : Γ ⊢[PRAAx] prefixLaw A B C R zero :=
    bound_congr (remainder_zero A B C).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianMonicResidualRadius.zero_bounded _ _ (prefix_power_positive K zero))
  have all : Γ ⊢[PRAAx] .all (prefixLaw (s A) (s B) (s C) (s R) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_prefixLaw, s, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h0
    · simpa only [subst_prefixLaw, s, Syn.subst_var, Syn.repl_zero, subst_repl_shift] using
        prefix_step (s A) (s B) (s C) (s R) (var 0) hs.wk hr.wk Prf.hyp0
  have finite : Γ ⊢[PRAAx] prefixLaw A B C R N := by
    simpa only [subst_prefixLaw, s, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE N
  exact bounded_radius_mono _ _ _ _ _ (prefix_power_positive K N) (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) (prefix_power_upper K N)) finite

theorem finite_error (A B C R N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le (A+C) (R*B)) : Γ ⊢[PRAAx]
    distanceBounded (product (A+C) B N)
      (qadd (product A B N) (qmul (step B C) (derivative A B N))) ((C*C)*bound R) (B*B) := by
  let L := qadd (product A B N) (qmul (step B C) (derivative A B N))
  let E := qmul (qmul (step B C) (step B C)) (remainder A B C N)
  have hc : Γ ⊢[PRAAx] bounded (step B C) C B :=
    rational_real_bound _ _ _ _ hB hB (le_congr (mul_comm _ _) (.eqRefl _) (le_refl _))
  have quad : Γ ⊢[PRAAx] bounded E ((C*C)*bound R) (B*B) :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (positive_product _ _ hB hB) (le_refl one)
        (bounded_product _ _ _ _ _ _ hB hB hc hc) (uniform_remainder A B C R N hB h))
  exact distance_congr (first_order A B C N hB).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (bound_congr (qadd_sub_cancel L E (qmul_canonical _ _)).eqSymm (.eqRefl _) (.eqRefl _) quad)

theorem actual_finite_imaginary_sine_product_quadratic_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let A := var 0
       let B := var 1
       let C := var 2
       let R := var 3
       let N := var 4
       (le one B ⋏ le (A+C) (R*B)) ⟶
       distanceBounded (product (A+C) B N) (qadd (product A B N) (qmul (step B C) (derivative A B N)))
         ((C*C)*bound R) (B*B)) :=
  closeUniv 5 (.impI (finite_error _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryFirstOrderBound
