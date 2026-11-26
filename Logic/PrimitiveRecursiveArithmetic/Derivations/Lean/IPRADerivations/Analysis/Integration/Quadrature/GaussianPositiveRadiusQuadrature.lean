import IPRADerivations.Analysis.FiniteOperations.FiniteSums.GaussianPositiveRadiusFiniteSum
import IPRADerivations.Analysis.Integration.RiemannSums.GaussianRationalRiemannRefinement
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerWeightedHalfDecay

/-!
# Euclidean comparison of weighted rational sums

Add a single rational allowance to each real comparison row. The actual
weighted sum then retains the real companion sum and one allowance times
the interval width. Its bound uses the actual nonnegative comparison
point; the number of cells cancels from the allowance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRadiusQuadrature

open_ipra
open GaussianPositiveRadiusFiniteSum (boundBy bound_congr rowBounds)
open GaussianRationalFiniteSum (sum termsEqual)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalRiemannRefinement (leftSum weight)
open GaussianRationalNaturalScale (natScale naturalPoint)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_congr radius_represents radius_multiply)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def firstBody (t : PTm 2) : PTm 2 := inst2 t (var 0) (fstT (var 1))
private def secondBody : PTm 2 := sndT (var 1)
def correctedBody (t : PTm 2) : PTm 2 := GaussianRationalFiniteSum.addBody (firstBody t) secondBody

private theorem first_at (t : PTm 2) (i x : PTm n) : inst2 (firstBody t) i x = inst2 t i (fstT x) := by
  change Syn.subst ![i,x] (inst2 t (var 0) (fstT (var 1))) = _
  simp only [subst_inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,subst_fstT]

theorem corrected_row (t : PTm 2) (i x r : PTm n) : Γ ⊢[PRAAx]
    inst2 (correctedBody t) i (pairT x r) ≐ qadd (inst2 t i x) r := by
  rw [correctedBody,GaussianRationalFiniteSum.inst2_addBody,first_at]
  exact qadd_congr (congrInst2 t (.eqRefl i) (fst_pair _ _))
    (by simpa [secondBody,inst2] using snd_pair (Γ := Γ) x r)

theorem corrected_sum (t : PTm 2) (N x r : PTm n) : Γ ⊢[PRAAx]
    sum (correctedBody t) N (pairT x r) ≐ qadd (sum t N x) (natScale N r) := by
  have first : Γ ⊢[PRAAx] termsEqual (firstBody t) t N (pairT x r) x := by
    refine .allI (.impI ?_)
    simpa [termsEqual,first_at,Syn.shift] using
      congrInst2 t (.eqRefl (var 0)) (fst_pair (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift x) (Syn.shift r))
  have second : Γ ⊢[PRAAx] termsEqual secondBody GaussianRationalRiemannRefinement.constantBody N (pairT x r) r := by
    refine .allI (.impI ?_)
    simpa [termsEqual,secondBody,inst2,Syn.shift,GaussianRationalRiemannRefinement.constantBody] using
      snd_pair (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift x) (Syn.shift r)
  exact (GaussianRationalFiniteSum.sum_add (firstBody t) secondBody N (pairT x r)).eqTrans
    (qadd_congr (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ first)
      ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ second).eqTrans (GaussianRationalRiemannRefinement.constant_sum r N)))

private theorem radius_controls_self (A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    boundBy (radiusPoint A D) (radiusPoint A D) := by
  have rep := radius_represents (Γ := Γ) A D hD
  have pos := GaussianPositiveRealArithmetic.positive_from_representation _ A D
    (GaussianRationalHorner.ofGaussian_canonical _ _ hD) hD rep
  have signed : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.re (radiusNumerator A)) (ZT.ofNat A) := by
    apply ZT.derive
    simp only [radiusNumerator,ComplexLogarithmRemainder.eval_re_code]
  exact GaussianPositiveRadiusFiniteSum.from_representation _ _ A D hD pos
    (GaussianRationalHorner.scalar_congr (.eqRefl _) signed (.eqRefl _) rep.andE₁)
    (GaussianDominantPairAlgebra.radius_bounded A D hD)

private theorem weight_is_radius (C E N : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] weight C E N ≐ radiusPoint C (E*N) :=
  GaussianEulerDecayFactorBounds.fraction_is_radius_point C (E*N) (positive_product _ _ hE hN)

theorem weighted_error (N C E A D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    qmul (weight C E N) (natScale N (radiusPoint A D)) ≐ radiusPoint (C*A) (E*D) := by
  let r := radiusPoint A D
  have hOne : Γ ⊢[PRAAx] le one one := le_refl one
  have e : Γ ⊢[PRAAx] weight C E N ≐ weight C E (N*one) :=
    (weight_is_radius C E N hE hN).eqTrans
      ((radius_congr (.eqRefl _) (by ipra_ring)).eqTrans (weight_is_radius C E (N*one) hE (positive_product _ _ hN hOne)).eqSymm)
  have eq := (qmul_congr e (GaussianRationalNaturalScale.natScale_as_product N r)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      (qmul_congr (GaussianRationalRiemannRefinement.weight_repetition C E N one hE hN hOne) (.eqRefl r)))
  exact eq.eqTrans ((qmul_congr (weight_is_radius C E one hE hOne) (.eqRefl r)).eqTrans
    ((radius_multiply C (E*one) A D (positive_product _ _ hE hOne) hD).eqTrans
      (radius_congr (.eqRefl _) (by ipra_ring))))

theorem weighted_bound (f g : PTm 2) (N x y C E A D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rowBounds f (correctedBody g) N x (pairT y (radiusPoint A D))) : Γ ⊢[PRAAx]
    boundBy (leftSum f N x C E) (qadd (leftSum g N y C E) (radiusPoint (C*A) (E*D))) := by
  let w := weight C E N
  let r := radiusPoint A D
  have wk := weight_is_radius C E N hE hN
  have wBound := bound_congr wk.eqSymm wk.eqSymm (radius_controls_self C (E*N) (positive_product _ _ hE hN))
  have sums := GaussianPositiveRadiusFiniteSum.sum_bound f (correctedBody g) N x (pairT y r) h
  have rhs := (qmul_congr (.eqRefl w) (corrected_sum g N y r)).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (.eqRefl _) (weighted_error N C E A D hN hE hD)))
  exact bound_congr (.eqRefl _) rhs (GaussianPositiveRadiusFiniteSum.multiply_bound _ _ _ _ wBound sums)

theorem actual_weighted_row_domination_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 0) ⋏ le one (var 4) ⋏ le one (var 6) ⋏
      rowBounds f (correctedBody g) (var 0) (var 1) (pairT (var 2) (radiusPoint (var 5) (var 6)))) ⟶
      boundBy (leftSum f (var 0) (var 1) (var 3) (var 4))
        (qadd (leftSum g (var 0) (var 2) (var 3) (var 4)) (radiusPoint (var 3*var 5) (var 4*var 6)))) :=
  closeUniv 7 (.impI (weighted_bound f g _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPositiveRadiusQuadrature
