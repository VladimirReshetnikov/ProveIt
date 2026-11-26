import IPRADerivations.Analysis.Integration.GaussianCompactRiemannFourSplit
import IPRADerivations.Analysis.Beta.GaussianBetaSharpPartition
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# The actual original eta-to-top grid split at one, N/2 and N

The old even eta denominator gives exact integer numerator boundaries.
The four actual piece counts are their original numerical widths times
one shared mesh factor. The checked generic split allows all zero widths,
including the middle piece at N=2 and the exterior piece at N=top.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpFourSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaSharpPartition (lowWidth middleWidth supportTailWidth exteriorWidth halfPoint)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianCompactRiemannName (quadrature sampledModulus)
open GaussianRationalHorner (qadd)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianBetaIntegralThreeSplit (quadrature_congr)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def pieces (F : PR 3) (s k A R N K x : PTm n) : PTm n :=
  qadd
    (qadd (quadrature F s (lowWidth k A R*K) one (lowWidth k A R) (etaDen k A R) x)
      (quadrature F s (middleWidth k A R N*K) (etaDen k A R) (middleWidth k A R N) (etaDen k A R) x))
    (qadd (quadrature F s (supportTailWidth k A R N*K) (halfPoint k A R N) (supportTailWidth k A R N) (etaDen k A R) x)
      (quadrature F s (exteriorWidth k A R N*K) (etaDen k A R*N) (exteriorWidth k A R N) (etaDen k A R) x))

def source (F : PR 3) (k A R N K L x : PTm n) : Fm PTm n :=
  GaussianBetaSharpPartition.source k A R N ⋏ (le one K ⋏ sampledModulus F one (width k A R) (etaDen k A R) L x)

theorem total_width (k A R N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    GaussianCompactRiemannFourSplit.totalWidth (lowWidth k A R) (middleWidth k A R N) (supportTailWidth k A R N) (exteriorWidth k A R N) ≐ width k A R := by
  have all := GaussianBetaSharpPartition.exact_partition k A R N h
  have a := natEq all.andE₁
  have b := natEq all.andE₂.andE₁
  have c := natEq all.andE₂.andE₂.andE₁
  have d := natEq all.andE₂.andE₂.andE₂
  have e := natEq (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint (Γ := Γ) k A R)
  apply deriveNat
  unfold GaussianCompactRiemannFourSplit.totalWidth
  ipra_simps
  linear_combination a+b+c+d-e

theorem first_two_endpoint (k A R N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    one+(lowWidth k A R+middleWidth k A R N) ≐ halfPoint k A R N := by
  have all := GaussianBetaSharpPartition.exact_partition k A R N h
  exact (add_assoc _ _ _).eqSymm.eqTrans
    ((congrAdd all.andE₁ (.eqRefl _)).eqTrans all.andE₂.andE₁)

theorem first_three_endpoint (k A R N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    (one+(lowWidth k A R+middleWidth k A R N))+supportTailWidth k A R N ≐ etaDen k A R*N :=
  (congrAdd (first_two_endpoint k A R N h) (.eqRefl _)).eqTrans
    (GaussianBetaSharpPartition.exact_partition k A R N h).andE₂.andE₂.andE₁

/-- Original rational endpoints, actual piece grids and original evaluator. -/
theorem original_sharp_four_piece_split (F : PR 3) (s k A R N K L x : PTm n)
    (h : Γ ⊢[PRAAx] source F k A R N K L x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s (width k A R*K) one (width k A R) (etaDen k A R) x)
      (pieces F s k A R N K x) (num 4*width k A R) (etaDen k A R*unit s) := by
  let C1 := lowWidth k A R
  let C2 := middleWidth k A R N
  let C3 := supportTailWidth k A R N
  let C4 := exteriorWidth k A R N
  let W := GaussianCompactRiemannFourSplit.totalWidth C1 C2 C3 C4
  have w := total_width k A R N h.andE₁
  have modulus : Γ ⊢[PRAAx] sampledModulus F one W (etaDen k A R) L x := by
    have direct := Prf.eqSubst (Γ := Γ) (Ax := PRAAx)
      (sampledModulus F one (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
      ![width k A R,etaDen k A R,L,x] ![W,etaDen k A R,L,x]
      (fun i => by fin_cases i; exact w.eqSymm; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)
      (by simpa only [GaussianCompactRiemannName.subst_sampledModulus,Syn.subst_var,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
        ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using h.andE₂.andE₂)
    simpa only [GaussianCompactRiemannName.subst_sampledModulus,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using direct
  have input : Γ ⊢[PRAAx] GaussianCompactRiemannFourSplit.input F one C1 C2 C3 C4 (etaDen k A R) K L x :=
    .andI (le_refl one) (.andI (eta_den_positive k A R) (.andI h.andE₂.andE₁ modulus))
  have old := GaussianCompactRiemannFourSplit.original_four_piece_split F s one C1 C2 C3 C4 (etaDen k A R) K L x input
  have all := GaussianBetaSharpPartition.exact_partition k A R N h.andE₁
  have full := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul w (.eqRefl K)) (.eqRefl one) w (.eqRefl (etaDen k A R)) (.eqRefl x)
  have q2 := quadrature_congr (Γ := Γ) F (.eqRefl s) (.eqRefl (C2*K)) all.andE₁ (.eqRefl C2) (.eqRefl (etaDen k A R)) (.eqRefl x)
  have q3 := quadrature_congr (Γ := Γ) F (.eqRefl s) (.eqRefl (C3*K)) (first_two_endpoint k A R N h.andE₁) (.eqRefl C3) (.eqRefl (etaDen k A R)) (.eqRefl x)
  have q4 := quadrature_congr (Γ := Γ) F (.eqRefl s) (.eqRefl (C4*K)) (first_three_endpoint k A R N h.andE₁) (.eqRefl C4) (.eqRefl (etaDen k A R)) (.eqRefl x)
  exact distance_congr full (qadd_congr (qadd_congr (.eqRefl _) q2) (qadd_congr q3 q4)) (congrMul (.eqRefl (num 4)) w) (.eqRefl _) old

/-- The actual original Euler evaluator supplies its global local rate
from the original disk and numerical cutoff guards. -/
theorem original_Euler_four_piece_split (s z R B k A N K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hp : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerIntegrandName.evaluatorF s (width k A R*K) one (width k A R) (etaDen k A R) (GaussianEulerIntegrandName.fixedData z B))
      (pieces GaussianEulerIntegrandName.evaluatorF s k A R N K (GaussianEulerIntegrandName.fixedData z B))
      (num 4*width k A R) (etaDen k A R*unit s) := by
  have interval : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B one (width k A R) (etaDen k A R) (top k A R) :=
    .andI (.andI h.andE₁ (.andI (eta_den_positive k A R) h.andE₂))
      (.andI (le_refl one) (le_congr (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint k A R).eqSymm (.eqRefl _) (le_refl _)))
  exact original_sharp_four_piece_split GaussianEulerIntegrandName.evaluatorF s k A R N K
    (GaussianEulerCompactModulus.lipschitz R (etaDen k A R) (top k A R)) (GaussianEulerIntegrandName.fixedData z B)
    (.andI hp (.andI hK (GaussianEulerCompactAdditivity.sampled_modulus z R B one (width k A R) (etaDen k A R) (top k A R) interval)))

theorem middle_width_two (k A R : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    middleWidth k A R two ≐ zero :=
  (congrMonus ((mul_comm (GaussianBetaSharpPartition.halfDen k A R) two).eqTrans
    (GaussianBetaSharpPartition.even_denominator k A R hA).eqSymm) (.eqRefl (etaDen k A R))).eqTrans (monus_self _)

theorem actual_middle_at_two_zero (F : PR 3) (s k A R K x : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    quadrature F s (middleWidth k A R two*K) (etaDen k A R) (middleWidth k A R two) (etaDen k A R) x ≐ GaussianRationalHorner.qzero :=
  (quadrature_congr F (.eqRefl s) ((congrMul (middle_width_two k A R hA) (.eqRefl K)).eqTrans (zero_mul K))
    (.eqRefl (etaDen k A R)) (middle_width_two k A R hA) (.eqRefl (etaDen k A R)) (.eqRefl x)).eqTrans
      (GaussianCompactZeroSafeSplit.quadrature_empty F s (etaDen k A R) zero (etaDen k A R) x)

theorem original_sharp_four_actual_grids_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (quadrature F (var 0) (width (var 1) (var 2) (var 3)*var 5) one
        (width (var 1) (var 2) (var 3)) (etaDen (var 1) (var 2) (var 3)) (var 7))
        (pieces F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))
        (num 4*width (var 1) (var 2) (var 3)) (etaDen (var 1) (var 2) (var 3)*unit (var 0))) :=
  closeUniv 8 (.impI (original_sharp_four_piece_split F _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_degree_two_middle_quadrature_zero_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ quadrature F (var 0) (middleWidth (var 1) (var 2) (var 3) two*var 4)
      (etaDen (var 1) (var 2) (var 3)) (middleWidth (var 1) (var 2) (var 3) two) (etaDen (var 1) (var 2) (var 3)) (var 5) ≐ GaussianRationalHorner.qzero) :=
  closeUniv 6 (.impI (actual_middle_at_two_zero F _ _ _ _ _ _ Prf.hyp0))

theorem original_source_only_Euler_sharp_four_grids_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianGammaEulerCompactQuadrature.source (var 1) (var 2) (var 3) ⋏
      GaussianBetaSharpPartition.source (var 4) (var 5) (var 2) (var 6) ⋏ le one (var 7)) ⟶
      distanceBounded
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (width (var 4) (var 5) (var 2)*var 7) one
          (width (var 4) (var 5) (var 2)) (etaDen (var 4) (var 5) (var 2)) (GaussianEulerIntegrandName.fixedData (var 1) (var 3)))
        (pieces GaussianEulerIntegrandName.evaluatorF (var 0) (var 4) (var 5) (var 2) (var 6) (var 7) (GaussianEulerIntegrandName.fixedData (var 1) (var 3)))
        (num 4*width (var 4) (var 5) (var 2)) (etaDen (var 4) (var 5) (var 2)*unit (var 0))) :=
  closeUniv 8 (.impI (original_Euler_four_piece_split _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpFourSplit
