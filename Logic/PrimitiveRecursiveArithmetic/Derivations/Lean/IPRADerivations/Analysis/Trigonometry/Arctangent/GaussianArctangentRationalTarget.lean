import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentGridSearch

/-!
# Exact rational arctangent targets on the finite grid

Enlarging the factorial index to cover twice the target denominator
represents the target in the grid's clearing denominator. The selected
point lies at or above that exact rational target, with overshoot at
most twice one grid width.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentRationalTarget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentExponentialPrefix (source total prefixValue)
open GaussianArctangentGridSearch (crossing crossing_spec crossing_residual)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product represents_rescale)
open GaussianRationalMetric (distanceBounded bounded_difference_iff)
open GaussianRootAlgebra (re_sub im_sub re_scale im_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Products (fact)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def target (Q D L : PTm n) : PTm n := Q*quo (fact L) (two*D)
def chosen (Q D M L : PTm n) : PTm n := crossing (target Q D L) M L
def targetPoint (Q D : PTm n) : PTm n := ofGaussian (scale Q imaginaryCode) D

theorem target_exact (Q D L : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hL : Γ ⊢[PRAAx] le (two*D) L) :
    Γ ⊢[PRAAx] (two*D)*target Q D L ≐ Q*fact L := by
  have hp := positive_product two D (le_succ_self one) hD
  have hs := RationalIntegerNormalization.positive_form hp
  have divides := AnalyticNumberTheory.Primes.dvd_fact (le_congr hs (.eqRefl _) hL)
  have exactDiv := DiophantineNumberTheory.Coprime.eq_of_dvd' hs (dvd_congr_left hs.eqSymm divides)
  exact (by unfold target; ipra_ring : Γ ⊢[PRAAx]
    (two*D)*target Q D L ≐ Q*((two*D)*quo (fact L) (two*D))).eqTrans
    (congrMul (.eqRefl Q) exactDiv.eqSymm)

theorem target_admitted (Q D M L : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hL : Γ ⊢[PRAAx] le (two*D) L)
    (hQ : Γ ⊢[PRAAx] le (Q*fact L) ((two*D)*total M M L)) :
    Γ ⊢[PRAAx] le (target Q D L) (total M M L) := by
  have hp := positive_product two D (le_succ_self one) hD
  have hs := RationalIntegerNormalization.positive_form hp
  have hT := target_exact Q D L hD hL
  exact mul_le_cancel (le_congr (hT.eqSymm.eqTrans (congrMul hs (.eqRefl _))) (congrMul hs (.eqRefl _)) hQ)

def brackets (Q D M L : PTm n) : Fm PTm n :=
  le (chosen Q D M L) M ⋏
    (le (Q*fact L) ((two*D)*total (chosen Q D M L) M L) ⋏
      le (M*((two*D)*total (chosen Q D M L) M L)) (M*(Q*fact L)+(two*D)*fact L))

theorem rational_target_brackets (Q D M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hD : Γ ⊢[PRAAx] le one D) (hL : Γ ⊢[PRAAx] le (two*D) L)
    (hQ : Γ ⊢[PRAAx] le (Q*fact L) ((two*D)*total M M L)) :
    Γ ⊢[PRAAx] brackets Q D M L := by
  have hT := target_admitted Q D M L hD hL hQ
  have hc := crossing_spec (chosen Q D M L) (target Q D L) M L hT
  have he := target_exact Q D L hD hL
  have low := le_congr he (.eqRefl _) (le_mul_mono (le_refl (two*D)) hc.andE₂.andE₁)
  have upper := le_mul_mono (le_refl (two*D)) (crossing_residual (target Q D L) M L hs hT)
  refine .andI hc.andE₁ (.andI low (le_congr (by unfold chosen; ipra_ring) ?_ upper))
  refine (by ipra_ring : Γ ⊢[PRAAx] (two*D)*(M*target Q D L+fact L) ≐
    M*((two*D)*target Q D L)+(two*D)*fact L).eqTrans (congrAdd (congrMul (.eqRefl _) he) (.eqRefl _))

theorem rational_target_distance (Q D M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hD : Γ ⊢[PRAAx] le one D) (hL : Γ ⊢[PRAAx] le (two*D) L)
    (hQ : Γ ⊢[PRAAx] le (Q*fact L) ((two*D)*total M M L)) :
    Γ ⊢[PRAAx] distanceBounded (prefixValue (chosen Q D M L) M L) (targetPoint Q D) two M := by
  let k := chosen Q D M L
  let F := fact L
  let E := F*D
  let X := (two*D)*total k M L
  let Y := Q*F
  let W := monus X Y
  let a := scale (two*total k M L) imaginaryCode
  let b := scale Q imaginaryCode
  have h := rational_target_brackets Q D M L hs hD hL hQ
  have he : Γ ⊢[PRAAx] X ≐ Y+W := eq_add_of_le h.andE₂.andE₁
  have upper : Γ ⊢[PRAAx] le (M*(Y+W)) (M*Y+two*E) :=
    le_congr (congrMul (.eqRefl M) he) (by dsimp only [Y,F,E]; ipra_ring) h.andE₂.andE₂
  have delta : Γ ⊢[PRAAx] le (M*W) (two*E) := by ipra_le sl upper
  have hF := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) L
  have hE := positive_product F D hF hD
  have hprefix := represents_rescale (prefixValue k M L) a F D (ofGaussian_represents _ _ hF)
  have htarget := GaussianRationalSyntheticDivision.rescale_to (targetPoint Q D) b D F E
    (ofGaussian_represents _ _ hD) (mul_comm _ _)
  have norm : Γ ⊢[PRAAx] normSq (GaussianRootAlgebra.sub (scale D a) (scale F b)) ≐ W*W := by
    have clear := natEq he
    apply deriveNat
    dsimp only [a,b,X,Y,F] at clear ⊢
    simp only [normSq_eval,re_sub,im_sub,re_scale,im_scale,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    linear_combination (2*𝔞 D*𝔞 (total k M L)-𝔞 Q*𝔞 (fact L)+𝔞 W)*clear
  apply (bounded_difference_iff _ _ _ _ E two M hE hs.andE₁ hprefix htarget).iffMpr
  exact le_congr ((by ipra_ring : Γ ⊢[PRAAx] (M*W)*(M*W) ≐ (M*M)*(W*W)).eqTrans
    (congrMul (.eqRefl _) norm.eqSymm)) (by ipra_ring) (le_mul_mono delta delta)

theorem actual_rational_arctangent_target_brackets_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 2) (var 3) ⋏ le one (var 1)) ⟶
      (le (two*var 1) (var 3) ⋏ le (var 0*fact (var 3)) ((two*var 1)*total (var 2) (var 2) (var 3))) ⟶
      brackets (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (rational_target_brackets _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

theorem actual_rational_arctangent_target_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 2) (var 3) ⋏ le one (var 1)) ⟶
      (le (two*var 1) (var 3) ⋏ le (var 0*fact (var 3)) ((two*var 1)*total (var 2) (var 2) (var 3))) ⟶
      distanceBounded (prefixValue (chosen (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3))
        (targetPoint (var 0) (var 1)) two (var 2)) :=
  closeUniv 4 (.impI (.impI (rational_target_distance _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianArctangentRationalTarget
