import IPRADerivations.Analysis.GaussianBarnesCanonicalFactor
import IPRADerivations.Analysis.GaussianGammaNameConjugation
import IPRADerivations.Core.CongruenceTactic

/-!
# Conjugation of each original Barnes factor

Conjugation commutes with the rational base power and with the exact
correction in the exponential. The original named product has the
corresponding symmetry even at a zero factor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFactorConjugation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalFactor
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNameConjugation (constant_name_conjugate)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianRationalConjugation (point point_add point_mul point_one point_power point_sub of_gaussian)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalReciprocal (conjugate power)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Conj" => GaussianNameConjugation.nameF
local notation "Exp" => GaussianRadiusExponentialName.nameF

theorem conjugate_source (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] source (conjugate z) R B k :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (GaussianGammaFiniteConjugation.native_disk z (R*B) h.andE₂.andE₂))

theorem base_equal (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] point (base z B k) ≐ base (conjugate z) B k :=
  (point_add _ _).eqTrans (qadd_congr point_one (of_gaussian z (B*k) (positive_product _ _ hB hk)))

theorem power_equal (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] point (powerValue z B k) ≐ powerValue (conjugate z) B k := by
  refine (point_power (base z B k) k).eqTrans ?_
  show Γ ⊢[PRAAx] power (point (base z B k)) k ≐ power (base (conjugate z) B k) k
  ipra_congr (power (var 0) (var 1) : PTm 2) with [base_equal z B k hB hk, .eqRefl k]

theorem correction_equal (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] point (correction z B k) ≐ correction (conjugate z) B k := by
  let a := ofGaussian z B
  let b := ofGaussian z (two*(B*k))
  have u := of_gaussian z B hB
  have v := of_gaussian z (two*(B*k)) (positive_product _ _ (le_succ_self one) (positive_product _ _ hB hk))
  exact (point_sub _ _).eqTrans (qsub_congr ((point_mul a b).eqTrans (qmul_congr u v)) u)

theorem factor_cross (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] crossEquivalent (Conj nameF) nameF (data z R B k) (data (conjugate z) R B k) := by
  let w := conjugate z
  let S := exponentRadius R
  let x := correction z B k
  let y := correction w B k
  let a := powerValue z B k
  let b := powerValue w B k
  let X := exponentialData z R B k
  let Y := exponentialData w R B k
  have hs := conjugate_source z R B k h
  have hx := exponential_input z R B k h
  have hy := exponential_input w R B k hs
  have hr := GaussianRadiusExponentialName.name_regular constantF S x hx
  have ht := GaussianRadiusExponentialName.name_regular constantF S y hy
  have he := GaussianRadiusExponentialName.cross_proper (Conj constantF) constantF S x y
    (GaussianNameConjugation.exponential_input constantF S x hx) hy
    (constant_name_conjugate x y (correction_equal z B k h.andE₁ h.andE₂.andE₁))
  have exp := cross_trans (Conj exponentialF) (Exp (Conj constantF)) exponentialF X X Y
    (GaussianNameConjugation.exponential_cross constantF S x hx) he
  have first := GaussianNameConjugation.multiply_cross constantF exponentialF a X (constant_regular a) hr
  have last := GaussianGammaAdjacentCutoff.multiply_cross (Conj constantF) constantF (Conj exponentialF) exponentialF
    a b X Y (GaussianNameConjugation.regular _ _ (constant_regular a)) (constant_regular b)
    (GaussianNameConjugation.regular _ _ hr) ht
    (constant_name_conjugate a b (power_equal z B k h.andE₁ h.andE₂.andE₁)) exp
  exact cross_trans (Conj nameF) (multiplyF (Conj constantF) (Conj exponentialF)) nameF
    (data z R B k) (multiplyData (Conj constantF) (Conj exponentialF) a X) (data w R B k) first last

theorem actual_Barnes_canonical_factor_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let k := var 3
     source z R B k ⟶ crossEquivalent (Conj nameF) nameF (data z R B k) (data (conjugate z) R B k)) :=
  closeUniv 4 (.impI (factor_cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFactorConjugation
