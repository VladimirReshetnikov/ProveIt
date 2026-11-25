import IPRADerivations.Analysis.GaussianNameArithmetic
import IPRADerivations.Analysis.GaussianRationalConjugation
import IPRADerivations.Analysis.GaussianRationalNaturalScale

/-!
# Gaussian rational norm-square values

Conjugate multiplication is the embedded squared norm. It
commutes with actual multiplication and has a finite Lipschitz
bound on pairs of bounded observations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalNormSquareTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq mul)
open GaussianRationalConjugation (point point_mul point_represents point_bound point_distance point_embed)
open GaussianRationalHorner (qmul qmul_represents qmul_canonical canonical_unique represents_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (bounded distanceBounded qnormSq qnormSq_represents)
open GaussianRationalPowerAlgebra (qmul_shuffle)
open GaussianRationalReciprocal (qone conjugate re_conjugate im_conjugate)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianNameArithmetic (product_distance)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul)
open RationalGaussianEmbedding (embed embed_canonical embed_from_representation native)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (q : PTm n) : PTm n := qmul q (point q)

@[simp] theorem subst_value {L : ℕ} (σ : Fin n → PTm L) (q : PTm n) :
    Syn.subst σ (value q) = value (Syn.subst σ q) := by simp [value]

theorem value_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) :
    Γ ⊢[PRAAx] value q ≐ value r :=
  qmul_congr h (GaussianRationalConjugation.point_congr h)

theorem product_value (q r : PTm n) :
    Γ ⊢[PRAAx] value (qmul q r) ≐ qmul (value q) (value r) :=
  (qmul_congr (.eqRefl _) (point_mul q r)).eqTrans (qmul_shuffle _ _ _ _)

theorem embed_value (q : PTm n) :
    Γ ⊢[PRAAx] value (embed q) ≐ qmul (embed q) (embed q) :=
  qmul_congr (.eqRefl _) (point_embed q)

private theorem native_norm_square (a : PTm n) :
    Γ ⊢[PRAAx] equal (mul a (conjugate a)) (native (ZT.ofNat (normSq a))) := by
  apply equal_of_values <;>
    simp only [re_mul,im_mul,re_conjugate,im_conjugate,native,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat,ComplexLogarithmRemainder.normSq_eval] <;>
    (try ipra_simps) <;> ring

theorem actual_squared_norm (q : PTm n) :
    Γ ⊢[PRAAx] value q ≐ embed (qnormSq q) := by
  let a := rawGaussian q
  let E := rawDen q
  have hE := raw_den_positive (Γ := Γ) q
  have h := raw_represents (Γ := Γ) q
  have l := qmul_represents q (point q) a (conjugate a) E E hE hE h (point_represents _ _ _ hE h)
  have r := embed_from_representation _ _ _ (qnormSq_represents q a E hE h)
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (embed_canonical _)
    (GaussianRationalHorner.positive_product _ _ hE hE)
    (represents_congr (.eqRefl _) (native_norm_square a) (.eqRefl _) l) r

theorem distance (q r A B C D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] bounded q A one) (hr : Γ ⊢[PRAAx] bounded r B one)
    (h : Γ ⊢[PRAAx] distanceBounded q r C D) :
    Γ ⊢[PRAAx] distanceBounded (value q) (value r) ((A+B)*C) D :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (product_distance q r (point q) (point r) C C D A B hD h
      (point_distance q r C D hD h) (point_bound _ _ _ (le_refl one) hq) hr)

theorem actual_product_norm_square_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (value (qmul (var 1) (var 0)) ≐ qmul (value (var 1)) (value (var 0))) :=
  closeUniv 2 (product_value _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalNormSquareTransport
