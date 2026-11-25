import IPRADerivations.Analysis.GaussianLogGammaEulerArgumentIncrement
import IPRADerivations.Analysis.GaussianLogGammaEulerReciprocalSlope
import IPRADerivations.Analysis.GaussianLogGammaEulerRepresentation

/-!
# The literal first-order rows of the finite Euler logarithm

The reciprocal slope's rational translation is exactly the encoded
argument of the original logarithm row. Multiplying every reciprocal
row by the actual displacement and summing gives the displacement times
the original finite reciprocal sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerLinearSlope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode eval_re_code eval_im_code)
open GaussianLogGammaEulerArgumentIncrement (step subst_step)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerReciprocalSlope (shiftedPoint reciprocalSum)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameReciprocal (reciprocal_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (represents ofGaussian_represents ofGaussian_canonical canonical_unique
  qadd_canonical qadd_represents represents_rescale represents_congr qmul)
open GaussianRationalReciprocal (reciprocal)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale re_one im_one)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "reciprocalBody" => GaussianLogGammaEulerReciprocalSlope.rowBody

theorem shifted_point (A B D neg k : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] shiftedPoint (argument A B D neg) k ≐ argument (A + k * D) B D neg := by
  let x := argument A B D neg
  let y := argument (A + k * D) B D neg
  let z := native A B neg
  let w := native (A + k * D) B neg
  let integer := fraction k one
  let u := scale (k * D) oneCode
  have integerNative : Γ ⊢[PRAAx] equal (scale D (scale k oneCode)) u := by
    apply equal_of_values <;> simp only [u, re_scale, im_scale, re_one, im_one] <;> ipra_simps <;> ring
  have integerRep : Γ ⊢[PRAAx] represents integer u D :=
    represents_congr (.eqRefl _) integerNative (one_mul D)
      (represents_rescale integer (scale k oneCode) one D (ofGaussian_represents _ _ (le_refl one)))
  have nativeSum : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.add u z) w := by
    apply equal_of_values
    · simp only [u, z, w, native, re_add, re_scale, re_one, eval_re_code, ZT.toZ_ofNat]
      ipra_simps
      ring
    · simp only [u, z, w, native, im_add, im_scale, im_one, eval_im_code]
      ring
  have sumRep := qadd_represents integer x u z D hD integerRep (ofGaussian_represents z D hD)
  exact canonical_unique (shiftedPoint x k) y w D (qadd_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) nativeSum (.eqRefl D) sumRep) (ofGaussian_represents w D hD)

def rowBody : PTm 2 := multiplyBody reciprocalBody

def rowData (A B neg a b sign D : PTm n) : PTm n :=
  pairT (step A B neg a b sign D) (argument A B D neg)

def linearSum (A B neg a b sign D N : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum rowBody (succ N) (rowData A B neg a b sign D)

@[simp] theorem subst_rowData {m : ℕ} (σ : Fin n → PTm m) (A B neg a b sign D : PTm n) :
    Syn.subst σ (rowData A B neg a b sign D) =
      rowData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ neg) (Syn.subst σ a) (Syn.subst σ b)
        (Syn.subst σ sign) (Syn.subst σ D) := by
  simp only [rowData, subst_pairT, subst_step, subst_argument]

theorem row_at (k A B neg a b sign D : PTm n) :
    Γ ⊢[PRAAx] inst2 rowBody k (rowData A B neg a b sign D) ≐
      qmul (step A B neg a b sign D) (reciprocal (shiftedPoint (argument A B D neg) k)) :=
  (multiply_body_at reciprocalBody (step A B neg a b sign D) k (argument A B D neg)).eqTrans
    (qmul_congr (.eqRefl _) (GaussianLogGammaEulerReciprocalSlope.row_at (argument A B D neg) k))

theorem row_shifted_at (k A B neg a b sign D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] inst2 rowBody k (rowData A B neg a b sign D) ≐
      qmul (step A B neg a b sign D) (reciprocal (argument (A + k * D) B D neg)) :=
  (row_at k A B neg a b sign D).eqTrans
    (qmul_congr (.eqRefl _) (reciprocal_congr (shifted_point A B D neg k hD)))

theorem sum_value (A B neg a b sign D N : PTm n) :
    Γ ⊢[PRAAx] linearSum A B neg a b sign D N ≐
      qmul (step A B neg a b sign D) (reciprocalSum A B D neg (succ N)) :=
  sum_multiply reciprocalBody (step A B neg a b sign D) (succ N) (argument A B D neg)

theorem actual_Euler_logarithm_linear_reciprocal_sum_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (linearSum (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
        qmul (step (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
          (reciprocalSum (var 0) (var 1) (var 6) (var 2) (succ (var 7)))) :=
  closeUniv 8 (sum_value _ _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerLinearSlope
