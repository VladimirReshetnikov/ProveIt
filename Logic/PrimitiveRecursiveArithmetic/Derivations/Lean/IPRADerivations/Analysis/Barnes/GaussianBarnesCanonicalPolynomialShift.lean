import IPRADerivations.Analysis.Barnes.GaussianBarnesWeightedProductShift
import IPRADerivations.Analysis.Barnes.Deflation.GaussianBarnesCanonicalDeflatedFactor
import IPRADerivations.Core.CongruenceTactic

/-!
# The shifted polynomial factors of the original Barnes product

After taking out the index-dependent reciprocal powers of the original
bases, the polynomial factors are ((z+k)^k). The division-free
finite shift leaves the ordinary Gamma denominator product and only
the power at the upper endpoint.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPolynomialShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesWeightedProductShift (weighted shifted unweighted shift_product)
open GaussianBarnesCanonicalDeflatedFactor (translatedValue)
open GaussianGammaEulerHeadLower (translated)
open GaussianRationalFiniteProduct (qprod product_congr_bounded)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (qmul ofGaussian_canonical ofGaussian_represents canonical_unique represents_congr)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (z B : PTm n) : PTm n := pairT z B
def rowF : PR 2 := PTm.toPR (translatedValue (fstT (var 1)) (sndT (var 1)) (succ (var 0)) : PTm 2)
def polynomial (z B N : PTm n) : PTm n := qprod (weighted rowF) N (data z B)
def plain (z B N : PTm n) : PTm n := qprod (unweighted rowF) N (data z B)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (data z B) = data (Syn.subst σ z) (Syn.subst σ B) := by simp [data]

@[local simp] private theorem subst_translatedValue {m : ℕ} (σ : Fin n → PTm m) (z B i : PTm n) :
    Syn.subst σ (translatedValue z B i) =
      translatedValue (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ i) := by
  simp [translatedValue,translated,ComplexLogarithmRemainder.oneCode,one]

theorem row_at (z B i : PTm n) : Γ ⊢[PRAAx] ap2 rowF i (data z B) ≐ translatedValue z B (succ i) := by
  let x := data z B
  have read : Γ ⊢[PRAAx] ap2 rowF i x ≐ translatedValue (fstT x) (sndT x) (succ i) := by
    simpa [rowF,ap2,translatedValue] using
      toPR_eq (Γ := Γ) (translatedValue (fstT (var 1)) (sndT (var 1)) (succ (var 0)) : PTm 2) ![i,x]
  refine read.eqTrans ?_
  dsimp only [x,data]
  ipra_congr (translatedValue (var 0) (var 1) (var 2) : PTm 3) with
    [fst_pair z B, snd_pair z B, .eqRefl (succ i)]

theorem translate_succ (z B i : PTm n) : Γ ⊢[PRAAx]
    equal (translated (translated z B one) B (succ i)) (translated z B (succ (succ i))) := by
  apply equal_of_values <;> simp only [translated,re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring

theorem shifted_row_equal (z B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    ap2 rowF (succ i) (data z B) ≐ ap2 rowF i (data (translated z B one) B) := by
  let a := translated (translated z B one) B (succ i)
  let b := translated z B (succ (succ i))
  have e : Γ ⊢[PRAAx] translatedValue (translated z B one) B (succ i) ≐ translatedValue z B (succ (succ i)) :=
    canonical_unique _ _ b B (ofGaussian_canonical a B hB) (ofGaussian_canonical b B hB) hB
      (represents_congr (.eqRefl _) (translate_succ z B i) (.eqRefl _) (ofGaussian_represents a B hB))
      (ofGaussian_represents b B hB)
  exact (row_at z B (succ i)).eqTrans (e.eqSymm.eqTrans (row_at (translated z B one) B i).eqSymm)

theorem shifted_product (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qprod (shifted rowF) N (data z B) ≐ polynomial (translated z B one) B N := by
  apply product_congr_bounded
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hb : Δ ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hB.shift.wk
  have row := shifted_row_equal (Γ := Δ) (sh z) (sh B) (var 0) hb
  simpa [shifted,weighted,inst2,power,Syn.shift,sh,Δ,GaussianGammaEulerHeadLower.translated,one] using
    congrAp2 powerF (.eqRefl (succ (var 0))) row

theorem polynomial_shift (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (polynomial (translated z B one) B N) (plain z B N) ≐
      qmul (polynomial z B N) (power (translatedValue z B (succ N)) N) :=
  (qmul_congr (shifted_product z B N hB).eqSymm (.eqRefl _)).eqTrans
    ((shift_product rowF N (data z B)).eqTrans
      (qmul_congr (.eqRefl _) (congrAp2 powerF (.eqRefl N) (row_at z B N))))

theorem actual_Barnes_polynomial_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let z := var 0
     let B := var 1
     let N := var 2
     le one B ⟶ qmul (polynomial (translated z B one) B N) (plain z B N) ≐
       qmul (polynomial z B N) (power (translatedValue z B (succ N)) N)) :=
  closeUniv 3 (.impI (polynomial_shift _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPolynomialShift
