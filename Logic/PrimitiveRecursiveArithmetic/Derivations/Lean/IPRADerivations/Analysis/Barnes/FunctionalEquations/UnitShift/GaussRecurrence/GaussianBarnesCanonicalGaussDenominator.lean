import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.FiniteProducts.GaussianBarnesCanonicalPolynomialShift
import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerDenominator

/-!
# The Barnes plain polynomial is the original Euler denominator

The polynomial in the cleared unit shift is the original Gamma Euler
denominator evaluated at the translated argument. At a positive cutoff
`N+1` it is exactly `N!` times the original normalized Euler head at `N`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalGaussDenominator

open_ipra
open GaussianBarnesCanonicalDeflatedFactor (translatedValue)
open GaussianBarnesCanonicalPolynomialShift (plain rowF row_at)
open GaussianBarnesWeightedProductShift (unweighted)
open GaussianGammaEulerDenominator (denominator linearBody linear_at denominator_normalization)
open GaussianGammaEulerHeadLower (translated)
open GaussianRationalFiniteProduct (product_congr_bounded)
open GaussianRationalHorner (canonical_unique ofGaussian_canonical ofGaussian_represents represents_congr qmul)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem translated_index (z B i : PTm n) : Γ ⊢[PRAAx]
    equal (translated z B (succ i)) (translated (translated z B one) B i) := by
  apply equal_of_values <;> simp only [translated,re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring

theorem denominator_cross (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    plain z B N ≐ denominator (translated z B one) B N := by
  apply product_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let Z := Syn.shift z
  let B' := Syn.shift B
  let w := translated Z B' one
  let i : PTm (n+1) := var 0
  let a := translated Z B' (succ i)
  let b := translated w B' i
  have hb : Δ ⊢[PRAAx] le one B' := by simpa [Fm.shift,Syn.shift,one,Δ,B'] using hB.shift.wk
  have e : Δ ⊢[PRAAx] translatedValue Z B' (succ i) ≐ GaussianGammaEulerHeadShift.linear w B' i :=
    canonical_unique _ _ b B' (ofGaussian_canonical a B' hb) (ofGaussian_canonical b B' hb) hb
      (represents_congr (.eqRefl _) (translated_index Z B' i) (.eqRefl _) (ofGaussian_represents a B' hb))
      (ofGaussian_represents b B' hb)
  simpa [unweighted,inst2,Syn.shift,Δ,Z,B',i,w,one] using
    (row_at (Γ := Δ) Z B' i).eqTrans (e.eqTrans (linear_at i w B').eqSymm)

theorem original_head (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    plain z B (succ N) ≐ qmul (naturalPoint (fact N)) (GaussianGammaEulerHead.run (translated z B one) B N) :=
  (denominator_cross z B (succ N) hB).eqTrans ((denominator_normalization (translated z B one) B N hB).eqTrans
    (qmul_congr (.eqRefl _) (GaussianGammaEulerHead.program_at _ _ _).eqSymm))

theorem actual_Barnes_plain_product_is_original_Gauss_denominator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let z := var 0
     let B := var 1
     let N := var 2
     le one B ⟶ plain z B (succ N) ≐ qmul (naturalPoint (fact N)) (GaussianGammaEulerHead.run (translated z B one) B N)) :=
  closeUniv 3 (.impI (original_head _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalGaussDenominator
