import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryCofinalLogDerivative

/-!
# Cleared partial fractions for the original hyperbolic cotangent

For the rational input (x=A/B), the actual original names satisfy
`(πx) cosh(πx) = sinh(πx) (1 + x·Σ 2x/(j²+x²))`.
The row sum is the checked cofinal sum of the original logarithmic
derivative rows, with (j) starting at one.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryCothExpansion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_one multiply_associative multiply_commutative distributive)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianSineProductImaginaryCofinalDerivative (sineData)
open GaussianSineProductImaginaryCoshIdentity (coshF coshData cosh_regular)
open GaussianSineProductImaginaryHyperbolic (expF expData sinhF sinhData)
open GaussianSineProductImaginaryLogDerivative (rationalReal)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Scale" => GaussianPiRationalScale.nameF
local notation "Product" => GaussianSineProductName.nameF
local notation "Rows" => GaussianSineProductImaginaryLogDerivativeTail.nameF
local notation "rowData" => GaussianSineProductImaginaryLogDerivativeTail.data
local notation "sumF" => GaussianSineProductImaginaryHyperbolicProductRule.sumF
local notation "sumData" => GaussianSineProductImaginaryHyperbolicProductRule.sumData

def weightedRowsF : PR 2 := multiplyF constantF Rows
def weightedRowsData (A B R : PTm n) : PTm n := multiplyData constantF Rows (rationalReal A B) (rowData A B R)
def factorF : PR 2 := addF oneF weightedRowsF
def factorData (A B R : PTm n) : PTm n := addData (sineData A B R) (weightedRowsData A B R)

private theorem rearrange (f g h : PR 2) (a b c : PTm n) (hf : Γ ⊢[PRAAx] pointCN f a)
    (hg : Γ ⊢[PRAAx] pointCN g b) (hh : Γ ⊢[PRAAx] pointCN h c) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (multiplyF g h)) (multiplyF g (multiplyF f h))
      (multiplyData f (multiplyF g h) a (multiplyData g h b c))
      (multiplyData g (multiplyF f h) b (multiplyData f h a c)) := by
  have e := multiply_cross (multiplyF f g) (multiplyF g f) h h _ _ c c
    (multiply_fast _ _ _ _ hf hg) (multiply_fast _ _ _ _ hg hf) hh hh (multiply_commutative f g a b hf hg)
    (cross_refl _ _ hh)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative f g h a b c hf hg hh))
    (cross_trans _ _ _ _ _ _ e (multiply_associative g f h b a c hg hf hh))

theorem factor_regular (A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN factorF (factorData A B R) :=
  add_fast _ _ _ _ (one_fast _) (multiply_fast _ _ _ _ (constant_regular _)
    (GaussianSineProductImaginaryLogDerivativeTail.regular A B R hB hA))

theorem factor_product_derivative (A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent sumF (multiplyF Product factorF) (sumData A B R)
      (multiplyData Product factorF (sineData A B R) (factorData A B R)) := by
  let a := rationalReal A B
  let p := sineData A B R
  let s := rowData A B R
  let v := weightedRowsData A B R
  let y := GaussianSineProductImaginaryHyperbolicProductRule.linearData A B R
  let F := GaussianSineProductImaginaryHyperbolicProductRule.linearF
  have ha := constant_regular (Γ := Γ) a
  have hp := GaussianSineProductName.name_regular _ _ _ hB (GaussianSineProductImaginaryFirstOrderBound.axis_disk A B R hA)
  have hs := GaussianSineProductImaginaryLogDerivativeTail.regular A B R hB hA
  have hy : Γ ⊢[PRAAx] pointCN F y := multiply_fast _ _ _ _ ha (multiply_fast _ _ _ _ hp hs)
  have hw : Γ ⊢[PRAAx] pointCN weightedRowsF v := multiply_fast _ _ _ _ ha hs
  have move := rearrange constantF Product Rows a p s ha hp hs
  have unit := multiply_one Product p hp
  have sum := add_cross Product (multiplyF Product oneF) F (multiplyF Product weightedRowsF) p
    (multiplyData Product oneF p p) y (multiplyData Product weightedRowsF p v)
    hp (multiply_fast _ _ _ _ hp (one_fast p)) hy (multiply_fast _ _ _ _ hp hw) (cross_symm _ _ _ _ unit) move
  exact cross_trans _ _ _ _ _ _ sum (cross_symm _ _ _ _ (distributive Product oneF weightedRowsF p p v hp (one_fast p) hw))

def leftF : PR 2 := multiplyF Scale coshF
def leftData (A B R x : PTm n) : PTm n := multiplyData Scale coshF (GaussianPiRationalScale.data false A B R x) (coshData A B R x)
def rightF : PR 2 := multiplyF sinhF factorF
def rightData (A B R x : PTm n) : PTm n := multiplyData sinhF factorF (sinhData A B R x) (factorData A B R)

theorem cleared_expansion (A B R x : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le (A+one) (R*B)) : Γ ⊢[PRAAx]
    crossEquivalent leftF rightF (leftData A B R x) (rightData A B R x) := by
  let z := GaussianPiRationalScale.data false A B R x
  let p := sineData A B R
  let f := factorData A B R
  have ha := le_trans (le_add_right A one) hA
  have hz := GaussianPiRationalScale.regular false A B R x hB ha
  have hp := GaussianSineProductName.name_regular _ _ _ hB (GaussianSineProductImaginaryFirstOrderBound.axis_disk A B R ha)
  have hf := factor_regular A B R hB ha
  have hc := cosh_regular A B R x hB ha
  have exp (s : Bool) := GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianPiRationalScale.exponential_input s A B R x hB ha)
  have sinh : Γ ⊢[PRAAx] pointCN sinhF (sinhData A B R x) := multiply_fast _ _ _ _ (constant_regular _)
    (GaussianNamedDifference.name_regular _ _ _ _ (exp true) (exp false))
  have factor := cross_trans _ _ _ _ _ _
    (GaussianSineProductImaginaryCofinalLogDerivative.cosh_as_product_and_derivative A B R x hR hB hA)
    (factor_product_derivative A B R hB ha)
  have left := multiply_cross Scale Scale coshF (multiplyF Product factorF) z z _ _ hz hz hc
    (multiply_fast _ _ _ _ hp hf) (cross_refl _ _ hz) factor
  have right := multiply_cross (multiplyF Scale Product) sinhF factorF factorF _ _ f f
    (multiply_fast _ _ _ _ hz hp) sinh hf hf
    (cross_symm _ _ _ _ (GaussianSineProductImaginaryHyperbolic.sinh_as_product A B R x hR hB ha))
    (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ left
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative Scale Product factorF z p f hz hp hf)) right)

theorem actual_cleared_hyperbolic_cotangent_partial_fractions_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 2) ⋏ (le one (var 1) ⋏ le (var 0+one) (var 2*var 1))) ⟶
        crossEquivalent leftF rightF (leftData (var 0) (var 1) (var 2) (var 3)) (rightData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (cleared_expansion _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryCothExpansion
