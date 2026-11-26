import IPRADerivations.Analysis.Gamma.GaussianGammaFoldedExponentBalance
import IPRADerivations.Analysis.Exponential.GaussianExponentialAddition
import IPRADerivations.Analysis.Exponential.GaussianExponentialRadiusIndependence

/-!
# The two folded C8 identities

The checked exponential addition law is compatible with all of the
actual disks chosen separately by the input names. Multiplying by the
identical polynomial head gives the two folded C8 product identities
without any apartness assumption.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFoldedApproximantBalance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiply_fast multiply_equivalent)
open GaussianRadiusExponentialName (input nameF data name_regular)
open GaussianExponentialRadiusIndependence (input_widen same_input_cross independent_radii_proper)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_to_diagonal cross_refl diagonal_refl)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular productF productData product_regular exponentF)
open GaussianGammaFiniteApproximantName (pF pData qF qData logExponentF logExponentData log_exponent_regular
  approximantF approximantData exponential_input exponentialInputData)
open GaussianGammaFoldedExponentBalance (correctionF correctionData correction_fast balanced_exponents)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exponential_product_equivalent (f g h : PR 2) (R S T x y z : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y) (hh : Γ ⊢[PRAAx] input h T z)
    (he : Γ ⊢[PRAAx] crossEquivalent (addF f g) h (addData x y) z) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (nameF f) (nameF g)) (nameF h)
      (multiplyData (nameF f) (nameF g) (data R x) (data S y)) (data T z) := by
  let U := R+S+one
  have hU : Γ ⊢[PRAAx] le one U :=
    le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _)
  have hfU := input_widen f R U x hf (le_trans (le_add_right R S) (le_add_right _ _))
  have hgU := input_widen g S U y hg
    (le_trans (le_congr (.eqRefl _) (add_comm _ _) (le_add_right S R)) (le_add_right _ _))
  have p := multiply_equivalent (nameF f) (nameF f) (nameF g) (nameF g) (data R x) (data U x) (data S y) (data U y)
    (name_regular f R x hf) (name_regular f U x hfU) (name_regular g S y hg) (name_regular g U y hgU)
    (cross_to_diagonal _ _ _ _ (same_input_cross f R U x hf hfU))
    (cross_to_diagonal _ _ _ _ (same_input_cross g S U y hg hgU))
  have a := GaussianExponentialAddition.exponential_add_cross f g U x y hU hfU hgU
  have b := independent_radii_proper (addF f g) h (U+U) T (addData x y) z
    (GaussianExponentialReference.add_input f g U x y hfU hgU) hh he
  exact cross_trans _ _ _ _ _ _ p (cross_trans _ _ _ _ _ _ a b)

/-- Transport a factorized exponent through the actual, shared polynomial head. -/
theorem approximant_product_equivalent (f g h : PR 2) (x y t z B N : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h t)
    (he : Γ ⊢[PRAAx] crossEquivalent (addF f g) h (addData x y) t) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (approximantF f) (nameF g)) (approximantF h)
      (multiplyData (approximantF f) (nameF g) (approximantData f x z B N) (exponentialInputData g y))
      (approximantData h t z B N) := by
  let H := GaussianGammaEulerHead.run z B N
  let X := exponentialInputData f x
  let Y := exponentialInputData g y
  let Z := exponentialInputData h t
  let F := nameF f
  let G := nameF g
  let T := nameF h
  have hfI := exponential_input f x hf
  have hgI := exponential_input g y hg
  have hhI := exponential_input h t hh
  have a : Γ ⊢[PRAAx] crossEquivalent (multiplyF F G) T (multiplyData F G X Y) Z :=
    exponential_product_equivalent f g h _ _ _ x y t hfI hgI hhI he
  have hX : Γ ⊢[PRAAx] pointCN F X := name_regular _ _ _ hfI
  have hY : Γ ⊢[PRAAx] pointCN G Y := name_regular _ _ _ hgI
  have hZ : Γ ⊢[PRAAx] pointCN T Z := name_regular _ _ _ hhI
  have hH : Γ ⊢[PRAAx] pointCN constantF H := constant_regular H
  have assoc := GaussianNameRingLaws.multiply_associative constantF F G H X Y hH hX hY
  have mul := multiply_equivalent constantF constantF (multiplyF F G) T H H (multiplyData F G X Y) Z
    hH hH (multiply_fast F G X Y hX hY) hZ (diagonal_refl constantF H) (cross_to_diagonal _ _ _ _ a)
  exact cross_trans _ _ _ _ _ _ assoc mul

def correctionExpF : PR 2 := nameF correctionF
def correctionExpData (z B N : PTm n) : PTm n := exponentialInputData correctionF (correctionData z B N)
def eulerProductF : PR 2 := multiplyF pF correctionExpF
def eulerProductData (z B N : PTm n) : PTm n :=
  multiplyData pF correctionExpF (pData z B N) (correctionExpData z B N)

theorem euler_factor_identity (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent qF eulerProductF (qData z B N) (eulerProductData z B N) :=
  cross_symm _ _ _ _ (approximant_product_equivalent productF correctionF logExponentF
    (productData z B N) (correctionData z B N) (logExponentData z B N) z B N
    (product_regular z B N) (correction_fast z B N hN) (log_exponent_regular z B N hN)
    (balanced_exponents z B N hN))

def tailExpF : PR 2 := nameF GaussianGammaCanonicalTailName.pointF
def tailExpData (z R B N : PTm n) : PTm n :=
  exponentialInputData GaussianGammaCanonicalTailName.pointF (GaussianGammaCanonicalTailName.data z R B N)
def tailProductF : PR 2 := multiplyF pF tailExpF
def tailProductData (z R B N : PTm n) : PTm n :=
  multiplyData pF tailExpF (pData z B N) (tailExpData z R B N)

theorem tail_factor_identity (z R B N : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaCutoffName.nameF tailProductF
      (GaussianGammaCutoffName.data z R B N) (tailProductData z R B N) :=
  cross_symm _ _ _ _
    (approximant_product_equivalent productF GaussianGammaCanonicalTailName.pointF exponentF
      (productData z B N) (GaussianGammaCanonicalTailName.data z R B N)
      (GaussianGammaCutoffName.exponentData z R B N) z B N (product_regular z B N)
      (GaussianGammaCanonicalTailName.name_regular z R B N hs)
      (GaussianGammaCutoffName.exponent_regular z R B N hs)
      (cross_refl _ _ (GaussianGammaCutoffName.exponent_regular z R B N hs)))

theorem original_folded_euler_C8_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ crossEquivalent qF eulerProductF (qData (var 0) (var 1) (var 2))
      (eulerProductData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (euler_factor_identity _ _ _ Prf.hyp0))

theorem original_folded_tail_C8_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaCanonicalTailName.source (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent GaussianGammaCutoffName.nameF tailProductF
        (GaussianGammaCutoffName.data (var 0) (var 1) (var 2) (var 3))
        (tailProductData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (tail_factor_identity _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFoldedApproximantBalance
