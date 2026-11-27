import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifferenceAlgebra
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-! The original native divided quotient commutes with named difference.
Independent bounds on the two divided quotients therefore add. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasDifferenceQuotientAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianNameArithmetic (multiply_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_to_diagonal)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "Q" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data

theorem quotient_difference (f g : PR 2) (x x₀ y y₀ h B : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hf₀ : Γ ⊢[PRAAx] pointCN f x₀)
    (hg : Γ ⊢[PRAAx] pointCN g y) (hg₀ : Γ ⊢[PRAAx] pointCN g y₀) :
    Γ ⊢[PRAAx] crossEquivalent (Q (Diff f g) (Diff f g)) (Diff (Q f f) (Q g g))
      (qd (Diff f g) (Diff f g) (dd x y) (dd x₀ y₀) h B) (dd (qd f f x x₀ h B) (qd g g y y₀ h B)) := by
  let F := Diff f g
  let G := Diff f f
  let H := Diff g g
  let a := dd x y
  let b := dd x₀ y₀
  let c := dd x x₀
  let d := dd y y₀
  let s := GaussianNamedDifferenceQuotient.inverse h B
  have ha := GaussianNamedDifference.name_regular f g x y hf hg
  have hb := GaussianNamedDifference.name_regular f g x₀ y₀ hf₀ hg₀
  have hc := GaussianNamedDifference.name_regular f f x x₀ hf hf₀
  have hd := GaussianNamedDifference.name_regular g g y y₀ hg hg₀
  have hs := constant_regular (Γ := Γ) s
  have reorder := GaussianNamedDifferenceAlgebra.shuffle f g f g x y x₀ y₀ hf hg hf₀ hg₀
  have first := multiply_equivalent constantF constantF (Diff F F) (Diff G H)
    s s (dd a b) (dd c d) hs hs (GaussianNamedDifference.name_regular F F a b ha hb)
    (GaussianNamedDifference.name_regular G H c d hc hd)
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ hs)) (cross_to_diagonal _ _ _ _ reorder)
  exact cross_trans _ _ _ _ _ _ first
    (GaussianNamedDifferenceAlgebra.distribute constantF G H s c d hs hc hd)

theorem dyadic_rate (f g u v : PR 2) (x x₀ y y₀ a b h B p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hf₀ : Γ ⊢[PRAAx] pointCN f x₀)
    (hg : Γ ⊢[PRAAx] pointCN g y) (hg₀ : Γ ⊢[PRAAx] pointCN g y₀)
    (hu : Γ ⊢[PRAAx] pointCN u a) (hv : Γ ⊢[PRAAx] pointCN v b)
    (hs : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B)
    (aRate : Γ ⊢[PRAAx] independentRate (Q f f) u (qd f f x x₀ h B) a one (unit p))
    (bRate : Γ ⊢[PRAAx] independentRate (Q g g) v (qd g g y y₀ h B) b one (unit p)) :
    Γ ⊢[PRAAx] independentRate (Q (Diff f g) (Diff f g)) (Diff u v)
      (qd (Diff f g) (Diff f g) (dd x y) (dd x₀ y₀) h B) (dd a b) two (unit p) := by
  let U := unit p
  let F := Diff f g
  let L := Diff (Q f f) (Q g g)
  let G := Diff u v
  let s := qd f f x x₀ h B
  let t := qd g g y y₀ h B
  let M := GaussianNamedDifferenceRate.leadingNumerator one U one U
  let D := GaussianNamedDifferenceRate.leadingDenominator U U
  have hU := unit_positive (Γ := Γ) p
  have hD := positive_product U U hU hU
  have r₁ := GaussianNamedDifferenceQuotient.name_regular f f x x₀ h B (.andI hf (.andI hf₀ hs))
  have r₂ := GaussianNamedDifferenceQuotient.name_regular g g y y₀ h B (.andI hg (.andI hg₀ hs))
  have r₃ := GaussianNamedDifference.name_regular u v a b hu hv
  have raw := GaussianNamedDifferenceRate.original_rate (Q f f) (Q g g) u v s t a b one U one U
    (.andI (.andI hU hU) (.andI (.andI r₁ r₂) (.andI (.andI hu hv) (.andI aRate bRate))))
  have e := quotient_difference f g x x₀ y y₀ h B hf hf₀ hg hg₀
  have core := GaussianNamedRateTransport.transport L G (Q F F) G (dd s t) (dd a b)
    (qd F F (dd x y) (dd x₀ y₀) h B) (dd a b) M D hD raw e (cross_refl _ _ r₃)
  have fit : Γ ⊢[PRAAx] le (M*U) (two*D) := le_of_eq_add (d := zero) (by
    dsimp only [M,D,GaussianNamedDifferenceRate.leadingNumerator,GaussianNamedDifferenceRate.leadingDenominator]
    ipra_ring)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hD hU fit core

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasDifferenceQuotientAlgebra
