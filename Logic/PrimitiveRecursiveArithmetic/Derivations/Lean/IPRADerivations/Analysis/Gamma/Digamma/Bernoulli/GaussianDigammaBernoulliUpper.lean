import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.GaussianDigammaBernoulliName
import IPRADerivations.Analysis.Gamma.BohrMollerup.Uniqueness.GaussianBohrMollerupZeroAlgebra
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelUniform
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference

/-!
# Strict upper comparison from the next Bernoulli remainder

The certified digamma recurrence is a difference with the exact
weighted primitive. Positivity of the next name turns that
recurrence into a strict upper comparison for the current name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliUpper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDigammaBernoulliName (nameF nameData name_regular)
open GaussianDigammaBernoulliRecurrence (weightedPrimitive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaRationalWendelUniform (zero_constant)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNameRingLaws (zeroF zero_fast add_zero_left)
open GaussianNamedStrictOrderDifference (add_right)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open GaussianRationalHorner (qzero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "differenceF" => GaussianNamedDifference.nameF
local notation "differenceData" => GaussianNamedDifference.data

theorem strict_of_positive_difference (F G : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] strictOrder constantF (differenceF G F) qzero (differenceData y x)) :
    Γ ⊢[PRAAx] strictOrder F G x y := by
  let D := differenceF G F
  let z := differenceData y x
  have hd : Γ ⊢[PRAAx] pointCN D z := GaussianNamedDifference.name_regular G F y x hg hf
  have hp : Γ ⊢[PRAAx] strictOrder zeroF D x z :=
    strict_transport _ _ _ _ _ _ _ _ (zero_constant x) (cross_refl D z hd) h
  exact strict_transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (add_zero_left F x hf))
    (GaussianBohrMollerupZeroAlgebra.subtract_add G F y x hg hf)
    (add_right zeroF D F x z x (zero_fast x) hd hf hp)

theorem named_recurrence_upper (initial : PR 2) (m : ℕ) (A B x : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN initial x)
    (hNext : Γ ⊢[PRAAx] strictOrder constantF (nameF initial (m+1)) qzero (nameData (m+1) A B x)) :
    Γ ⊢[PRAAx] strictOrder (nameF initial m) constantF (nameData m A B x) (weightedPrimitive m A B) :=
  strict_of_positive_difference (nameF initial m) constantF _ _
    (name_regular initial m A B x hx) (constant_regular _) hNext

theorem named_recurrence_bracket (initial : PR 2) (m : ℕ) (A B x : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN initial x)
    (hCurrent : Γ ⊢[PRAAx] strictOrder constantF (nameF initial m) qzero (nameData m A B x))
    (hNext : Γ ⊢[PRAAx] strictOrder constantF (nameF initial (m+1)) qzero (nameData (m+1) A B x)) :
    Γ ⊢[PRAAx] strictOrder constantF (nameF initial m) qzero (nameData m A B x) ⋏
      strictOrder (nameF initial m) constantF (nameData m A B x) (weightedPrimitive m A B) :=
  .andI hCurrent (named_recurrence_upper initial m A B x hx hNext)

theorem oriented_error_bracket (initial F : PR 2) (m : ℕ) (A B x y c : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN initial x)
    (hCurrent : Γ ⊢[PRAAx] strictOrder constantF (nameF initial m) qzero (nameData m A B x))
    (hNext : Γ ⊢[PRAAx] strictOrder constantF (nameF initial (m+1)) qzero (nameData (m+1) A B x))
    (hError : Γ ⊢[PRAAx] crossEquivalent (nameF initial m) F (nameData m A B x) y)
    (hCap : Γ ⊢[PRAAx] weightedPrimitive m A B ≐ c) :
    Γ ⊢[PRAAx] strictOrder constantF F qzero y ⋏ strictOrder F constantF y c := by
  have hZero : Γ ⊢[PRAAx] crossEquivalent constantF constantF qzero qzero :=
    cross_refl constantF _ (constant_regular _)
  exact .andI (strict_transport _ _ _ _ _ _ _ _ hZero hError hCurrent)
    (strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ hError)
      (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ hCap)
      (named_recurrence_upper initial m A B x hx hNext))

theorem named_recurrence_upper_closed (initial : PR 2) (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (pointCN initial (var 2) ⟶
        strictOrder constantF (nameF initial (m+1)) qzero (nameData (m+1) (var 0) (var 1) (var 2)) ⟶
        strictOrder (nameF initial m) constantF (nameData m (var 0) (var 1) (var 2))
          (weightedPrimitive m (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (named_recurrence_upper initial m _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliUpper
