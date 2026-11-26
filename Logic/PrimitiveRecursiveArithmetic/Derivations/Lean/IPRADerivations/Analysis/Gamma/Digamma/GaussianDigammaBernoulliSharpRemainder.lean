import IPRADerivations.Analysis.Gamma.Digamma.GaussianDigammaBernoulliTruncation
import IPRADerivations.Analysis.Gamma.Digamma.GaussianDigammaBernoulliActualUpper
import IPRADerivations.Analysis.Gamma.Digamma.GaussianDigammaBernoulliRadius

/-!
# Sharp signed digamma remainder at every fixed order

For r=m+1, the oriented name is (-1)^r times the original digamma
error after the first r-1 corrections. Both its strict bounds use
the same actual improper integral. The upper point is the exact
magnitude of the first omitted Bernoulli term.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliSharpRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDigammaBernoulliActualUpper (original_positive)
open GaussianDigammaBernoulliImproperName (original_improper_cross)
open GaussianDigammaBernoulliRadius (radiusNumerator radiusDenominator weighted_primitive_radius)
open GaussianDigammaBernoulliTruncation (orientedF orientedData named_truncation)
open GaussianDigammaBernoulliUpper (oriented_error_bracket)
open GaussianDigammaFirstBernoulliImproper (baseF baseData base_regular)
open GaussianGammaCanonicalExponent (constantF)
open GaussianRationalHorner (qzero)
open GaussianStirlingAllOrderLogRateTransport (upperPoint)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianStirlingNames (source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cap (m : ℕ) (A B : PTm n) : PTm n :=
  upperPoint (radiusNumerator m B) (radiusDenominator m A)

theorem original_improper_bracket (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF (GaussianDigammaBernoulliImproperName.nameF m) qzero
      (GaussianDigammaBernoulliImproperName.data m A B) ⋏
      strictOrder (GaussianDigammaBernoulliImproperName.nameF m) constantF
        (GaussianDigammaBernoulliImproperName.data m A B) (cap m A B) :=
  oriented_error_bracket baseF _ m A B (baseData A B) _ _ (base_regular A B hs)
    (original_positive m A B hs) (original_positive (m+1) A B hs)
    (GaussianNameEquivalence.cross_symm _ _ _ _ (original_improper_cross m A B hs))
    (weighted_primitive_radius m A B hs)

theorem original_signed_bracket (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF orientedF qzero (orientedData m A B) ⋏
      strictOrder orientedF constantF (orientedData m A B) (cap m A B) :=
  oriented_error_bracket baseF orientedF m A B (baseData A B) _ _ (base_regular A B hs)
    (original_positive m A B hs) (original_positive (m+1) A B hs)
    (named_truncation m A B hs) (weighted_primitive_radius m A B hs)

theorem actual_original_all_order_digamma_strict_bracket_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶ strictOrder constantF orientedF qzero (orientedData m (var 0) (var 1)) ⋏
        strictOrder orientedF constantF (orientedData m (var 0) (var 1)) (cap m (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_signed_bracket m _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliSharpRemainder
