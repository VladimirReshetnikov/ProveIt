import IPRADerivations.Analysis.GaussianNamedDampingPowerCompact
import IPRADerivations.Analysis.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.GaussianCompactIntervalRescaling

/-!
# Additivity and endpoint representation for the named damped Euler integral

The original compact evaluator uses the same parameter names across
subintervals. Its checked time modulus proves additivity and invariance
under common positive rescaling of the endpoint fractions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompactAdditivity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedDampingPowerCompact (source evaluatorF fixedData lipschitz nameF data compact_input sampled_modulus)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNameArithmetic (addF addData)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def splitSource (F G : PR 2) (z Rz B x y C₀ C R₀ R a V W E T : PTm n) : Fm PTm n :=
  source F G z Rz B x y C₀ C R₀ R a (V+W) E T ⋏ (le one V ⋏ le one W)
def splitData (z Rz B x y C R a V W E T : PTm n) : PTm n :=
  addData (data z Rz B x y C R a V E T) (data z Rz B x y C R (a+V) W E T)
def scaledData (k z Rz B x y C R a W E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data (k*a) (k*W) (k*E) (lipschitz Rz C R E T) T (fixedData z B x y)

theorem split_input (F G : PR 2) (z Rz B x y C₀ C R₀ R a V W E T : PTm n)
    (hs : Γ ⊢[PRAAx] splitSource F G z Rz B x y C₀ C R₀ R a V W E T) : Γ ⊢[PRAAx]
    GaussianCompactNamedAdditivity.input (evaluatorF F G) a V W E (lipschitz Rz C R E T) T (fixedData z B x y) := by
  have full := compact_input F G z Rz B x y C₀ C R₀ R a (V+W) E T hs.andE₁
  exact .andI full.andE₁ (.andI full.andE₂.andE₁ (.andI hs.andE₂.andE₁ (.andI hs.andE₂.andE₂ full.andE₂.andE₂)))

theorem name_additivity (F G : PR 2) (z Rz B x y C₀ C R₀ R a V W E T : PTm n)
    (hs : Γ ⊢[PRAAx] splitSource F G z Rz B x y C₀ C R₀ R a V W E T) : Γ ⊢[PRAAx]
    crossEquivalent (nameF F G) (addF (nameF F G) (nameF F G))
      (data z Rz B x y C R a (V+W) E T) (splitData z Rz B x y C R a V W E T) :=
  GaussianCompactNamedAdditivity.name_additivity _ _ _ _ _ _ _ _ (split_input F G z Rz B x y C₀ C R₀ R a V W E T hs)

theorem observations (F G : PR 2) (p q z Rz B x y C₀ C R₀ R a V W E T : PTm n)
    (hs : Γ ⊢[PRAAx] splitSource F G z Rz B x y C₀ C R₀ R a V W E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF F G) p (data z Rz B x y C R a (V+W) E T))
      (ap2 (addF (nameF F G) (nameF F G)) q (splitData z Rz B x y C R a V W E T)) (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (name_additivity F G z Rz B x y C₀ C R₀ R a V W E T hs)

theorem name_rescaling (F G : PR 2) (k z Rz B x y C₀ C R₀ R a W E T : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    crossEquivalent (nameF F G) (nameF F G)
      (data z Rz B x y C R a W E T) (scaledData k z Rz B x y C R a W E T) :=
  GaussianCompactIntervalRescaling.name_rescaling _ _ _ _ _ _ _ _
    (.andI hk (compact_input F G z Rz B x y C₀ C R₀ R a W E T hs))

theorem actual_named_power_damped_compact_additivity_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
      (splitSource F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
        crossEquivalent (nameF F G) (addF (nameF F G) (nameF F G))
          (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 8) (var 9) (var 10+var 11) (var 12) (var 13))
          (splitData (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))) :=
  closeUniv 14 (.impI (name_additivity F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_named_power_damped_compact_endpoint_rescaling_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
      (source F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
        le one (var 0) ⟶ crossEquivalent (nameF F G) (nameF F G)
          (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 9) (var 10) (var 11) (var 12) (var 13))
          (scaledData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 9) (var 10) (var 11) (var 12) (var 13))) :=
  closeUniv 14 (.impI (.impI (name_rescaling F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompactAdditivity
