import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianNamedEulerCompactTimeRate

/-!
# A sampled compact modulus for the actual named Euler evaluator

Regularity of the original fixed input name and the literal compact
endpoint guards imply the actual evaluator's sampled time modulus.
The usual original compact integration program therefore gives a regular
quadrature name, with no supplied integrand or output-name premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerCompactModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedEulerCompactTimeRate (gain)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCompactRiemannName (inside value nameData evaluatorName)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (f : PR 2) (x E T C : PTm n) : Fm PTm n := pointCN f x ⋏ (le one E ⋏ le (one+C) (E*T))
def data (f : PR 2) (x E T C : PTm n) : PTm n := GaussianCompactRiemannName.data one C E (gain f x E T) T x
def nameF (f : PR 2) : PR 2 := GaussianCompactRiemannName.nameF (GaussianNamedEulerIntegrand.evaluatorF f)
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E T C : PTm n) :
    (source f x E T C).subst σ = source f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) := by simp [source]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E T C : PTm n) :
    Syn.subst σ (data f x E T C) = data f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) := by simp [data]

theorem wrapped_at (f : PR 2) (p t x : PTm n) : Γ ⊢[PRAAx]
    ap2 (evaluatorName (GaussianNamedEulerIntegrand.evaluatorF f)) p (nameData t x) ≐
      ap2 (GaussianNamedEulerIntegrand.nameF f) p (GaussianNamedEulerIntegrand.data f x (fstT t) (sndT t)) :=
  (GaussianCompactRiemannName.evaluator_at _ p t x).eqTrans (GaussianNamedEulerIntegrand.evaluator_at f p t x)

theorem wrapped_rate (f : PR 2) (t u x A N : PTm n)
    (h : Γ ⊢[PRAAx] independentRate (GaussianNamedEulerIntegrand.nameF f) (GaussianNamedEulerIntegrand.nameF f)
      (GaussianNamedEulerIntegrand.data f x (fstT t) (sndT t)) (GaussianNamedEulerIntegrand.data f x (fstT u) (sndT u)) A N) : Γ ⊢[PRAAx]
    independentRate (evaluatorName (GaussianNamedEulerIntegrand.evaluatorF f)) (evaluatorName (GaussianNamedEulerIntegrand.evaluatorF f))
      (nameData t x) (nameData u x) A N := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      independentRate (GaussianNamedEulerIntegrand.nameF f) (GaussianNamedEulerIntegrand.nameF f)
        (GaussianNamedEulerIntegrand.data f (Syn.shift (Syn.shift x)) (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t))))
        (GaussianNamedEulerIntegrand.data f (Syn.shift (Syn.shift x)) (fstT (Syn.shift (Syn.shift u))) (sndT (Syn.shift (Syn.shift u))))
        (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,Syn.shift] using
    distance_congr (wrapped_at f (var 1) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift x))).eqSymm
      (wrapped_at f (var 0) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift x))).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) hs)

theorem local_modulus_at (f : PR 2) (x E T C t u A N : PTm n) (h : Γ ⊢[PRAAx] source f x E T C)
    (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] inside one C E t) (hu : Γ ⊢[PRAAx] inside one C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) A N) : Γ ⊢[PRAAx]
    independentRate (evaluatorName (GaussianNamedEulerIntegrand.evaluatorF f)) (evaluatorName (GaussianNamedEulerIntegrand.evaluatorF f))
      (nameData t x) (nameData u x) (gain f x E T*A) N :=
  wrapped_rate f t u x _ N (GaussianNamedEulerCompactTimeRate.original_rate f x E T (fstT t) (sndT t) (fstT u) (sndT u) A N
    (.andI h.andE₁ (.andI h.andE₂.andE₁ (.andI (GaussianEulerCompactModulus.domain_of_inside t C E T h.andE₂.andE₁ h.andE₂.andE₂ ht)
      (.andI (GaussianEulerCompactModulus.domain_of_inside u C E T h.andE₂.andE₁ h.andE₂.andE₂ hu) (.andI hN hd))))))

theorem sampled_modulus (f : PR 2) (x E T C : PTm n) (h : Γ ⊢[PRAAx] source f x E T C) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.sampledModulus (GaussianNamedEulerIntegrand.evaluatorF f) one C E (gain f x E T) x := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source f (Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [GaussianCompactRiemannName.localBody,GaussianNamedEulerCompactTimeRate.subst_gain,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    local_modulus_at f (Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C))))
      (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (f : PR 2) (x E T C : PTm n) (h : Γ ⊢[PRAAx] source f x E T C) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input (GaussianNamedEulerIntegrand.evaluatorF f) one C E (gain f x E T) T x :=
  .andI (le_refl one) (.andI h.andE₂.andE₁ (.andI (le_trans (le_add_left C one) h.andE₂.andE₂) (sampled_modulus f x E T C h)))

theorem name_regular (f : PR 2) (x E T C : PTm n) (h : Γ ⊢[PRAAx] source f x E T C) : Γ ⊢[PRAAx]
    pointCN (nameF f) (data f x E T C) :=
  GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ (compact_input f x E T C h)

theorem original_named_Euler_sampled_compact_modulus_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source f (var 0) (var 1) (var 2) (var 3) ⟶ GaussianCompactRiemannName.sampledModulus
      (GaussianNamedEulerIntegrand.evaluatorF f) one (var 3) (var 1) (gain f (var 0) (var 1) (var 2)) (var 0)) :=
  closeUniv 4 (.impI (sampled_modulus f _ _ _ _ Prf.hyp0))
theorem original_named_Euler_regular_compact_quadrature_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source f (var 0) (var 1) (var 2) (var 3) ⟶ pointCN (nameF f) (data f (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerCompactModulus
