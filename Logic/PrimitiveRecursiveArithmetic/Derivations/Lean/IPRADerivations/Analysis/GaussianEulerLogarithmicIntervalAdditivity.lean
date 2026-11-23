import IPRADerivations.Analysis.GaussianEulerLogarithmicIntervalName
import IPRADerivations.Analysis.GaussianCompactIntervalRescaling

/-!
# Actual logarithmic compact additivity with an unchanged client

The original numerical interval source derives the local contracts of
the actual logarithmic evaluator. The three compact names retain the
same j,R,E,T client and are related by the existing normalized addF
program, without identifying independently sampled grids.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicIntervalAdditivity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicIntervalName (nameF data sampled_modulus)
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData)
open GaussianEulerLogarithmicMultiplier (lipschitz)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C1 C2 E T : PTm n) : Fm PTm n :=
  GaussianEulerCompactAdditivity.intervalSource z R B a (C1+C2) E T ⋏ (le one C1 ⋏ le one C2)
def addedData (j z R B a C1 C2 E T : PTm n) : PTm n :=
  addData (data j z R B a C1 E T) (data j z R B (a+C1) C2 E T)
def rescaledData (k j z R B a C E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data (k*a) (k*C) (k*E) (lipschitz j R E T) T (fixedData j R E T z B)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C1 C2 E T : PTm n) :
    (source z R B a C1 C2 E T).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C1) (Syn.subst σ C2) (Syn.subst σ E) (Syn.subst σ T) := by simp [source]
@[simp] theorem subst_addedData {m : ℕ} (σ : Fin n → PTm m) (j z R B a C1 C2 E T : PTm n) :
    Syn.subst σ (addedData j z R B a C1 C2 E T) = addedData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C1) (Syn.subst σ C2) (Syn.subst σ E) (Syn.subst σ T) := by simp [addedData]
@[simp] theorem subst_rescaledData {m : ℕ} (σ : Fin n → PTm m) (k j z R B a C E T : PTm n) :
    Syn.subst σ (rescaledData k j z R B a C E T) = rescaledData (Syn.subst σ k) (Syn.subst σ j)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [rescaledData]

theorem additivity_input (j z R B a C1 C2 E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C1 C2 E T) : Γ ⊢[PRAAx]
    GaussianCompactNamedAdditivity.input evaluatorF a C1 C2 E (lipschitz j R E T) T (fixedData j R E T z B) :=
  .andI h.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂
    (.andI (le_trans (le_add_left (C1+C2) a) h.andE₁.andE₂.andE₂)
      (sampled_modulus j z R B a (C1+C2) E T h.andE₁)))))

theorem original_additivity (j z R B a C1 C2 E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C1 C2 E T) : Γ ⊢[PRAAx]
    crossEquivalent nameF (addF nameF nameF) (data j z R B a (C1+C2) E T) (addedData j z R B a C1 C2 E T) :=
  GaussianCompactNamedAdditivity.name_additivity evaluatorF a C1 C2 E (lipschitz j R E T) T (fixedData j R E T z B)
    (additivity_input j z R B a C1 C2 E T h)

theorem original_observations (p q j z R B a C1 C2 E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C1 C2 E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data j z R B a (C1+C2) E T))
      (ap2 (addF nameF nameF) q (addedData j z R B a C1 C2 E T)) (unit p+unit q) (unit p*unit q) :=
  GaussianNameEquivalence.cross_at _ _ _ _ p q (original_additivity j z R B a C1 C2 E T h)

/-- The original client j,R,E,T and all of its actual query clocks stay
fixed while the numerical interval encoding is multiplied by k. -/
theorem original_rescaling (k j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data j z R B a C E T) (rescaledData k j z R B a C E T) :=
  GaussianCompactIntervalRescaling.name_rescaling evaluatorF k a C E (lipschitz j R E T) T (fixedData j R E T z B)
    (.andI hk (GaussianEulerLogarithmicIntervalName.compact_input j z R B a C E T h))

theorem original_rescaling_observations (p q k j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data j z R B a C E T)) (ap2 nameF q (rescaledData k j z R B a C E T))
      (unit p+unit q) (unit p*unit q) :=
  GaussianNameEquivalence.cross_at _ _ _ _ p q (original_rescaling k j z R B a C E T h hk)

theorem actual_logarithmic_compact_additivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      crossEquivalent nameF (addF nameF nameF) (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5+var 6) (var 7) (var 8))
        (addedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (original_additivity _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_logarithmic_compact_fixed_client_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((GaussianEulerCompactAdditivity.intervalSource (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏ le one (var 0)) ⟶
      crossEquivalent nameF nameF (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (rescaledData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (original_rescaling _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicIntervalAdditivity
