import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicCompactName
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# Original logarithmic compact names on arbitrary positive intervals

Only the interval starting numerator changes. The actual original
logarithmic PR3 evaluator, its uniform query, modulus and normalization
programs are unchanged. The original finite positive interval guards
derive both local sample contracts and regularity internally.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicIntervalName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData wrapped_at original_variation)
open GaussianEulerLogarithmicMultiplier (lipschitz)
open GaussianEulerCompactAdditivity (intervalSource domain_of_inside)
open GaussianCompactRiemannName (inside sampledModulus localBody)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev nameF : PR 2 := GaussianEulerLogarithmicCompactName.nameF
def data (j z R B a C E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a C E (lipschitz j R E T) T (fixedData j R E T z B)
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (j z R B a C E T : PTm n) :
    Syn.subst σ (data j z R B a C E T) = data (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [data]

theorem local_modulus_at (j z R B a C E T t u A D : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hD : Γ ⊢[PRAAx] le one D)
    (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) :
    Γ ⊢[PRAAx] independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData j R E T z B))
      (GaussianCompactRiemannName.nameData u (fixedData j R E T z B)) (lipschitz j R E T*A) D := by
  have input : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.input z R B E T
      (fstT t) (sndT t) (fstT u) (sndT u) A D :=
    .andI h.andE₁ (.andI (domain_of_inside t a C E T h.andE₂.andE₁ h.andE₁.andE₂.andE₁ h.andE₂.andE₂ ht)
      (.andI (domain_of_inside u a C E T h.andE₂.andE₁ h.andE₁.andE₂.andE₁ h.andE₂.andE₂ hu) (.andI hD hd)))
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianEulerExponentCompactBounds.input (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
        (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t)))
        (fstT (Syn.shift (Syn.shift u))) (sndT (Syn.shift (Syn.shift u)))
        (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using input.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,
    GaussianEulerLogarithmicCompactName.subst_fixedData,GaussianEulerLogarithmicMultiplier.subst_lipschitz,
    PTm.subst_mul,Syn.shift] using
    distance_congr (wrapped_at (var 1) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (wrapped_at (var 0) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift R))
        (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (.eqRefl _) (.eqRefl _)
      (original_variation (var 1) (var 0) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
        (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t)))
        (fstT (Syn.shift (Syn.shift u))) (sndT (Syn.shift (Syn.shift u)))
        (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) hs)

theorem sampled_modulus (j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF a C E (lipschitz j R E T) (fixedData j R E T z B) := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      intervalSource (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) := by simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,GaussianEulerLogarithmicCompactName.subst_fixedData,
    GaussianEulerLogarithmicMultiplier.subst_lipschitz,Syn.shift] using
    local_modulus_at (Syn.shift (Syn.shift (Syn.shift (Syn.shift j)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift z))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift R)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift B))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift a)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift E)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift T))))
      (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input evaluatorF a C E (lipschitz j R E T) T (fixedData j R E T z B) :=
  .andI h.andE₂.andE₁ (.andI h.andE₁.andE₂.andE₁
    (.andI (le_trans (le_add_left C a) h.andE₂.andE₂) (sampled_modulus j z R B a C E T h)))

theorem name_regular (j z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data j z R B a C E T) :=
  GaussianCompactRiemannName.name_regular evaluatorF _ _ _ _ _ _ (compact_input j z R B a C E T h)

theorem name_at (p j z R B a C E T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data j z R B a C E T) ≐ GaussianCompactRiemannName.quadrature evaluatorF
      (GaussianCompactRiemannName.precision p T) (GaussianCompactRiemannName.mesh p (lipschitz j R E T) T)
      a C E (fixedData j R E T z B) := GaussianCompactRiemannName.name_at evaluatorF p _ _ _ _ _ _

theorem actual_logarithmic_arbitrary_positive_interval_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (intervalSource (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (name_regular _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicIntervalName
