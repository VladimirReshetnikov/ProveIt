import IPRADerivations.Analysis.Euler.GaussianEulerCompactModulus

/-!
# Ordinary Euler quadrature with an independent lower time margin

A panel encoded over denominator E can use the common time domain
[1/G,T] whenever E ≤ G*a and a+C ≤ T*E. The original Euler evaluator
then has its usual compact modulus with G in place of the denominator.
This lets rational image panels and refinements use the same modulus.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageCompactModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactLogarithmBounds (domain)
open GaussianCompactRiemannName (inside localBody sampledModulus)
open GaussianEulerCompactModulus (lipschitz)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def geometry (a C E G T : PTm n) : Fm PTm n :=
  (le one a ⋏ le one E) ⋏ (le E (G*a) ⋏ le (a+C) (T*E))

def source (z R B a C E G T : PTm n) : Fm PTm n :=
  GaussianEulerExponentCompactBounds.source z R B G ⋏ geometry a C E G T

def data (z R B a C E G T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a C E (lipschitz R G T) T (fixedData z B)

abbrev nameF : PR 2 := GaussianEulerCompactModulus.nameF

@[simp] theorem subst_geometry {m : ℕ} (σ : Fin n → PTm m) (a C E G T : PTm n) :
    (geometry a C E G T).subst σ = geometry (Syn.subst σ a) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ G) (Syn.subst σ T) := by simp [geometry]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C E G T : PTm n) :
    (source z R B a C E G T).subst σ = source (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ G) (Syn.subst σ T) := by simp [source]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B a C E G T : PTm n) :
    Syn.subst σ (data z R B a C E G T) = data (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ G) (Syn.subst σ T) := by simp [data]

theorem domain_of_inside (t a C E G T : PTm n) (hg : Γ ⊢[PRAAx] geometry a C E G T)
    (ht : Γ ⊢[PRAAx] inside a C E t) : Γ ⊢[PRAAx] domain (fstT t) (sndT t) G T := by
  have lo₁ := mul_le_mul_right (sndT t) hg.andE₂.andE₁
  have lo₂ := mul_le_mul_right G ht.andE₂.andE₂.andE₁
  have lo : Γ ⊢[PRAAx] le (E*sndT t) (E*(G*fstT t)) :=
    le_trans lo₁ (le_congr (by ipra_ring) (by ipra_ring) lo₂)
  have hi : Γ ⊢[PRAAx] le (E*fstT t) (E*(T*sndT t)) :=
    le_trans ht.andE₂.andE₂.andE₂
      (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right (sndT t) hg.andE₂.andE₂))
  exact .andI (.andI ht.andE₁ ht.andE₂.andE₁)
    (.andI (RationalValueBounds.positive_cancel hg.andE₁.andE₂ lo)
      (RationalValueBounds.positive_cancel hg.andE₁.andE₂ hi))

theorem local_modulus_at (z R B a C E G T t u A D : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E G T)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) :
    Γ ⊢[PRAAx] GaussianNamedInverseRate.independentRate
      (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData z B)) (GaussianCompactRiemannName.nameData u (fixedData z B))
      (lipschitz R G T*A) D :=
  GaussianEulerCompactModulus.wrapped_rate t u z B _ D
    (GaussianEulerCompactModulus.original_rate z R B G T (fstT t) (sndT t) (fstT u) (sndT u) A D
      (.andI h.andE₁ (.andI (domain_of_inside t a C E G T h.andE₂ ht)
        (.andI (domain_of_inside u a C E G T h.andE₂ hu) (.andI hD hd)))))

theorem sampled_modulus (z R B a C E G T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G T) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF a C E (lipschitz R G T) (fixedData z B) := by
  let s₄ (x : PTm n) : PTm (n+1+1+1+1) := Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (s₄ z) (s₄ R) (s₄ B) (s₄ a) (s₄ C) (s₄ E) (s₄ G) (s₄ T) := by
    simpa [Fm.shift,Syn.shift,s₄] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,GaussianEulerIntegrandName.subst_fixedData,GaussianEulerCompactModulus.subst_lipschitz,Syn.shift,s₄]
    using local_modulus_at (s₄ z) (s₄ R) (s₄ B) (s₄ a) (s₄ C) (s₄ E) (s₄ G) (s₄ T)
      (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (z R B a C E G T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G T) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input evaluatorF a C E (lipschitz R G T) T (fixedData z B) := by
  have upper : Γ ⊢[PRAAx] le C (E*T) :=
    le_congr (.eqRefl _) (mul_comm _ _) (le_trans (le_add_left C a) h.andE₂.andE₂.andE₂)
  exact .andI h.andE₂.andE₁.andE₁ (.andI h.andE₂.andE₁.andE₂
    (.andI upper (sampled_modulus z R B a C E G T h)))

theorem name_regular (z R B a C E G T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G T) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF (data z R B a C E G T) :=
  GaussianCompactRiemannName.name_regular evaluatorF _ _ _ _ _ _ (compact_input z R B a C E G T h)

theorem actual_euler_compact_modulus_independent_lower_margin_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      sampledModulus evaluatorF (var 3) (var 4) (var 5) (lipschitz (var 1) (var 6) (var 7)) (fixedData (var 0) (var 2))) :=
  closeUniv 8 (.impI (sampled_modulus _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_euler_compact_name_independent_lower_margin_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (name_regular _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageCompactModulus
