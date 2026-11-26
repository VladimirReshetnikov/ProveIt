import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.Euler.GaussianEulerCompactModulus

/-!
# Source-only additive compact names of the original Euler integrand

All original input/time guards are numerical. The actual original PR3
Euler evaluator supplies the local modulus internally. The SAME existing
compact names at [a/E,(a+C1+C2)/E] and its two original subintervals are
cross-equivalent through the actual normalized addF program. The proved
conservative factor is retained; no sharper paper mesh or varying-cutoff
improper-integral conclusion is asserted here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactAdditivity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCompactModulus (lipschitz)
open GaussianCompactRiemannName (inside sampledModulus localBody)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCompactLogarithmBounds (domain)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def intervalSource (z R B a C E T : PTm n) : Fm PTm n :=
  GaussianEulerExponentCompactBounds.source z R B E ⋏ (le one a ⋏ le (a+C) (E*T))
def source (z R B a C1 C2 E T : PTm n) : Fm PTm n :=
  intervalSource z R B a (C1+C2) E T ⋏ (le one C1 ⋏ le one C2)
def data (z R B a C E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a C E (lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B)
def nameF : PR 2 := GaussianCompactRiemannName.nameF GaussianEulerIntegrandName.evaluatorF
def addedData (z R B a C1 C2 E T : PTm n) : PTm n :=
  GaussianNameArithmetic.addData (data z R B a C1 E T) (data z R B (a+C1) C2 E T)

@[simp] theorem subst_intervalSource {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T : PTm n) :
    (intervalSource z R B a C E T).subst σ = intervalSource (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [intervalSource]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C1 C2 E T : PTm n) :
    (source z R B a C1 C2 E T).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C1) (Syn.subst σ C2) (Syn.subst σ E) (Syn.subst σ T) := by simp [source]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T : PTm n) :
    Syn.subst σ (data z R B a C E T) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [data]
@[simp] theorem subst_addedData {m : ℕ} (σ : Fin n → PTm m) (z R B a C1 C2 E T : PTm n) :
    Syn.subst σ (addedData z R B a C1 C2 E T) = addedData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C1) (Syn.subst σ C2) (Syn.subst σ E) (Syn.subst σ T) := by simp [addedData]

/-- Genuine original cross-multiplied interval guards, allowing arbitrary
raw time codes and any positive numerical starting numerator. -/
theorem domain_of_inside (t a C E T : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (he : Γ ⊢[PRAAx] le (a+C) (E*T)) (h : Γ ⊢[PRAAx] inside a C E t) : Γ ⊢[PRAAx] domain (fstT t) (sndT t) E T := by
  have low := le_trans (le_congr (one_mul _) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono ha (le_refl (sndT t)))) h.andE₂.andE₂.andE₁
  have upper := le_trans h.andE₂.andE₂.andE₂ (mul_le_mul_right (sndT t) he)
  have clear : Γ ⊢[PRAAx] le (E*fstT t) (E*(T*sndT t)) := le_congr (.eqRefl _) (by ipra_ring) upper
  exact .andI (.andI h.andE₁ h.andE₂.andE₁) (.andI low (RationalValueBounds.positive_cancel hE clear))

theorem local_modulus_at (z R B a C E T t u A D : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate (GaussianCompactRiemannName.evaluatorName GaussianEulerIntegrandName.evaluatorF)
      (GaussianCompactRiemannName.evaluatorName GaussianEulerIntegrandName.evaluatorF)
      (GaussianCompactRiemannName.nameData t (GaussianEulerIntegrandName.fixedData z B))
      (GaussianCompactRiemannName.nameData u (GaussianEulerIntegrandName.fixedData z B)) (lipschitz R E T*A) D :=
  GaussianEulerCompactModulus.wrapped_rate t u z B _ D (GaussianEulerCompactModulus.original_rate z R B E T
    (fstT t) (sndT t) (fstT u) (sndT u) A D (.andI h.andE₁
      (.andI (domain_of_inside t a C E T h.andE₂.andE₁ h.andE₁.andE₂.andE₁ h.andE₂.andE₂ ht)
        (.andI (domain_of_inside u a C E T h.andE₂.andE₁ h.andE₁.andE₂.andE₁ h.andE₂.andE₂ hu) (.andI hD hd)))))

theorem sampled_modulus (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    sampledModulus GaussianEulerIntegrandName.evaluatorF a C E (lipschitz R E T) (GaussianEulerIntegrandName.fixedData z B) := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      intervalSource (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) := by simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,GaussianEulerIntegrandName.subst_fixedData,GaussianEulerCompactModulus.subst_lipschitz,Syn.shift] using
    local_modulus_at (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (var 3) (var 2) (var 1) (var 0)
      hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input GaussianEulerIntegrandName.evaluatorF a C E (lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B) :=
  .andI h.andE₂.andE₁ (.andI h.andE₁.andE₂.andE₁ (.andI (le_trans (le_add_left C a) h.andE₂.andE₂)
    (sampled_modulus z R B a C E T h)))
theorem name_regular (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data z R B a C E T) :=
  GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ (compact_input z R B a C E T h)

theorem additivity_input (z R B a C1 C2 E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C1 C2 E T) : Γ ⊢[PRAAx]
    GaussianCompactNamedAdditivity.input GaussianEulerIntegrandName.evaluatorF a C1 C2 E (lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B) :=
  .andI h.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂
    (.andI (le_trans (le_add_left (C1+C2) a) h.andE₁.andE₂.andE₂) (sampled_modulus z R B a (C1+C2) E T h.andE₁)))))

/-- Actual original Euler compact names are additive. No sampled modulus
or target name relation is supplied: both are derived from original guards. -/
theorem name_additivity (z R B a C1 C2 E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C1 C2 E T) : Γ ⊢[PRAAx]
    crossEquivalent nameF (GaussianNameArithmetic.addF nameF nameF) (data z R B a (C1+C2) E T) (addedData z R B a C1 C2 E T) :=
  GaussianCompactNamedAdditivity.name_additivity _ _ _ _ _ _ _ _ (additivity_input z R B a C1 C2 E T h)

theorem observations (p q z R B a C1 C2 E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C1 C2 E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a (C1+C2) E T))
      (ap2 (GaussianNameArithmetic.addF nameF nameF) q (addedData z R B a C1 C2 E T))
      (unit p+unit q) (unit p*unit q) := GaussianNameEquivalence.cross_at _ _ _ _ p q (name_additivity z R B a C1 C2 E T h)

theorem original_origin_binding (z R B C E T : PTm n) : Γ ⊢[PRAAx]
    data z R B one C E T ≐ GaussianEulerCompactModulus.data z R B E T C := .eqRefl _

def output (p q z R B a C1 C2 E T : PTm n) : PTm n := pairT (ap2 nameF p (data z R B a (C1+C2) E T))
  (pairT (ap2 (GaussianNameArithmetic.addF nameF nameF) q (addedData z R B a C1 C2 E T)) (pairT (unit p+unit q) (unit p*unit q)))
def outputF : PR 10 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
def run (p q z R B a C1 C2 E T : PTm n) : PTm n := PTm.app outputF ![p,q,z,R,B,a,C1,C2,E,T]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (p q z R B a C1 C2 E T : PTm n) :
    Syn.subst σ (output p q z R B a C1 C2 E T) = output (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C1) (Syn.subst σ C2) (Syn.subst σ E) (Syn.subst σ T) := by simp [output]
theorem program_at (p q z R B a C1 C2 E T : PTm n) : Γ ⊢[PRAAx]
    run p q z R B a C1 C2 E T ≐ output p q z R B a C1 C2 E T := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) : PTm 10) ![p,q,z,R,B,a,C1,C2,E,T]
theorem returned_full (p q z R B a C1 C2 E T : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q z R B a C1 C2 E T) ≐ ap2 nameF p (data z R B a (C1+C2) E T) :=
  (congrFst (program_at p q z R B a C1 C2 E T)).eqTrans (fst_pair _ _)
theorem returned_tail (p q z R B a C1 C2 E T : PTm n) : Γ ⊢[PRAAx]
    sndT (run p q z R B a C1 C2 E T) ≐ pairT (ap2 (GaussianNameArithmetic.addF nameF nameF) q (addedData z R B a C1 C2 E T))
      (pairT (unit p+unit q) (unit p*unit q)) := (congrSnd (program_at p q z R B a C1 C2 E T)).eqTrans (snd_pair _ _)
theorem returned_sum (p q z R B a C1 C2 E T : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p q z R B a C1 C2 E T)) ≐ ap2 (GaussianNameArithmetic.addF nameF nameF) q (addedData z R B a C1 C2 E T) :=
  (congrFst (returned_tail p q z R B a C1 C2 E T)).eqTrans (fst_pair _ _)
theorem returned_budget (p q z R B a C1 C2 E T : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run p q z R B a C1 C2 E T)) ≐ pairT (unit p+unit q) (unit p*unit q) :=
  (congrSnd (returned_tail p q z R B a C1 C2 E T)).eqTrans (snd_pair _ _)
theorem returned_numerator (p q z R B a C1 C2 E T : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run p q z R B a C1 C2 E T))) ≐ unit p+unit q :=
  (congrFst (returned_budget p q z R B a C1 C2 E T)).eqTrans (fst_pair _ _)
theorem returned_denominator (p q z R B a C1 C2 E T : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run p q z R B a C1 C2 E T))) ≐ unit p*unit q :=
  (congrSnd (returned_budget p q z R B a C1 C2 E T)).eqTrans (snd_pair _ _)
theorem returned_distance (p q z R B a C1 C2 E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C1 C2 E T) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p q z R B a C1 C2 E T)) (fstT (sndT (run p q z R B a C1 C2 E T)))
      (fstT (sndT (sndT (run p q z R B a C1 C2 E T)))) (sndT (sndT (sndT (run p q z R B a C1 C2 E T)))) :=
  distance_congr (returned_full p q z R B a C1 C2 E T).eqSymm (returned_sum p q z R B a C1 C2 E T).eqSymm
    (returned_numerator p q z R B a C1 C2 E T).eqSymm (returned_denominator p q z R B a C1 C2 E T).eqSymm
    (observations p q z R B a C1 C2 E T h)

theorem original_Euler_general_compact_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (intervalSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      sampledModulus GaussianEulerIntegrandName.evaluatorF (var 3) (var 4) (var 5) (lipschitz (var 1) (var 5) (var 6))
        (GaussianEulerIntegrandName.fixedData (var 0) (var 2))) :=
  closeUniv 7 (.impI (sampled_modulus _ _ _ _ _ _ _ Prf.hyp0))
theorem original_Euler_general_compact_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (intervalSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (name_regular _ _ _ _ _ _ _ Prf.hyp0))
theorem original_Euler_compact_names_additive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      crossEquivalent nameF (GaussianNameArithmetic.addF nameF nameF)
        (data (var 0) (var 1) (var 2) (var 3) (var 4+var 5) (var 6) (var 7))
        (addedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (name_additivity _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_Euler_compact_additivity_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6+var 7) (var 8) (var 9)))
        (ap2 (GaussianNameArithmetic.addF nameF nameF) (var 1) (addedData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (observations _ _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_Euler_compact_additivity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)) :=
  closeUniv 10 (program_at _ _ _ _ _ _ _ _ _ _)
theorem actual_returned_Euler_compact_additivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)))))
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)))))) :=
  closeUniv 10 (.impI (returned_distance _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactAdditivity
