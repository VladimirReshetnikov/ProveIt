import IPRADerivations.Analysis.Euler.GaussianEulerExponentCompactBounds
import IPRADerivations.Analysis.Exponential.GaussianRadiusExponentialLipschitzRate
import IPRADerivations.Analysis.Exponential.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport
import IPRADerivations.Analysis.Integration.GaussianCompactRiemannName
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual constructive Euler-integrand compact modulus

Only original input disk/positive denominator/compact endpoint guards
are inputs. The unchanged original PR3 evaluator is bound to a genuine
verified local sampled modulus and therefore to an actual compact
quadrature name. Its conservative mesh may be denser than the paper's
sharper displayed majorant. No integrand modulus/output relation is an
input, and no varying-cutoff improper-integral claim is made.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNamedInverseRate (independentRate)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEulerIntegrandName (exponentF exponentData)
open GaussianCompactLogarithmBounds (domain)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lipschitz (R E T : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor
  (GaussianEulerExponentCompactBounds.radius R E T)*GaussianEulerExponentCompactBounds.factor R E
def source (z R B E T C : PTm n) : Fm PTm n := GaussianEulerExponentCompactBounds.source z R B E ⋏ le (one+C) (E*T)
def data (z R B E T C : PTm n) : PTm n := GaussianCompactRiemannName.data one C E (lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B)
def nameF : PR 2 := GaussianCompactRiemannName.nameF GaussianEulerIntegrandName.evaluatorF
@[simp] theorem subst_lipschitz {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (lipschitz R E T) = lipschitz (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [lipschitz]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B E T C : PTm n) :
    (source z R B E T C).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) := by simp [source]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B E T C : PTm n) :
    Syn.subst σ (data z R B E T C) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) := by simp [data]

theorem rate_congr (F G : PR 2) (x y A A' D : PTm n) (he : Γ ⊢[PRAAx] A ≐ A')
    (h : Γ ⊢[PRAAx] independentRate F G x y A D) : Γ ⊢[PRAAx] independentRate F G x y A' D := by
  simpa using Prf.eqSubst (independentRate F G (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![x,y,A,D] ![x,y,A',D] (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact he; exact .eqRefl _) (by simpa using h)

/-- Original per-time radii are transported to and from the genuinely
derived common radius; original output programs and data are preserved. -/
theorem original_rate (z R B E T a b c d A D : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.input z R B E T a b c d A D) : Γ ⊢[PRAAx]
    independentRate GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF
      (GaussianEulerIntegrandName.data z B a b) (GaussianEulerIntegrandName.data z B c d) (lipschitz R E T*A) D := by
  let M := GaussianEulerExponentCompactBounds.radius R E T
  let H := GaussianEulerExponentCompactBounds.factor R E
  have ca := GaussianEulerExponentCompactBounds.common_exponential_input z R B E T a b h.andE₁ h.andE₂.andE₁
  have cc := GaussianEulerExponentCompactBounds.common_exponential_input z R B E T c d h.andE₁ h.andE₂.andE₂.andE₁
  have origA := GaussianEulerIntegrandName.exponent_input z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁.andE₁)
  have origC := GaussianEulerIntegrandName.exponent_input z B c d (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)
  have common := GaussianRadiusExponentialLipschitzRate.independent_rate exponentF exponentF M
    (exponentData z B a b) (exponentData z B c d) (H*A) D
    (.andI h.andE₂.andE₂.andE₂.andE₁ (.andI ca (.andI cc (GaussianEulerExponentCompactBounds.independent_rate z R B E T a b c d A D h))))
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF exponentF
    (GaussianEulerIntegrandName.radius z B a b) M (exponentData z B a b) (exponentData z B a b) origA ca
    (GaussianNameEquivalence.cross_refl _ _ origA.andE₁)
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF exponentF
    (GaussianEulerIntegrandName.radius z B c d) M (exponentData z B c d) (exponentData z B c d) origC cc
    (GaussianNameEquivalence.cross_refl _ _ origC.andE₁)
  have moved := GaussianNamedRateTransport.transport (GaussianRadiusExponentialName.nameF exponentF) (GaussianRadiusExponentialName.nameF exponentF)
    GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF (GaussianRadiusExponentialName.data M (exponentData z B a b))
    (GaussianRadiusExponentialName.data M (exponentData z B c d)) (GaussianEulerIntegrandName.data z B a b) (GaussianEulerIntegrandName.data z B c d)
    (GaussianRadiusExponentialLipschitzRate.factor M*(H*A)) D h.andE₂.andE₂.andE₂.andE₁ common left right
  exact rate_congr _ _ _ _ _ _ _ (by unfold lipschitz H M; ipra_ring) moved

/-- Original cross-multiplied interval guards imply the actual compact
time domain, including arbitrary raw encoded time arguments. -/
theorem domain_of_inside (t C E T : PTm n) (hE : Γ ⊢[PRAAx] le one E) (he : Γ ⊢[PRAAx] le (one+C) (E*T))
    (h : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside one C E t) : Γ ⊢[PRAAx] domain (fstT t) (sndT t) E T := by
  have low := le_congr (one_mul _) (.eqRefl _) h.andE₂.andE₂.andE₁
  have upper := le_trans h.andE₂.andE₂.andE₂ (mul_le_mul_right (sndT t) he)
  have clear : Γ ⊢[PRAAx] le (E*fstT t) (E*(T*sndT t)) := le_congr (.eqRefl _) (by ipra_ring) upper
  exact .andI (.andI h.andE₁ h.andE₂.andE₁) (.andI low (RationalValueBounds.positive_cancel hE clear))

theorem evaluator_raw_at (p t z B : PTm n) : Γ ⊢[PRAAx]
    ap3 GaussianEulerIntegrandName.evaluatorF p t (GaussianEulerIntegrandName.fixedData z B) ≐
      ap2 GaussianEulerIntegrandName.nameF p (GaussianEulerIntegrandName.data z B (fstT t) (sndT t)) := by
  apply (GaussianEulerIntegrandName.evaluator_at p t (GaussianEulerIntegrandName.fixedData z B)).eqTrans
  apply congrAp2 GaussianEulerIntegrandName.nameF (.eqRefl p)
  ipra_congr (GaussianEulerIntegrandName.data (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [(show _ ⊢[PRAAx] fstT (GaussianEulerIntegrandName.fixedData z B) ≐ z from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (GaussianEulerIntegrandName.fixedData z B) ≐ B from snd_pair _ _), .eqRefl (fstT t),
      .eqRefl (sndT t)]

theorem wrapped_at (p t z B : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianCompactRiemannName.evaluatorName GaussianEulerIntegrandName.evaluatorF) p
      (GaussianCompactRiemannName.nameData t (GaussianEulerIntegrandName.fixedData z B)) ≐
        ap2 GaussianEulerIntegrandName.nameF p (GaussianEulerIntegrandName.data z B (fstT t) (sndT t)) :=
  (GaussianCompactRiemannName.evaluator_at _ p t _).eqTrans (evaluator_raw_at p t z B)

theorem wrapped_rate (t u z B A D : PTm n)
    (h : Γ ⊢[PRAAx] independentRate GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF
      (GaussianEulerIntegrandName.data z B (fstT t) (sndT t)) (GaussianEulerIntegrandName.data z B (fstT u) (sndT u)) A D) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName GaussianEulerIntegrandName.evaluatorF)
      (GaussianCompactRiemannName.evaluatorName GaussianEulerIntegrandName.evaluatorF)
      (GaussianCompactRiemannName.nameData t (GaussianEulerIntegrandName.fixedData z B))
      (GaussianCompactRiemannName.nameData u (GaussianEulerIntegrandName.fixedData z B)) A D := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF
      (GaussianEulerIntegrandName.data (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B)) (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t))))
      (GaussianEulerIntegrandName.data (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B)) (fstT (Syn.shift (Syn.shift u))) (sndT (Syn.shift (Syn.shift u))))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,GaussianEulerIntegrandName.subst_fixedData,Syn.shift] using
    distance_congr (wrapped_at (var 1) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (wrapped_at (var 0) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) hs)

theorem local_modulus_at (z R B E T C t u A D : PTm n) (hz : Γ ⊢[PRAAx] source z R B E T C)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside one C E t)
    (hu : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside one C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName GaussianEulerIntegrandName.evaluatorF)
      (GaussianCompactRiemannName.evaluatorName GaussianEulerIntegrandName.evaluatorF)
      (GaussianCompactRiemannName.nameData t (GaussianEulerIntegrandName.fixedData z B))
      (GaussianCompactRiemannName.nameData u (GaussianEulerIntegrandName.fixedData z B)) (lipschitz R E T*A) D :=
  wrapped_rate t u z B _ D (original_rate z R B E T (fstT t) (sndT t) (fstT u) (sndT u) A D
    (.andI hz.andE₁ (.andI (domain_of_inside t C E T hz.andE₁.andE₂.andE₁ hz.andE₂ ht)
      (.andI (domain_of_inside u C E T hz.andE₁.andE₂.andE₁ hz.andE₂ hu) (.andI hD hd)))))


/-- Every bound variable here is numerical; the original local sampled
modulus is now a conclusion of the genuine source guards. -/
theorem sampled_modulus (z R B E T C : PTm n) (h : Γ ⊢[PRAAx] source z R B E T C) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.sampledModulus GaussianEulerIntegrandName.evaluatorF one C E (lipschitz R E T) (GaussianEulerIntegrandName.fixedData z B) := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [GaussianCompactRiemannName.localBody,GaussianEulerIntegrandName.subst_fixedData,subst_lipschitz,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    local_modulus_at (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C))))
      (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (z R B E T C : PTm n) (h : Γ ⊢[PRAAx] source z R B E T C) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input GaussianEulerIntegrandName.evaluatorF one C E (lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B) :=
  .andI (le_refl one) (.andI h.andE₁.andE₂.andE₁
    (.andI (le_trans (le_add_left C one) h.andE₂) (sampled_modulus z R B E T C h)))

/-- An actual regular compact quadrature name of the ORIGINAL Euler
integrand, with no supplied integrand-modulus or output-name premise. -/
theorem name_regular (z R B E T C : PTm n) (h : Γ ⊢[PRAAx] source z R B E T C) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data z R B E T C) :=
  GaussianCompactRiemannName.name_regular GaussianEulerIntegrandName.evaluatorF _ _ _ _ _ _ (compact_input z R B E T C h)

theorem sample_at (p z R B E T C : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B E T C) ≐ GaussianCompactRiemannName.quadrature GaussianEulerIntegrandName.evaluatorF
      (p+T+num 6) (GaussianCompactRiemannName.mesh p (lipschitz R E T) T) one C E (GaussianEulerIntegrandName.fixedData z B) :=
  GaussianCompactRiemannName.name_at GaussianEulerIntegrandName.evaluatorF p _ _ _ _ _ _

def output (p z R B E T C : PTm n) : PTm n := pairT (ap2 nameF p (data z R B E T C))
  (pairT (lipschitz R E T) (pairT (GaussianCompactRiemannName.mesh p (lipschitz R E T) T) (GaussianCompactRiemannName.precision p T)))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (p z R B E T C : PTm n) : PTm n := PTm.app outputF ![p,z,R,B,E,T,C]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (p z R B E T C : PTm n) :
    Syn.subst σ (output p z R B E T C) = output (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) := by simp [output]
theorem program_at (p z R B E T C : PTm n) : Γ ⊢[PRAAx] run p z R B E T C ≐ output p z R B E T C := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![p,z,R,B,E,T,C]
theorem returned_sample (p z R B E T C : PTm n) : Γ ⊢[PRAAx]
    fstT (run p z R B E T C) ≐ GaussianCompactRiemannName.quadrature GaussianEulerIntegrandName.evaluatorF
      (p+T+num 6) (GaussianCompactRiemannName.mesh p (lipschitz R E T) T) one C E (GaussianEulerIntegrandName.fixedData z B) :=
  (congrFst (program_at p z R B E T C)).eqTrans ((fst_pair _ _).eqTrans (sample_at p z R B E T C))
theorem returned_tail (p z R B E T C : PTm n) : Γ ⊢[PRAAx]
    sndT (run p z R B E T C) ≐ pairT (lipschitz R E T)
      (pairT (GaussianCompactRiemannName.mesh p (lipschitz R E T) T) (GaussianCompactRiemannName.precision p T)) :=
  (congrSnd (program_at p z R B E T C)).eqTrans (snd_pair _ _)
theorem returned_modulus (p z R B E T C : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p z R B E T C)) ≐ lipschitz R E T := (congrFst (returned_tail p z R B E T C)).eqTrans (fst_pair _ _)
theorem returned_schedules (p z R B E T C : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run p z R B E T C)) ≐ pairT (GaussianCompactRiemannName.mesh p (lipschitz R E T) T) (GaussianCompactRiemannName.precision p T) :=
  (congrSnd (returned_tail p z R B E T C)).eqTrans (snd_pair _ _)

theorem original_Euler_integrand_verified_sampled_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      GaussianCompactRiemannName.sampledModulus GaussianEulerIntegrandName.evaluatorF one (var 5) (var 3)
        (lipschitz (var 1) (var 3) (var 4)) (GaussianEulerIntegrandName.fixedData (var 0) (var 2))) :=
  closeUniv 6 (.impI (sampled_modulus _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_Euler_compact_quadrature_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (name_regular _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_Euler_compact_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ≐
      GaussianCompactRiemannName.quadrature GaussianEulerIntegrandName.evaluatorF (var 0+var 5+num 6)
        (GaussianCompactRiemannName.mesh (var 0) (lipschitz (var 2) (var 4) (var 5)) (var 5)) one (var 6) (var 4)
        (GaussianEulerIntegrandName.fixedData (var 1) (var 3))) := closeUniv 7 (sample_at _ _ _ _ _ _ _)
theorem actual_Euler_compact_modulus_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerCompactModulus
