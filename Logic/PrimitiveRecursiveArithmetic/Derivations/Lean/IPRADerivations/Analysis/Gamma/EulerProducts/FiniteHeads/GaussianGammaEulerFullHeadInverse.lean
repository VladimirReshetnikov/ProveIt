import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaEulerReciprocalInverse
import IPRADerivations.Analysis.Trigonometry.SineProducts.Bounds.GaussianSineProductReflectionLower

/-!
# The original finite Euler inverse with its full rational head

The finite Euler reciprocal equals the product of the reciprocal of the
original head through cutoff (N) and the exponential of the negated
original logarithmic exponent. The finite pole guard supplies the
reciprocal for the entire head by a direct bound beyond the original disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerFullHeadInverse

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadLower (poleAt poleGuard pole_at returned_inverse_identity)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData eulerHeight original_euler_inverse)
open GaussianGammaFiniteApproximantName
  (logExponentF logExponentData log_exponent_regular exponential_input qF qData)
open GaussianGammaReciprocalInverse (inverse_pairs constant_inverse)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNameRingLaws (negativeF negativeData oneF)
open GaussianRationalReciprocal (reciprocal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def headInverse (z B N : PTm n) : PTm n := reciprocal (GaussianGammaEulerHead.run z B N)
def radius (z B N : PTm n) : PTm n := GaussianNameBounds.U logExponentF (logExponentData z B N)
def negExpF : PR 2 := GaussianRadiusExponentialName.nameF (negativeF logExponentF)
def negExpData (z B N : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (radius z B N) (negativeData (logExponentData z B N))
def nameF : PR 2 := multiplyF constantF negExpF
def data (z B N : PTm n) : PTm n :=
  multiplyData constantF negExpF (headInverse z B N) (negExpData z B N)

@[simp] theorem subst_headInverse {l : ℕ} (σ : Fin n → PTm l) (z B N : PTm n) :
    Syn.subst σ (headInverse z B N) = headInverse (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  have e : Syn.subst σ (GaussianGammaEulerHead.run z B N) =
      GaussianGammaEulerHead.run (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
    change ConciseIPRA.PTm.app GaussianGammaEulerHead.headF (fun i => Syn.subst σ (![z,B,N] i)) =
      ConciseIPRA.PTm.app GaussianGammaEulerHead.headF ![Syn.subst σ z,Syn.subst σ B,Syn.subst σ N]
    congr 1
    funext i
    fin_cases i <;> rfl
  simp only [headInverse,GaussianRationalReciprocal.subst_reciprocal,e]

ipra_subst radius [logExponentData]

ipra_subst negExpData [logExponentData]

ipra_subst data

theorem extended_guard (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d) :
    Γ ⊢[PRAAx] poleGuard z B one d N := by
  refine .allI (.impI ?_)
  let i : PTm (n+1) := var 0
  let sh (t : PTm n) := Syn.shift t
  let Δ := le i (sh N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (sh z) (sh R) (sh B) (sh a) (sh d) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.wk
  have safe : Δ ⊢[PRAAx] le (succ (sh R)) (succ (two*sh R)) :=
    le_of_eq_add (d := sh R) (by ipra_ring)
  have result : Δ ⊢[PRAAx] poleAt (sh z) (sh B) one (sh d) i := by
    refine .orE (lt_or_le (two*sh R) i) ?_ ?_
    · exact GaussianSineProductReflectionLower.automatic_pole_at (sh z) (sh R) (sh B) one (sh d) i
        hs.andE₁.andE₂.andE₂.wk hs.andE₂.andE₂.andE₁.wk (le_trans safe.wk Prf.hyp0)
    · have step : le i (two*sh R) :: Δ ⊢[PRAAx] le (one*sh B) (sh a*sh B) :=
        le_mul_mono hs.andE₂.andE₁.wk (le_refl (sh B))
      exact le_trans (le_mul_mono step step)
        (pole_at (sh z) (sh B) (sh a) (sh d) (two*sh R) i hs.andE₂.andE₂.andE₂.wk Prf.hyp0)
  simpa only [i,Δ,sh,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using result

theorem exponent_input (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input logExponentF (radius z B N) (logExponentData z B N) :=
  exponential_input logExponentF (logExponentData z B N) (log_exponent_regular z B N hN)

theorem negative_exponential_regular (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN negExpF (negExpData z B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianExponentialInverse.negative_input _ _ _ (exponent_input z B N hN))

theorem name_regular (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN nameF (data z B N) :=
  multiply_fast constantF negExpF (headInverse z B N) (negExpData z B N)
    (constant_regular _) (negative_exponential_regular z B N hN)

theorem inverse_product (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF qF nameF) oneF
      (multiplyData qF nameF (qData z B N) (data z B N)) (qData z B N) := by
  let F := GaussianRadiusExponentialName.nameF logExponentF
  let X := logExponentData z B N
  let W := radius z B N
  let H := GaussianGammaEulerHead.run z B N
  let E := GaussianRadiusExponentialName.data W X
  let ref := qData z B N
  have ha := returned_inverse_identity z B one d N h.andE₁.andE₂.andE₁ (le_refl one) h.andE₂.andE₂.andE₁
    (extended_guard z R B a d N h)
  have hc := constant_inverse H (headInverse z B N) ref ha
  have he := exponent_input z B N hN
  have pair := cross_trans _ _ _ _ _ _ (GaussianExponentialInverse.exponential_inverse logExponentF W X he)
    (GaussianBoundedInverseApartness.ones_equivalent X ref)
  exact inverse_pairs constantF F constantF negExpF H E (headInverse z B N) (negExpData z B N) ref
    (constant_regular H) (GaussianRadiusExponentialName.name_regular logExponentF W X he)
    (constant_regular _) (negative_exponential_regular z B N hN) hc pair

theorem cutoff_positive (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source z R B a d N) :
    Γ ⊢[PRAAx] le one N :=
  le_trans h.andE₁.andE₁.andE₁ (le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right R R)) h.andE₂)

theorem original_factorization (z R B a d N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source z R B a d N) :
    Γ ⊢[PRAAx] crossEquivalent eulerF nameF (eulerData z R B d N) (data z B N) := by
  have hi := (original_euler_inverse z R B a d N h).andE₁
  have hN := cutoff_positive z R B a d N h
  exact GaussianBoundedInverseApartness.reciprocal_matches_inverse qF nameF (eulerHeight z R B d N)
    (qData z B N) (data z B N) hi.andE₁ (name_regular z B N hN) hi.andE₂
    (inverse_product z R B a d N h.andE₁ hN)

theorem actual_full_Euler_head_inverse_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaEulerReciprocalInverse.source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent eulerF nameF (eulerData (var 0) (var 1) (var 2) (var 4) (var 5)) (data (var 0) (var 2) (var 5))) :=
  closeUniv 6 (.impI (original_factorization _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerFullHeadInverse
