import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaRepeatedShift
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaShift

/-!
# V8 for the actual original Gamma names at every numerical shift

The original reciprocal repeated-shift identity already uses the genuine
finite product of z/B+j. Actual inverse uniqueness turns that identity
into Gamma(z/B+N)=(z/B)_N Gamma(z/B). Only the two original endpoint pole
certificates are supplied. The shifted disk is derived along the actual
native trajectory, and every shift length is an internal parameter.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRisingFactorial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaShiftTrajectory (point point_source)
open GaussianGammaRepeatedShift (risingProduct)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaReciprocalInverse (gammaF gammaData gammaHeight gamma_regular gamma_product)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm cross_at)
open GaussianNameRingLaws (oneF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Independent original endpoint certificates; the endpoint disk itself
is obtained from the original base disk and the native trajectory. -/
def input (z R B a d e f N : PTm n) : Fm PTm n := GaussianGammaReciprocalInverse.source z R B a d ⋏
  (le one e ⋏ (le one f ⋏ GaussianGammaEulerHeadLower.poleGuard (point z B N) B e f (two*(R+N))))
def risingF : PR 2 := multiplyF constantF gammaF
def risingData (z R B d N : PTm n) : PTm n := multiplyData constantF gammaF
  (risingProduct z B N) (gammaData z R B d)
def endpointData (z R B f N : PTm n) : PTm n := gammaData (point z B N) (R+N) B f

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z R B a d e f N : PTm n) :
    (input z R B a d e f N).subst σ = input (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ N) := by simp [input]
@[simp] theorem subst_risingData {m : ℕ} (σ : Fin n → PTm m) (z R B d N : PTm n) :
    Syn.subst σ (risingData z R B d N) = risingData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ d) (Syn.subst σ N) := by simp [risingData,gammaData,gammaHeight]
@[simp] theorem subst_endpointData {m : ℕ} (σ : Fin n → PTm m) (z R B f N : PTm n) :
    Syn.subst σ (endpointData z R B f N) = endpointData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ f) (Syn.subst σ N) := by simp [endpointData,gammaData,gammaHeight]

theorem endpoint_source (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (point z B N) (R+N) B e f :=
  .andI (point_source z R B N h.andE₁.andE₁)
    (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂))

theorem rising_regular (z R B a d N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d) : Γ ⊢[PRAAx]
    pointCN risingF (risingData z R B d N) := multiply_fast _ _ _ _ (constant_regular _) (gamma_regular z R B a d h)

theorem endpoint_regular (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    pointCN gammaF (endpointData z R B f N) := gamma_regular _ _ _ _ _ (endpoint_source z R B a d e f N h)

/-- The original reciprocal product at the endpoint times the actual
rising-factorial candidate equals one by multiplication alone. -/
theorem endpoint_candidate_product (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF GaussianGammaC7Name.nameF risingF) oneF
      (multiplyData GaussianGammaC7Name.nameF risingF
        (GaussianGammaC7Name.data (point z B N) (R+N) B) (risingData z R B d N))
      (GaussianGammaC7Name.data (point z B N) (R+N) B) := by
  let P := GaussianGammaC7Name.nameF
  let x := risingProduct z B N
  let S := GaussianGammaC7Name.data (point z B N) (R+N) B
  let Z := GaussianGammaC7Name.data z R B
  let G := gammaData z R B d
  have hp : Γ ⊢[PRAAx] pointCN P Z := GaussianGammaC7Name.name_regular z R B h.andE₁.andE₁
  have hs : Γ ⊢[PRAAx] pointCN P S := GaussianGammaC7Name.name_regular _ _ _ (endpoint_source z R B a d e f N h).andE₁
  have hx := constant_regular (Γ := Γ) x
  have hg := gamma_regular z R B a d h.andE₁
  have swap := GaussianNameRingLaws.multiply_commutative P constantF S x hs hx
  have liftSwap := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF P constantF) (multiplyF constantF P) gammaF gammaF
    (multiplyData P constantF S x) (multiplyData constantF P x S) G G
    (multiply_fast _ _ _ _ hs hx) (multiply_fast _ _ _ _ hx hs) hg hg swap (cross_refl _ _ hg)
  have repeated := GaussianGammaRepeatedShift.repeated_shift z R B N h.andE₁.andE₁
  have liftRepeated := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF constantF P) P gammaF gammaF
    (multiplyData constantF P x S) Z G G (multiply_fast _ _ _ _ hx hs) hp hg hg
    (cross_symm _ _ _ _ repeated) (cross_refl _ _ hg)
  have assoc := GaussianNameRingLaws.multiply_associative P constantF gammaF S x G hs hx hg
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc)
    (cross_trans _ _ _ _ _ _ liftSwap (cross_trans _ _ _ _ _ _ liftRepeated
      (cross_trans _ _ _ _ _ _ (gamma_product z R B a d h.andE₁) (GaussianBoundedInverseApartness.ones_equivalent Z S))))

/-- Source V8 for the SAME original Gamma samplers and the original
finite rising product, including the empty numerical product N=0. -/
theorem original_Gamma_rising_factorial (z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    crossEquivalent gammaF risingF (endpointData z R B f N) (risingData z R B d N) := by
  have target := (GaussianGammaReciprocalInverse.original_gamma_inverse (point z B N) (R+N) B e f
    (endpoint_source z R B a d e f N h)).andE₁
  exact GaussianBoundedInverseApartness.reciprocal_matches_inverse GaussianGammaC7Name.nameF risingF
    (gammaHeight (point z B N) (R+N) B f) (GaussianGammaC7Name.data (point z B N) (R+N) B)
    (risingData z R B d N) target.andE₁ (rising_regular z R B a d N h.andE₁) target.andE₂
    (endpoint_candidate_product z R B a d e f N h)

theorem original_observations (p q z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 gammaF p (endpointData z R B f N)) (ap2 risingF q (risingData z R B d N))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_Gamma_rising_factorial z R B a d e f N h)

/-- Actual independently queried endpoint Gamma, finite polynomial
multiplier, and normalized product candidate returned by one PR program. -/
def output (p q z R B d f N : PTm n) : PTm n := pairT (ap2 gammaF p (endpointData z R B f N))
  (pairT (risingProduct z B N) (ap2 risingF q (risingData z R B d N)))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (p q z R B d f N : PTm n) : PTm n := PTm.app outputF ![p,q,z,R,B,d,f,N]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (p q z R B d f N : PTm n) :
    Syn.subst σ (output p q z R B d f N) = output (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) (Syn.subst σ f) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (p q z R B d f N : PTm n) :
    Syn.subst σ (run p q z R B d f N) = run (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) (Syn.subst σ f) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (p q z R B d f N : PTm n) : Γ ⊢[PRAAx] run p q z R B d f N ≐ output p q z R B d f N := by
  have decoded : Syn.subst ![p,q,z,R,B,d,f,N]
      (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) = output p q z R B d f N := by
    simp only [subst_output,Syn.subst_var]
    rfl
  simpa only [run,outputF,decoded] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![p,q,z,R,B,d,f,N]

theorem returned_endpoint (p q z R B d f N : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q z R B d f N) ≐ ap2 gammaF p (endpointData z R B f N) :=
  (congrFst (program_at p q z R B d f N)).eqTrans (fst_pair _ _)
theorem returned_product (p q z R B d f N : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p q z R B d f N)) ≐ risingProduct z B N :=
  (congrFst ((congrSnd (program_at p q z R B d f N)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_candidate (p q z R B d f N : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run p q z R B d f N)) ≐ ap2 risingF q (risingData z R B d N) :=
  (congrSnd ((congrSnd (program_at p q z R B d f N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_distance (p q z R B a d e f N : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f N) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p q z R B d f N)) (sndT (sndT (run p q z R B d f N)))
      (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_endpoint p q z R B d f N).eqSymm
    (returned_candidate p q z R B d f N).eqSymm (.eqRefl _) (.eqRefl _) (original_observations p q z R B a d e f N h)

theorem actual_original_rising_factorial_endpoint_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianGammaReciprocalInverse.source (point (var 0) (var 2) (var 7)) (var 1+var 7) (var 2) (var 5) (var 6)) :=
  closeUniv 8 (.impI (endpoint_source _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_Gamma_rising_factorial_V8_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      crossEquivalent gammaF risingF (endpointData (var 0) (var 1) (var 2) (var 6) (var 7))
        (risingData (var 0) (var 1) (var 2) (var 4) (var 7))) :=
  closeUniv 8 (.impI (original_Gamma_rising_factorial _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_Gamma_V8_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (ap2 gammaF (var 0) (endpointData (var 2) (var 3) (var 4) (var 8) (var 9)))
        (ap2 risingF (var 1) (risingData (var 2) (var 3) (var 4) (var 6) (var 9)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_Gamma_V8_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) := closeUniv 8 (program_at _ _ _ _ _ _ _ _)
theorem actual_returned_original_Gamma_V8_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 8) (var 9)))
        (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 8) (var 9))))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (returned_distance _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaRisingFactorial
