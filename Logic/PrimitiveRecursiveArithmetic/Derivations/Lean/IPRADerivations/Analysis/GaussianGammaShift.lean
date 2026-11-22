import IPRADerivations.Analysis.GaussianGammaFunctionalEquation
import IPRADerivations.Analysis.GaussianGammaReciprocalInverse
import IPRADerivations.Analysis.GaussianRobinMeshExponential

/-!
# The original Gamma shift on its two actual pole-free domains

The radius at z+1 is the derived R+1. Each original reciprocal name
retains its own cleared pole separation and computed anchor height.
The original C20 identity and actual named ring products prove that
(z/B)*Gamma(z/B) is the actual inverse of P(z/B+1). No division by
z/B and no shifted Gamma output law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaReciprocalInverse (gammaF gammaData gammaHeight gamma_regular gamma_product)
open GaussianGammaFunctionalEquation (allLogInverse leftLimitF leftLimitData original_C20_shift)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNameRingLaws (oneF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Original z-domain and original shifted pole separation. The shifted
native disk itself is derived from the first original disk. -/
def input (z R B a d e f : PTm n) : Fm PTm n := GaussianGammaReciprocalInverse.source z R B a d ⋏
  (le one e ⋏ (le one f ⋏ GaussianGammaEulerHeadLower.poleGuard (shifted z B) B e f (two*(R+one))))

def shiftF : PR 2 := multiplyF constantF gammaF
def shiftData (z R B d : PTm n) : PTm n := multiplyData constantF gammaF (ofGaussian z B) (gammaData z R B d)
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (z R B a d e f : PTm n) :
    (input z R B a d e f).subst σ = input (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ e) (Syn.subst σ f) := by simp [input]
@[simp] theorem subst_shiftData {l : ℕ} (σ : Fin n → PTm l) (z R B d : PTm n) :
    Syn.subst σ (shiftData z R B d) = shiftData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by
  simp [shiftData,gammaData,gammaHeight]

theorem shifted_source (z R B a d e f : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (shifted z B) (R+one) B e f :=
  .andI (GaussianGammaEulerShiftLimit.shifted_source z R B h.andE₁.andE₁)
    (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂))

theorem shift_regular (z R B a d : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d) : Γ ⊢[PRAAx]
    pointCN shiftF (shiftData z R B d) := multiply_fast _ _ _ _ (constant_regular _) (gamma_regular z R B a d h)

/-- The source C20 reciprocal identity makes the actual shifted candidate
an inverse. Every product and operand data is the existing original program. -/
theorem shifted_candidate_product (z R B a d e f : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f)
    (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF GaussianGammaC7Name.nameF shiftF) oneF
      (multiplyData GaussianGammaC7Name.nameF shiftF
        (GaussianGammaC7Name.data (shifted z B) (R+one) B) (shiftData z R B d))
      (GaussianGammaC7Name.data (shifted z B) (R+one) B) := by
  let P := GaussianGammaC7Name.nameF
  let x := ofGaussian z B
  let S := GaussianGammaC7Name.data (shifted z B) (R+one) B
  let Z := GaussianGammaC7Name.data z R B
  let G := gammaData z R B d
  have hp : Γ ⊢[PRAAx] pointCN P Z := GaussianGammaC7Name.name_regular z R B h.andE₁.andE₁
  have hs : Γ ⊢[PRAAx] pointCN P S := GaussianGammaC7Name.name_regular _ _ _ (shifted_source z R B a d e f h).andE₁
  have hx := constant_regular (Γ := Γ) x
  have hg := gamma_regular z R B a d h.andE₁
  have swap := GaussianNameRingLaws.multiply_commutative P constantF S x hs hx
  have liftSwap := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF P constantF) (multiplyF constantF P) gammaF gammaF
    (multiplyData P constantF S x) (multiplyData constantF P x S) G G
    (multiply_fast _ _ _ _ hs hx) (multiply_fast _ _ _ _ hx hs) hg hg swap (cross_refl _ _ hg)
  have c20 := original_C20_shift z R B h.andE₁.andE₁ hi
  have liftC20 := GaussianGammaAdjacentCutoff.multiply_cross leftLimitF P gammaF gammaF
    (leftLimitData z R B) Z G G (GaussianGammaFunctionalEquation.left_limit_regular z R B h.andE₁.andE₁)
    hp hg hg c20 (cross_refl _ _ hg)
  have assoc := GaussianNameRingLaws.multiply_associative P constantF gammaF S x G hs hx hg
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc)
    (cross_trans _ _ _ _ _ _ liftSwap (cross_trans _ _ _ _ _ _ liftC20
      (cross_trans _ _ _ _ _ _ (gamma_product z R B a d h.andE₁) (GaussianBoundedInverseApartness.ones_equivalent Z S))))

/-- C21 for the SAME original Gamma name on z and z+1. Independent
pole guards and reciprocal anchor heights are retained exactly. -/
theorem original_Gamma_shift (z R B a d e f : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f)
    (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    crossEquivalent gammaF shiftF (gammaData (shifted z B) (R+one) B f) (shiftData z R B d) := by
  have target := (GaussianGammaReciprocalInverse.original_gamma_inverse (shifted z B) (R+one) B e f
    (shifted_source z R B a d e f h)).andE₁
  exact GaussianBoundedInverseApartness.reciprocal_matches_inverse GaussianGammaC7Name.nameF shiftF
    (gammaHeight (shifted z B) (R+one) B f) (GaussianGammaC7Name.data (shifted z B) (R+one) B)
    (shiftData z R B d) target.andE₁ (shift_regular z R B a d h.andE₁) target.andE₂
    (shifted_candidate_product z R B a d e f h hi)


/-- The mesh-log exponential provider is proved from the original Robin
programs, so only the two original pole-free domains remain as inputs. -/
theorem C21_Gamma_shift (z R B a d e f : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f) : Γ ⊢[PRAAx]
    crossEquivalent gammaF shiftF (gammaData (shifted z B) (R+one) B f) (shiftData z R B d) :=
  original_Gamma_shift z R B a d e f h GaussianRobinMeshExponential.all_mesh_exponential_inverses

/-- The two separation numerators a,e are proof inputs. The original
samplers themselves use only their original denominators d,f. -/
def output (p q z R B d f : PTm n) : PTm n :=
  pairT (ap2 gammaF p (gammaData (shifted z B) (R+one) B f)) (ap2 shiftF q (shiftData z R B d))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (p q z R B d f : PTm n) : PTm n := PTm.app outputF ![p,q,z,R,B,d,f]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (p q z R B d f : PTm n) :
    Syn.subst σ (output p q z R B d f) = output (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) (Syn.subst σ f) := by
  simp [output,gammaData,gammaHeight]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (p q z R B d f : PTm n) :
    Syn.subst σ (run p q z R B d f) = run (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) (Syn.subst σ f) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (p q z R B d f : PTm n) : Γ ⊢[PRAAx] run p q z R B d f ≐ output p q z R B d f := by
  simpa [run,outputF] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![p,q,z,R,B,d,f]
theorem returned_shifted_Gamma (p q z R B d f : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q z R B d f) ≐ ap2 gammaF p (gammaData (shifted z B) (R+one) B f) :=
  (congrFst (program_at p q z R B d f)).eqTrans (fst_pair _ _)
theorem returned_original_product (p q z R B d f : PTm n) : Γ ⊢[PRAAx]
    sndT (run p q z R B d f) ≐ ap2 shiftF q (shiftData z R B d) :=
  (congrSnd (program_at p q z R B d f)).eqTrans (snd_pair _ _)
theorem returned_distance (p q z R B a d e f : PTm n) (h : Γ ⊢[PRAAx] input z R B a d e f) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p q z R B d f)) (sndT (run p q z R B d f)) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_shifted_Gamma p q z R B d f).eqSymm
    (returned_original_product p q z R B d f).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.cross_at _ _ _ _ p q (C21_Gamma_shift z R B a d e f h))

theorem original_shifted_pole_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianGammaReciprocalInverse.source (shifted (var 0) (var 2)) (var 1+one) (var 2) (var 5) (var 6)) :=
  closeUniv 7 (.impI (shifted_source _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_shifted_Gamma_inverse_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent (multiplyF GaussianGammaC7Name.nameF shiftF) oneF
        (multiplyData GaussianGammaC7Name.nameF shiftF
          (GaussianGammaC7Name.data (shifted (var 0) (var 2)) (var 1+one) (var 2))
          (shiftData (var 0) (var 1) (var 2) (var 4)))
        (GaussianGammaC7Name.data (shifted (var 0) (var 2)) (var 1+one) (var 2))) :=
  closeUniv 7 (.impI (shifted_candidate_product _ _ _ _ _ _ _ Prf.hyp0 GaussianRobinMeshExponential.all_mesh_exponential_inverses))

theorem original_C21_Gamma_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent gammaF shiftF
        (gammaData (shifted (var 0) (var 2)) (var 1+one) (var 2) (var 6))
        (shiftData (var 0) (var 1) (var 2) (var 4))) :=
  closeUniv 7 (.impI (C21_Gamma_shift _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_Gamma_shift_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (program_at _ _ _ _ _ _ _)

theorem actual_returned_original_C21_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 8)))
        (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 8)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 9 (.impI (returned_distance _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaShift
