import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactModulus
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactQuadratureBoundary

/-!
# Original eta/top Euler quadrature with a verified conservative modulus

The interval endpoints are exactly the original Gamma cutoffs. The
actual original Euler evaluator's modulus is proved, never supplied.
The cell count uses its conservative factor, kept explicitly distinct
from the paper's sharper displayed factor. Regularity is asserted for
each fixed outer cutoff, not for the varying-cutoff improper diagonal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerCompactQuadrature

open_ipra
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianEulerIntegrandName (evaluatorF fixedData)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B : PTm n) : Fm PTm n := le one B ⋏ ComplexLogarithmRemainder.bounded z (R*B)
def localFactor (p A R : PTm n) : PTm n := GaussianEulerCompactModulus.lipschitz R (etaDen p A R) (top p A R)
def conservativeCells (q p A R : PTm n) : PTm n := GaussianCompactRiemannName.mesh q (localFactor p A R) (top p A R)
def data (z R B p A : PTm n) : PTm n :=
  GaussianEulerCompactModulus.data z R B (etaDen p A R) (top p A R) (width p A R)
def nameF : PR 2 := GaussianEulerCompactModulus.nameF
ipra_subst source [ComplexLogarithmRemainder.bounded]
ipra_subst localFactor [etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst conservativeCells [top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst data [etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem original_input (z R B p A : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianEulerCompactModulus.source z R B (etaDen p A R) (top p A R) (width p A R) :=
  .andI (.andI h.andE₁ (.andI (GaussianGammaIntegralCutoffs.eta_den_positive p A R) h.andE₂))
    (le_congr (.eqRefl _) (exact_right_endpoint p A R) (le_refl _))

/-- The ORIGINAL evaluator now has its actual verified local modulus on
exactly [eta,top], from the original disk and denominator alone. -/
theorem original_evaluator_modulus (z R B p A : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.sampledModulus evaluatorF one (width p A R) (etaDen p A R) (localFactor p A R) (fixedData z B) :=
  GaussianEulerCompactModulus.sampled_modulus _ _ _ _ _ _ (original_input z R B p A h)

theorem fixed_interval_regular (z R B p A : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data z R B p A) :=
  GaussianEulerCompactModulus.name_regular _ _ _ _ _ _ (original_input z R B p A h)

theorem original_sample (q z R B p A : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF q (data z R B p A) ≐ GaussianCompactRiemannName.quadrature evaluatorF
      (q+top p A R+num 6) (conservativeCells q p A R) one (width p A R) (etaDen p A R) (fixedData z B) :=
  GaussianEulerCompactModulus.sample_at _ _ _ _ _ _ _

def output (q z R B p A : PTm n) : PTm n := pairT (ap2 nameF q (data z R B p A))
  (pairT (localFactor p A R) (pairT (conservativeCells q p A R) (pairT (etaDen p A R) (top p A R))))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (q z R B p A : PTm n) : PTm n := PTm.app outputF ![q,z,R,B,p,A]
ipra_subst output [etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
theorem program_at (q z R B p A : PTm n) : Γ ⊢[PRAAx] run q z R B p A ≐ output q z R B p A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![q,z,R,B,p,A]
theorem returned_sample (q z R B p A : PTm n) : Γ ⊢[PRAAx]
    fstT (run q z R B p A) ≐ GaussianCompactRiemannName.quadrature evaluatorF
      (q+top p A R+num 6) (conservativeCells q p A R) one (width p A R) (etaDen p A R) (fixedData z B) :=
  (congrFst (program_at q z R B p A)).eqTrans ((fst_pair _ _).eqTrans (original_sample q z R B p A))

theorem original_eta_top_Euler_evaluator_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) ⟶ GaussianCompactRiemannName.sampledModulus evaluatorF one (width (var 3) (var 4) (var 1))
      (etaDen (var 3) (var 4) (var 1)) (localFactor (var 3) (var 4) (var 1)) (fixedData (var 0) (var 2))) :=
  closeUniv 5 (.impI (original_evaluator_modulus _ _ _ _ _ Prf.hyp0))
theorem actual_original_eta_top_Euler_compact_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) ⟶ GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (fixed_interval_regular _ _ _ _ _ Prf.hyp0))
theorem actual_original_eta_top_Euler_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ GaussianCompactRiemannName.quadrature evaluatorF
      (var 0+top (var 4) (var 5) (var 2)+num 6) (conservativeCells (var 0) (var 4) (var 5) (var 2)) one
      (width (var 4) (var 5) (var 2)) (etaDen (var 4) (var 5) (var 2)) (fixedData (var 1) (var 3))) :=
  closeUniv 6 (original_sample _ _ _ _ _ _)
theorem actual_original_eta_top_Euler_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerCompactQuadrature
