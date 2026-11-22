import IPRADerivations.Analysis.GaussianRationalUniformExponentialLipschitz
import IPRADerivations.Analysis.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.GaussianRadiusExponentialName

/-!
# Original common-radius exponential names preserve a Lipschitz rate

The SAME original two output samplers use a common actual cutoff and
input clock. The genuine uniform finite exponential bound derives their
real diagonal variation. Existing finite integer-gap removal gives the
sharp independent output observation errors. No completed-exponential
variation or output estimate is supplied as a hypothesis.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRadiusExponentialLipschitzRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRadiusExponentialName (query inputPrecision sample sample_at nameF data)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def factor (R : PTm n) : PTm n := pw (num 3) R
def input (F G : PR 2) (R x y A N : PTm n) : Fm PTm n := le one N ⋏
  (GaussianRadiusExponentialName.input F R x ⋏ (GaussianRadiusExponentialName.input G R y ⋏ independentRate F G x y A N))
@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (factor R) = factor (Syn.subst σ R) := by simp [factor]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (R x y A N : PTm n) :
    (input F G R x y A N).subst σ = input F G (Syn.subst σ R) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A) (Syn.subst σ N) := by simp [input]

theorem original_clock_later (R p : PTm n) : Γ ⊢[PRAAx] le p (inputPrecision R p) :=
  le_of_eq_add (d := num 4+(R+two)*GaussianRadiusExponentialName.index R p) (by unfold inputPrecision; ipra_ring)

theorem diagonal (F G : PR 2) (R x y A N p : PTm n) (h : Γ ⊢[PRAAx] input F G R x y A N) : Γ ⊢[PRAAx]
    distanceBounded (sample F R p x) (sample G R p y)
      ((factor R*A)*unit p+(two*factor R)*N) (N*unit p) := by
  let t := inputPrecision R p
  have n := h.andE₁
  have old := GaussianNamedInverseRate.diagonal_rate F G x y A N t n h.andE₂.andE₂.andE₂
  have finite := GaussianRationalUniformExponentialLipschitz.scalar_sum_lipschitz
    (query F R p x) (query G R p y) R (A*unit t+two*N) (N*unit t) (GaussianRadiusExponentialName.index R p)
    (positive_product _ _ n (unit_positive t)) (GaussianRadiusExponentialName.query_bound F R x p h.andE₂.andE₁)
    (GaussianRadiusExponentialName.query_bound G R y p h.andE₂.andE₂.andE₁) old
  have actual := distance_congr (sample_at F R p x).eqSymm (sample_at G R p y).eqSymm (.eqRefl _) (.eqRefl _) finite
  have grow : Γ ⊢[PRAAx] le (unit p) (unit t) :=
    GaussianFactorBudget.power_monotone_length two p t (le_succ_self one) (original_clock_later R p)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ n (unit_positive t)) (positive_product _ _ n (unit_positive p)) _ actual
  dsimp only [factor]
  ipra_le (2*𝔞(pw (num 3) R)*𝔞(N)*𝔞(N))*sl grow

theorem diagonal_envelope (F G : PR 2) (R x y A N : PTm n) (h : Γ ⊢[PRAAx] input F G R x y A N) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope (nameF F) (nameF G) (data R x) (data R y) (factor R*A) N (two*factor R) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input F G (Syn.shift R) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,sample,GaussianRadiusExponentialName.subst_data,
    subst_factor,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using diagonal F G (Syn.shift R) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift N) (var 0) hs

/-- Sharp independent errors at the actual original exponential programs. -/
theorem independent_rate (F G : PR 2) (R x y A N : PTm n) (h : Γ ⊢[PRAAx] input F G R x y A N) : Γ ⊢[PRAAx]
    independentRate (nameF F) (nameF G) (data R x) (data R y) (factor R*A) N :=
  GaussianNamedLipschitzRate.independent_rate (nameF F) (nameF G) (data R x) (data R y) (factor R*A) N (two*factor R)
    h.andE₁ (GaussianRadiusExponentialName.name_regular F R x h.andE₂.andE₁)
    (GaussianRadiusExponentialName.name_regular G R y h.andE₂.andE₂.andE₁) (diagonal_envelope F G R x y A N h)

theorem observations (F G : PR 2) (R x y A N p q : PTm n) (h : Γ ⊢[PRAAx] input F G R x y A N) : Γ ⊢[PRAAx]
    distanceBounded (sample F R p x) (sample G R q y) (rateNumerator (factor R*A) N p q) (rateDenominator N p q) :=
  GaussianNamedInverseRate.rate_at (nameF F) (nameF G) (data R x) (data R y) (factor R*A) N p q (independent_rate F G R x y A N h)


def output (F G : PR 2) (R x y A N p q : PTm n) : PTm n := pairT (sample F R p x)
  (pairT (sample G R q y) (pairT (rateNumerator (factor R*A) N p q) (rateDenominator N p q)))
def outputF (F G : PR 2) : PR 7 := PTm.toPR (output F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (F G : PR 2) (R x y A N p q : PTm n) : PTm n := PTm.app (outputF F G) ![R,x,y,A,N,p,q]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (R x y A N p q : PTm n) :
    Syn.subst σ (output F G R x y A N p q) = output F G (Syn.subst σ R) (Syn.subst σ x) (Syn.subst σ y)
      (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ q) := by simp [output]
theorem program_at (F G : PR 2) (R x y A N p q : PTm n) : Γ ⊢[PRAAx] run F G R x y A N p q ≐ output F G R x y A N p q := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![R,x,y,A,N,p,q]
theorem returned_first (F G : PR 2) (R x y A N p q : PTm n) : Γ ⊢[PRAAx]
    fstT (run F G R x y A N p q) ≐ sample F R p x := (congrFst (program_at F G R x y A N p q)).eqTrans (fst_pair _ _)
theorem returned_tail (F G : PR 2) (R x y A N p q : PTm n) : Γ ⊢[PRAAx]
    sndT (run F G R x y A N p q) ≐ pairT (sample G R q y) (pairT (rateNumerator (factor R*A) N p q) (rateDenominator N p q)) :=
  (congrSnd (program_at F G R x y A N p q)).eqTrans (snd_pair _ _)
theorem returned_second (F G : PR 2) (R x y A N p q : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F G R x y A N p q)) ≐ sample G R q y := (congrFst (returned_tail F G R x y A N p q)).eqTrans (fst_pair _ _)
theorem returned_budget (F G : PR 2) (R x y A N p q : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run F G R x y A N p q)) ≐ pairT (rateNumerator (factor R*A) N p q) (rateDenominator N p q) :=
  (congrSnd (returned_tail F G R x y A N p q)).eqTrans (snd_pair _ _)
theorem returned_numerator (F G : PR 2) (R x y A N p q : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run F G R x y A N p q))) ≐ rateNumerator (factor R*A) N p q :=
  (congrFst (returned_budget F G R x y A N p q)).eqTrans (fst_pair _ _)
theorem returned_denominator (F G : PR 2) (R x y A N p q : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run F G R x y A N p q))) ≐ rateDenominator N p q :=
  (congrSnd (returned_budget F G R x y A N p q)).eqTrans (snd_pair _ _)
theorem returned_distance (F G : PR 2) (R x y A N p q : PTm n) (h : Γ ⊢[PRAAx] input F G R x y A N) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run F G R x y A N p q)) (fstT (sndT (run F G R x y A N p q)))
      (fstT (sndT (sndT (run F G R x y A N p q)))) (sndT (sndT (sndT (run F G R x y A N p q)))) :=
  distance_congr (returned_first F G R x y A N p q).eqSymm (returned_second F G R x y A N p q).eqSymm
    (returned_numerator F G R x y A N p q).eqSymm (returned_denominator F G R x y A N p q).eqSymm
    (observations F G R x y A N p q h)

theorem actual_common_radius_exponential_diagonal_variation_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input F G (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded (sample F (var 0) (var 5) (var 1)) (sample G (var 0) (var 5) (var 2))
      ((factor (var 0)*var 3)*unit (var 5)+(two*factor (var 0))*var 4) (var 4*unit (var 5))) :=
  closeUniv 6 (.impI (diagonal F G _ _ _ _ _ _ Prf.hyp0))
theorem original_common_radius_exponential_independent_rate_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input F G (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ independentRate (nameF F) (nameF G)
      (data (var 0) (var 1)) (data (var 0) (var 2)) (factor (var 0)*var 3) (var 4)) :=
  closeUniv 5 (.impI (independent_rate F G _ _ _ _ _ Prf.hyp0))
theorem original_common_radius_exponential_observations_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input F G (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded (sample F (var 0) (var 5) (var 1)) (sample G (var 0) (var 6) (var 2))
      (rateNumerator (factor (var 0)*var 3) (var 4) (var 5) (var 6)) (rateDenominator (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (observations F G _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_common_radius_exponential_rate_program_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ output F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at F G _ _ _ _ _ _ _)
theorem actual_returned_common_radius_exponential_rate_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input F G (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      distanceBounded (fstT (run F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (fstT (sndT (run F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))
        (fstT (sndT (sndT (run F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))
        (sndT (sndT (sndT (run F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))) :=
  closeUniv 7 (.impI (returned_distance F G _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRadiusExponentialLipschitzRate
