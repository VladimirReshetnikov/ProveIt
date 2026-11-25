import IPRADerivations.Analysis.GaussianCyclicSinePositiveRows
import IPRADerivations.Analysis.GaussianCyclicSineSupplement
import IPRADerivations.Analysis.GaussianCyclicSineProductSquare
import IPRADerivations.Analysis.GaussianRationalNonnegativeProducts
import IPRADerivations.Analysis.GaussianRationalSquareCancellation

/-!
# Positive cancellation in the actual cyclic sine product

The first half-turn uses the original chord lower bound. The remaining
indices use its reflected positive margin via supplementary sine.
All encoded factors of the doubled sine product are then nonnegative
on a single cofinal clock. Stable cancellation of squares gives
the unsquared normalization by the modulus.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianCyclicSineProductNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentDivisionAngles (coefficient)
open GaussianCyclicChordSquare (realSine doubledSine)
open GaussianCyclicSinePositiveRows (first_half_upper first_half_nonnegative scalar_nonnegative_of_upper)
open GaussianCyclicSineSupplement (supplementary_sine_distance supplementError)
open GaussianCyclicSineProductSquare (data sineF sine_at index normBudget product_square_error)
open GaussianCyclicExponentialRoots (source)
open GaussianNamedFiniteProduct (sample)
open GaussianRationalNonnegativeProducts (nonnegative nonnegativeRows nonnegative_double sample_nonnegative)
open GaussianRationalSquareCancellation (cancel_square natural_sum_lower)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianCoordinateRadius (coordinates)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open RationalGaussianEmbedding (scalarZero)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def reserve (m : PTm n) : PTm n := (num 14+supplementError)*m
def fine (p m : PTm n) : Fm PTm n := le (reserve m) (unit p)
def clock (p m : PTm n) : PTm n := GaussianCyclicExponentialSeparation.clock m (p+reserve m)

@[simp] theorem subst_reserve {L : ℕ} (σ : Fin n → PTm L) (m : PTm n) :
    Syn.subst σ (reserve m) = reserve (Syn.subst σ m) := by
  simp [reserve,supplementError,GaussianCyclicSineSupplement.unitError,GaussianCyclicSineSupplement.productError,
    GaussianArctangentExponentialPeriod.fullTurnRadius,GaussianArctangentExponentialPeriod.twiceRadius,
    GaussianArctangentQuarterExponential.radius]

theorem clock_later (p m : PTm n) : Γ ⊢[PRAAx] le p (clock p m) :=
  le_trans (le_add_right _ _) (GaussianCyclicExponentialSeparation.clock_later m _)

theorem clock_fine (p m : PTm n) : Γ ⊢[PRAAx] fine (clock p m) m :=
  le_trans (le_trans (le_add_left _ _) (GaussianCyclicExponentialSeparation.clock_later m _))
    (le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow _))

private theorem half_budget (m : PTm n) : Γ ⊢[PRAAx] le (num 14*m) (reserve m) :=
  le_mul_mono (le_add_right (num 14) supplementError) (le_refl _)

private theorem complementary_half (r m : PTm n) (hr : Γ ⊢[PRAAx] lt r m)
    (hlarge : Γ ⊢[PRAAx] le m (two*r)) : Γ ⊢[PRAAx] le (two*monus m r) m := by
  let d := monus m r
  have e : Γ ⊢[PRAAx] m ≐ r+d := eq_add_of_le (le_of_lt hr)
  have c : Γ ⊢[PRAAx] le (d+r) (r+r) :=
    le_congr (e.eqTrans (add_comm _ _)) (by ipra_ring) hlarge
  exact le_congr (by ipra_ring) e.eqSymm
    (le_congr (.eqRefl _) (add_comm _ _) (add_le_add₂ (le_refl d) (le_of_add_le_add_right c)))

private theorem complementary_positive (r m : PTm n) (h : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] le one (monus m r) :=
  le_of_add_le_add_right (le_congr ((succ_eq_add_one r).eqTrans (add_comm _ _))
    ((eq_add_of_le (le_of_lt h)).eqTrans (add_comm _ _)) h)

theorem positive_at (p r m x : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] lt r m)
    (hp : Γ ⊢[PRAAx] fine p m) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE scalarZero (fstT (realSine p r m x)) := by
  have hM := le_trans hr (le_of_lt hm)
  refine .orE (le_total (two*r) m) ?_ ?_
  · exact first_half_nonnegative p r m x (.andI hM.wk Prf.hyp0) hr.wk (le_trans (half_budget m) hp.wk)
  · let Δ := le m (two*r) :: Γ
    let d := monus m r
    let U := unit p
    have hD : Δ ⊢[PRAAx] le one d := complementary_positive r m hm.wk
    have hhalf : Δ ⊢[PRAAx] GaussianArctangentDivisionAngles.source d m :=
      .andI hM.wk (complementary_half r m hm.wk Prf.hyp0)
    have eq : Δ ⊢[PRAAx] r+d ≐ m := (eq_add_of_le (le_of_lt hm.wk)).eqSymm
    have h₁ : Δ ⊢[PRAAx] source r m := .andI hM.wk (le_of_lt hm.wk)
    have h₂ := GaussianCyclicRootHalfAngle.cyclic_source d m hhalf
    have hU := unit_positive (Γ := Δ) p
    have about := distance_symmetric _ _ _ _ hU (supplementary_sine_distance p r d m x h₁ h₂ eq)
    have ext := upper_of_radius _ _ _ _ (coordinates _ _ _ _ hU about).andE₁
    have pre := upper_triangle _ _ _ _ _ _ _ (first_half_upper p d m x hhalf) ext
    have upper' : Δ ⊢[PRAAx] upper (fstT (coefficient d m)) (fstT (realSine p r m x))
        (num 14+supplementError) U :=
      upper_mono _ _ _ _ _ _ (positive_product _ _ hU hU) pre
        (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring))
    exact scalar_nonnegative_of_upper d m _ _ _ hM.wk hU upper'
      (le_trans hp.wk (le_congr (one_mul U) (.eqRefl _)
        (le_mul_mono (le_trans hD (le_of_eq_add (d := d) (by ipra_ring))) (le_refl _))))

private theorem reversed_index (N i : PTm n) (h : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] lt (index N i) N := by
  have eq : Γ ⊢[PRAAx] N ≐ succ i+index N i := eq_add_of_le h
  exact le_of_eq_add (d := i) (eq.eqTrans (by ipra_ring))

theorem nonnegative_rows (p N x : PTm n) (hf : Γ ⊢[PRAAx] fine p (succ N)) :
    Γ ⊢[PRAAx] nonnegativeRows sineF p N (data N x) := by
  refine .allI (.impI ?_)
  let P := Syn.shift p
  let J := Syn.shift N
  let X := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i J :: Γ.map Fm.shift
  let r := succ (index J i)
  let m := succ J
  let u := GaussianCyclicExponentialRoots.sample P r (two*m) X
  have h : Δ ⊢[PRAAx] lt i J := Prf.hyp0
  have hf' : Δ ⊢[PRAAx] fine P m := by simpa [fine,Fm.shift,Syn.shift,Δ,P,J,m] using hf.shift.wk
  have order : Δ ⊢[PRAAx] lt r m :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one (reversed_index J i h))
  have real : Δ ⊢[PRAAx] nonnegative (realSine P r m X) := .andI
    (positive_at P r m X (zero_lt_succ _) order hf') (snd_pair (RationalArithmetic.recode (sndT u)) scalarZero)
  have both := nonnegative_double _ real
  simpa [nonnegativeRows,Syn.shift,P,J,X,i,Δ,r,m] using GaussianRationalNonnegativeProducts.congr
    (sine_at P J X i).eqSymm both

theorem product_real_error (p N x : PTm n) (hf : Γ ⊢[PRAAx] fine p (succ N))
    (hc : Γ ⊢[PRAAx] GaussianCyclicExponentialSeparation.fine (succ N) p) :
    Γ ⊢[PRAAx] distanceBounded (naturalPoint (succ N)) (sample sineF p N (data N x)) (normBudget N) (unit p) :=
  cancel_square _ _ _ _ (unit_positive p)
    (natural_sum_lower (succ N) _ (zero_lt_succ N)
      (sample_nonnegative sineF p N (data N x) (nonnegative_rows p N x hf)).andE₁)
    (product_square_error p N x hc)

theorem actual_cyclic_sine_product_normalization_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (distanceBounded (naturalPoint (succ (var 1)))
        (sample sineF (clock (var 2) (succ (var 1))) (var 1) (data (var 1) (var 0)))
        (normBudget (var 1)) (unit (clock (var 2) (succ (var 1))))) :=
  closeUniv 3 (product_real_error _ _ _ (clock_fine _ _) (GaussianCyclicExponentialSeparation.clock_fine _ _))

end LeanProofs.IPRA.Analysis.GaussianCyclicSineProductNormalization
