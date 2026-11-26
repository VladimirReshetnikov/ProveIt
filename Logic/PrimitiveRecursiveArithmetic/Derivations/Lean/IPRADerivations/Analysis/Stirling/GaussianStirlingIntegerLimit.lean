import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingIntegerTail
import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpScheduledApproximation
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSchedule

/-!
# Cofinal primitive-recursive name for the integer Stirling limit

At precision (p) the sampler reads the original integer (A) at
argument (2^{p+4}) and precision (p+4). The finite named order
contract proves regularity and the (1/(12i)) tail against the original
(A(i)), with both independent observation tolerances.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingIntegerLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingIntegerTail (point integerTailContract tailDen den_positive after_congr point_congr integer_source
  mixedNumerator mixedDenominator mixed_den_positive anchored_left anchored_right)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def clock (p : PTm n) : PTm n := p+num 4
def index (p : PTm n) : PTm n := unit (clock p)
def sample (p : PTm n) : PTm n := point (clock p) (index p)
def nameF : PR 2 := PTm.toPR (sample (var 0) : PTm 2)

@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (clock p) = clock (Syn.subst σ p) := by simp [clock]
@[simp] theorem subst_index {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (index p) = index (Syn.subst σ p) := by simp [index]
@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (sample p) = sample (Syn.subst σ p) := by simp [sample]

theorem name_at (p x : PTm n) : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p := by
  simpa [nameF,ap2] using toPR_eq (Γ := Γ) (sample (var 0) : PTm 2) ![p,x]

theorem index_positive (p : PTm n) : Γ ⊢[PRAAx] le one (index p) := unit_positive (clock p)
theorem index_value (p : PTm n) : Γ ⊢[PRAAx] index p ≐ num 16*unit p :=
  GaussianEulerSharpScheduledApproximation.four_bit_identity p
theorem index_budget (p : PTm n) : Γ ⊢[PRAAx] le (num 10*unit p) (index p) :=
  le_congr (.eqRefl _) (index_value p).eqSymm (by ipra_le 6*𝔞 (unit p))
theorem index_dominates_unit (p : PTm n) : Γ ⊢[PRAAx] le (unit p) (index p) :=
  GaussianExponentialReference.unit_monotone (le_add_right p (num 4))

theorem cofinal_index (i : PTm n) : Γ ⊢[PRAAx] le i (index (GaussianRootSchedule.binaryLength i)) :=
  le_trans (GaussianRootSchedule.binary_length_correct i).andE₁ (index_dominates_unit _)

theorem name_real (x : PTm n) : Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples nameF x := by
  refine .allI ?_
  let p : PTm (n+1) := var 0
  let X := Syn.shift x
  let Δ := Γ.map Fm.shift
  let k := index p
  have real := GaussianStirlingNames.name_real (Γ := Δ) k one (integer_source k (index_positive p))
  have s := GaussianSignedNameExponentialOrder.real_sample_at _ _ (clock p) real
  let e := name_at (Γ := Δ) p X
  exact .andI (GaussianRationalHorner.canonical_congr e s.andE₁)
    (RationalGaussianEmbedding.axis_congr e.eqSymm s.andE₂)

private theorem anchor_budget (p t : PTm n) :
    Γ ⊢[PRAAx] le (mixedNumerator (clock p) t (index p)*(unit p*unit t))
      ((unit p+unit t)*mixedDenominator (clock p) t (index p)) := by
  let P := unit p
  let W := unit t
  let V := index p
  let D := tailDen V
  have lift : Γ ⊢[PRAAx] le (num 10*P) V := index_budget p
  have den : Γ ⊢[PRAAx] le V D := by dsimp only [D,tailDen]; ipra_le 11*𝔞 V
  change Γ ⊢[PRAAx] le ((V*W+D*(V+num 9*W))*(P*W)) ((P+W)*(D*(V*W)))
  ipra_le (𝔞 W)^2*𝔞 D*sl lift + (𝔞 W)^2*𝔞 P*sl den

theorem later_integer_distance (p t j : PTm n) (hj : Γ ⊢[PRAAx] le (index p) j)
    (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (sample p) (point t j) (unit p+unit t) (unit p*unit t) := by
  let k := index p
  let N := monus j k
  have hk := index_positive (Γ := Γ) p
  have same := distance_congr (.eqRefl _) (point_congr t (after_congr k j hj)) (.eqRefl _) (.eqRefl _)
    (anchored_left (clock p) t k N hk h)
  exact distance_radius_mono _ _ _ _ _ _ (mixed_den_positive _ _ _ hk)
    (positive_product _ _ (unit_positive p) (unit_positive t)) (anchor_budget p t) same

private theorem cofinal_ordered (p q : PTm n) (hord : Γ ⊢[PRAAx] le (index p) (index q))
    (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (sample p) (sample q) (unit p+unit q) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  let W := index q
  have hr := index_dominates_unit (Γ := Γ) q
  have d := later_integer_distance p (clock q) (index q) hord h
  exact distance_radius_mono _ _ (P+W) (P*W) (P+Q) (P*Q)
    (positive_product _ _ (unit_positive p) (index_positive q))
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (by ipra_le (𝔞 P)^2*sl hr) d

theorem sample_distance (p q : PTm n) (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (sample p) (sample q) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total (index p) (index q)) (cofinal_ordered p q Prf.hyp0 h.wk) ?_
  have d := cofinal_ordered q p Prf.hyp0 h.wk
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) d)

theorem name_regular (x : PTm n) (h : Γ ⊢[PRAAx] integerTailContract) : Γ ⊢[PRAAx] pointCN nameF x := by
  refine .allI (.allI ?_)
  let X := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] integerTailContract := by simpa [Fm.shift,Δ,Syn.shift] using h.shift.shift
  exact distance_congr (name_at (var 1) X).eqSymm (name_at (var 0) X).eqSymm (.eqRefl _) (.eqRefl _)
    (sample_distance (var 1) (var 0) hs)

def tailNumerator (p q i : PTm n) : PTm n := unit p*unit q+tailDen i*(unit p+unit q)
def tailDenominator (p q i : PTm n) : PTm n := tailDen i*(unit p*unit q)

@[simp] theorem subst_tailNumerator {l : ℕ} (σ : Fin n → PTm l) (p q i : PTm n) :
    Syn.subst σ (tailNumerator p q i) = tailNumerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ i) :=
  by simp [tailNumerator]
@[simp] theorem subst_tailDenominator {l : ℕ} (σ : Fin n → PTm l) (p q i : PTm n) :
    Syn.subst σ (tailDenominator p q i) = tailDenominator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ i) :=
  by simp [tailDenominator]

theorem tail_den_positive (p q i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] le one (tailDenominator p q i) :=
  positive_product _ _ (den_positive i hi) (positive_product _ _ (unit_positive p) (unit_positive q))

private theorem endpoint_early (p q i : PTm n) (hi : Γ ⊢[PRAAx] le one i) (ord : Γ ⊢[PRAAx] le i (index q))
    (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (point p i) (sample q) (tailNumerator p q i) (tailDenominator p q i) := by
  let s := clock q
  let P := unit q
  let V := index q
  let W := unit p
  let D := tailDen i
  let N := monus V i
  have d := distance_congr (.eqRefl _) (point_congr s (after_congr i V ord)) (.eqRefl _) (.eqRefl _)
    (anchored_right s p i N hi h)
  have budget := le_trans (show Γ ⊢[PRAAx] le (num 9*P) (num 10*P) by ipra_le 𝔞 P) (index_budget q)
  apply distance_radius_mono _ _ _ _ _ _ (mixed_den_positive s p i hi) (tail_den_positive p q i hi) _ d
  change Γ ⊢[PRAAx] le ((V*W+D*(V+num 9*W))*(D*(W*P))) ((W*P+D*(W+P))*(D*(V*W)))
  ipra_le (𝔞 D)^2*(𝔞 W)^2*sl budget

private theorem endpoint_late (p q i : PTm n) (hi : Γ ⊢[PRAAx] le one i) (ord : Γ ⊢[PRAAx] le (index q) i)
    (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (point p i) (sample q) (tailNumerator p q i) (tailDenominator p q i) := by
  let P := unit p
  let Q := unit q
  have hPQ := positive_product (Γ := Γ) _ _ (unit_positive q) (unit_positive p)
  have d := distance_symmetric _ _ _ _ hPQ (later_integer_distance q p i ord h)
  exact distance_radius_mono _ _ _ _ _ _ hPQ (tail_den_positive p q i hi)
    (by unfold tailNumerator tailDenominator; ipra_le 𝔞 P*𝔞 Q*𝔞 P*𝔞 Q) d

theorem sample_tail (p q i : PTm n) (hi : Γ ⊢[PRAAx] le one i) (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (point p i) (sample q) (tailNumerator p q i) (tailDenominator p q i) :=
  .orE (le_total i (index q)) (endpoint_early p q i hi.wk Prf.hyp0 h.wk) (endpoint_late p q i hi.wk Prf.hyp0 h.wk)

theorem tail_endpoint (p q i x : PTm n) (hi : Γ ⊢[PRAAx] le one i) (h : Γ ⊢[PRAAx] integerTailContract) :
    Γ ⊢[PRAAx] distanceBounded (point p i) (ap2 nameF q x) (tailNumerator p q i) (tailDenominator p q i) :=
  distance_congr (.eqRefl _) (name_at q x).eqSymm (.eqRefl _) (.eqRefl _) (sample_tail p q i hi h)

theorem actual_Stirling_integer_limit_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (integerTailContract ⟶ pointCN nameF (var 0)) :=
  closeUniv 1 (.impI (name_regular _ Prf.hyp0))

theorem actual_Stirling_integer_limit_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((integerTailContract ⋏ le one (var 1)) ⟶
      distanceBounded (point (var 3) (var 1)) (ap2 nameF (var 2) (var 0))
        (tailNumerator (var 3) (var 2) (var 1)) (tailDenominator (var 3) (var 2) (var 1))) :=
  closeUniv 4 (.impI (tail_endpoint _ _ _ _ Prf.hyp0.andE₂ Prf.hyp0.andE₁))

end LeanProofs.IPRA.Analysis.GaussianStirlingIntegerLimit
