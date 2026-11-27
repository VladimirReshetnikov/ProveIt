import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# Original diagonal variation gives the exact independent observation rate

This is a finite original-rational error bridge. Actual regularity of both
original names and a genuine same-precision A/N+C*2^-t estimate derive
A/N+2^-p+2^-q for independent observations. The sole auxiliary precision
is the existing explicit integer-gap query; no limit or name induction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedLipschitzRate

open_ipra
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianNamedInverseRate (rateNumerator rateDenominator independentRate denominator_positive rate_at diagonal_of_later_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def diagonalNumerator (A N C t : PTm n) : PTm n := A*unit t+C*N
def diagonalDenominator (N t : PTm n) : PTm n := N*unit t
def diagonalEnvelope (F G : PR 2) (x y A N C : PTm n) : Fm PTm n := .all
  (distanceBounded (ap2 F (var 0) (Syn.shift x)) (ap2 G (var 0) (Syn.shift y))
    (diagonalNumerator (Syn.shift A) (Syn.shift N) (Syn.shift C) (var 0))
    (diagonalDenominator (Syn.shift N) (var 0)))
def input (F G : PR 2) (x y A N C : PTm n) : Fm PTm n := le one N ⋏
  (pointCN F x ⋏ (pointCN G y ⋏ diagonalEnvelope F G x y A N C))
ipra_subst diagonalNumerator
ipra_subst diagonalDenominator
ipra_subst diagonalEnvelope [Syn.subst_shift, Syn.shift_subst]
ipra_subst input

theorem envelope_at (F G : PR 2) (x y A N C t : PTm n)
    (h : Γ ⊢[PRAAx] diagonalEnvelope F G x y A N C) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F t x) (ap2 G t y) (diagonalNumerator A N C t) (diagonalDenominator N t) := by
  simpa only [diagonalEnvelope,GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_diagonalNumerator,
    subst_diagonalDenominator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE t

/-- Add a leading radius to two equal-clock observation allowances. -/
theorem diagonal_of_regular_distance (x y A N p : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded x y (unit p+unit p) (unit p*unit p)) :
    Γ ⊢[PRAAx] distanceBounded x y (diagonalNumerator A N two p) (diagonalDenominator N p) :=
  distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive p))
    (positive_product _ _ hN (unit_positive p))
    (le_of_eq_add (d := A*unit p*unit p*unit p) (by unfold diagonalNumerator diagonalDenominator; ipra_ring)) h

/-- Bound the diagonal error between a cutoff observation and a fixed
prefix by using the rate in whichever direction their cutoffs are ordered. -/
theorem ordered_prefix_diagonal (F : PR 2) (p A N L C x y : PTm n) {a : PTm n}
    (hN : Γ ⊢[PRAAx] le one N) (readback : Γ ⊢[PRAAx] a ≐ ap2 F (succ p) y)
    (early : le L C :: Γ ⊢[PRAAx] independentRate F F x y A N)
    (late : le C L :: Γ ⊢[PRAAx] distanceBounded a (ap2 F p x) (unit p+unit p) (unit p*unit p)) :
    Γ ⊢[PRAAx] distanceBounded a (ap2 F p x) (diagonalNumerator A N two p) (diagonalDenominator N p) := by
  refine (le_total L C).orE ?_ ?_
  · have h := diagonal_of_later_rate _ _ A N p (succ p) hN.wk (le_succ_self p)
      (rate_at F F x y A N p (succ p) early)
    exact distance_congr readback.wk.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (distance_symmetric _ _ _ _ (positive_product N (unit p) hN.wk (unit_positive p)) h)
  · exact diagonal_of_regular_distance _ _ A N p hN.wk late

/-- Three original metric legs at one proved positive common denominator. -/
theorem independent_slack (F G : PR 2) (x y A N C p q t : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] diagonalEnvelope F G x y A N C) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 F p x) (ap2 G q y))
      (rateNumerator A N p q) (rateDenominator N p q) (C+two) t := by
  let Z := rateDenominator N p q*unit t
  have z : Γ ⊢[PRAAx] le one Z := positive_product _ _ (denominator_positive N p q hN) (unit_positive t)
  have left := distance_radius_mono _ _ _ _ ((unit p+unit t)*(N*unit q)) Z
    (positive_product _ _ (unit_positive p) (unit_positive t)) z
    (le_of_eq_add (d := zero) (by dsimp [Z,rateDenominator]; ipra_ring)) (GaussianNameEquivalence.point_at F x p t hf)
  have middle := distance_radius_mono _ _ _ _ ((A*unit t+C*N)*(unit p*unit q)) Z
    (positive_product _ _ hN (unit_positive t)) z
    (le_of_eq_add (d := zero) (by dsimp [Z,rateDenominator,diagonalNumerator,diagonalDenominator]; ipra_ring))
    (envelope_at F G x y A N C t h)
  have right := distance_radius_mono _ _ _ _ ((unit t+unit q)*(N*unit p)) Z
    (positive_product _ _ (unit_positive t) (unit_positive q)) z
    (le_of_eq_add (d := zero) (by dsimp [Z,rateDenominator]; ipra_ring)) (GaussianNameEquivalence.point_at G y t q hg)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp [rateNumerator,rateDenominator,unit]; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ z (distance_triangle_same _ _ _ _ _ _ z left middle) right)

/-- The original independent observations satisfy the sharp rate. The
existing finite integer-gap precision removes all auxiliary dyadic slack. -/
theorem independent_at (F G : PR 2) (x y A N C p q : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] diagonalEnvelope F G x y A N C) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F p x) (ap2 G q y) (rateNumerator A N p q) (rateDenominator N p q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (C+two) (denominator_positive N p q hN)
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have fs := GaussianEuclideanDistanceName.shift_pointCN hf
  have gs := GaussianEuclideanDistanceName.shift_pointCN hg
  have hs : Γ.map Fm.shift ⊢[PRAAx] diagonalEnvelope F G (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift N) (Syn.shift C) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,subst_ap2,
    GaussianNamedInverseRate.subst_rateNumerator,GaussianNamedInverseRate.subst_rateDenominator,PTm.subst_mul,PTm.subst_add,
    Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    independent_slack F G (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift N) (Syn.shift C) (Syn.shift p) (Syn.shift q) (var 0) ns fs gs hs

theorem independent_rate (F G : PR 2) (x y A N C : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] diagonalEnvelope F G x y A N C) : Γ ⊢[PRAAx] independentRate F G x y A N := by
  have ns : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using hN.shift.shift
  have fs := GaussianEuclideanDistanceName.shift_pointCN (GaussianEuclideanDistanceName.shift_pointCN hf)
  have gs := GaussianEuclideanDistanceName.shift_pointCN (GaussianEuclideanDistanceName.shift_pointCN hg)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] diagonalEnvelope F G (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift C)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift] using independent_at F G (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y))
    (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift C)) (var 1) (var 0) ns fs gs hs


def gapQuery (F G : PR 2) (p q x y A N C : PTm n) : PTm n :=
  GaussianRationalSlackRemoval.precision (qsub (ap2 F p x) (ap2 G q y)) (rateNumerator A N p q) (rateDenominator N p q) (C+two)
ipra_subst gapQuery
theorem computed_gap_query (F G : PR 2) (p q x y A N C : PTm n) (h : Γ ⊢[PRAAx] input F G x y A N C) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 F p x) (ap2 G q y))
      (rateNumerator A N p q) (rateDenominator N p q) (C+two) (gapQuery F G p q x y A N C) :=
  independent_slack F G x y A N C p q _ h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂

theorem single_query_suffices (F G : PR 2) (p q x y A N C : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack (qsub (ap2 F p x) (ap2 G q y))
      (rateNumerator A N p q) (rateDenominator N p q) (C+two) (gapQuery F G p q x y A N C)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F p x) (ap2 G q y) (rateNumerator A N p q) (rateDenominator N p q) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ _ (denominator_positive N p q hN) h

def output (F G : PR 2) (p q x y A N C : PTm n) : PTm n :=
  pairT (ap2 F p x) (pairT (ap2 G q y) (pairT (rateNumerator A N p q) (pairT (rateDenominator N p q) (gapQuery F G p q x y A N C))))
def outputF (F G : PR 2) : PR 7 := PTm.toPR (output F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (F G : PR 2) (p q x y A N C : PTm n) : PTm n := PTm.app (outputF F G) ![p,q,x,y,A,N,C]
ipra_subst output
theorem program_at (F G : PR 2) (p q x y A N C : PTm n) : Γ ⊢[PRAAx]
    run F G p q x y A N C ≐ output F G p q x y A N C := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![p,q,x,y,A,N,C]
theorem returned_first (F G : PR 2) (p q x y A N C : PTm n) : Γ ⊢[PRAAx]
    fstT (run F G p q x y A N C) ≐ ap2 F p x := (program_at F G p q x y A N C).fstE
theorem returned_tail (F G : PR 2) (p q x y A N C : PTm n) : Γ ⊢[PRAAx]
    sndT (run F G p q x y A N C) ≐
      pairT (ap2 G q y) (pairT (rateNumerator A N p q) (pairT (rateDenominator N p q) (gapQuery F G p q x y A N C))) :=
  (program_at F G p q x y A N C).sndE
theorem returned_second (F G : PR 2) (p q x y A N C : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F G p q x y A N C)) ≐ ap2 G q y := (returned_tail F G p q x y A N C).fstE
theorem returned_budget (F G : PR 2) (p q x y A N C : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run F G p q x y A N C)) ≐
      pairT (rateNumerator A N p q) (pairT (rateDenominator N p q) (gapQuery F G p q x y A N C)) :=
  (returned_tail F G p q x y A N C).sndE
theorem returned_numerator (F G : PR 2) (p q x y A N C : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run F G p q x y A N C))) ≐ rateNumerator A N p q :=
  (returned_budget F G p q x y A N C).fstE
theorem returned_denominator_query (F G : PR 2) (p q x y A N C : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run F G p q x y A N C))) ≐ pairT (rateDenominator N p q) (gapQuery F G p q x y A N C) :=
  (returned_budget F G p q x y A N C).sndE
theorem returned_denominator (F G : PR 2) (p q x y A N C : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run F G p q x y A N C)))) ≐ rateDenominator N p q :=
  (returned_denominator_query F G p q x y A N C).fstE
theorem returned_query (F G : PR 2) (p q x y A N C : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run F G p q x y A N C)))) ≐ gapQuery F G p q x y A N C :=
  (returned_denominator_query F G p q x y A N C).sndE

theorem original_diagonal_variation_to_independent_rate_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input F G (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ independentRate F G (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (independent_rate F G _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_independent_observation_rate_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input F G (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ distanceBounded (ap2 F (var 0) (var 2)) (ap2 G (var 1) (var 3))
      (rateNumerator (var 4) (var 5) (var 0) (var 1)) (rateDenominator (var 5) (var 0) (var 1))) :=
  closeUniv 7 (.impI (independent_at F G _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_computed_integer_gap_query_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input F G (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianRationalSlackRemoval.slack (qsub (ap2 F (var 0) (var 2)) (ap2 G (var 1) (var 3)))
        (rateNumerator (var 4) (var 5) (var 0) (var 1)) (rateDenominator (var 5) (var 0) (var 1)) (var 6+two)
        (gapQuery F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (computed_gap_query F G _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_one_finite_query_suffices_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 5) ⟶ GaussianRationalSlackRemoval.slack (qsub (ap2 F (var 0) (var 2)) (ap2 G (var 1) (var 3)))
        (rateNumerator (var 4) (var 5) (var 0) (var 1)) (rateDenominator (var 5) (var 0) (var 1)) (var 6+two)
        (gapQuery F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ⟶
      distanceBounded (ap2 F (var 0) (var 2)) (ap2 G (var 1) (var 3))
        (rateNumerator (var 4) (var 5) (var 0) (var 1)) (rateDenominator (var 5) (var 0) (var 1))) :=
  closeUniv 7 (.impI (.impI (single_query_suffices F G _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_diagonal_rate_query_program_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (program_at F G _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianNamedLipschitzRate
