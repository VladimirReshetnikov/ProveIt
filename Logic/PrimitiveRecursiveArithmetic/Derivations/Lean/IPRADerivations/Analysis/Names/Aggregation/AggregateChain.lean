import IPRADerivations.Analysis.Names.Aggregation.AggregateEquality
import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalNearest

/-!
# The actual least-neighbor chain of a regular rational aggregate

Finite-demand packet, Section 3, `thm:aggregate-chain` and `eq:chain-tail`.
The list evaluator is one fixed PR program. Dimension, starting precision,
starting index, all later indices and persistent data are internal values.
The chain really recurses through the actual rational nearest-neighbor
program; its coherence is a conclusion.

The object endpoints concern finite rational observations, rather than an
ambient completed-real object or a global choice function.

Totalization is inherited from the actual nearest/sequence-entry programs;
an invalid empty aggregate is not promised to return the zero vector.
Distances interpret the first `d` coordinates through the total rational
decoder. Stored point lengths are not needed for these stronger arithmetic
estimates: out-of-range coordinate lookup follows `MasterCertificate.entry`
(the head of the reverse stack), rather than adding zero coordinates.
For source lists of well-formed `d`-vectors, the separate `shaped` contract
below proves that every returned point/name code has stored length `d`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.AggregateChain

open_ipra
open LeanProofs.IPRA.Analysis.AggregateEquality
  (unit subst_unit unit_positive sample subst_sample nonempty subst_nonempty nonempty_at
    regular subst_regular regular_at pointRadius_diagonal)
open LeanProofs.IPRA.Analysis.RationalHausdorff
open LeanProofs.IPRA.Analysis.RationalHausdorffTriangle (coordinateRadius_triangle)
open LeanProofs.IPRA.Analysis.RationalNearest (selected subst_selected selected_spec cover_selected_radius)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_neg)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private alias positive_cancel := Common.mul_cancel_le

theorem coordinate_congr {x x' y y' k k' A A' B B' : PTm n}
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') (hk : Γ ⊢[PRAAx] k ≐ k')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] coordinateRadius x y k A B) : Γ ⊢[PRAAx] coordinateRadius x' y' k' A' B' := by
  have hin : Γ ⊢[PRAAx] (coordinateRadius (var 0) (var 1) (var 2) (var 3) (var 4)).subst ![x,y,k,A,B] := by simpa using h
  have out := Prf.eqSubst (coordinateRadius (var 0) (var 1) (var 2) (var 3) (var 4))
    ![x,y,k,A,B] ![x',y',k',A',B'] (fun i => by fin_cases i <;> assumption) hin
  simpa using out

theorem point_congr {x x' y y' d d' A A' B B' : PTm n}
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') (hd : Γ ⊢[PRAAx] d ≐ d')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] pointRadius x y d A B) : Γ ⊢[PRAAx] pointRadius x' y' d' A' B' := by
  have hin : Γ ⊢[PRAAx] (pointRadius (var 0) (var 1) (var 2) (var 3) (var 4)).subst ![x,y,d,A,B] := by simpa using h
  have out := Prf.eqSubst (pointRadius (var 0) (var 1) (var 2) (var 3) (var 4))
    ![x,y,d,A,B] ![x',y',d',A',B'] (fun i => by fin_cases i <;> assumption) hin
  simpa using out

/-- Compare rational budgets without assuming normalized fractions. -/
theorem fraction_mono {v scale A B C D : PTm n} (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le (B*v) (A*scale)) (hAD : Γ ⊢[PRAAx] le (A*D) (C*B)) :
    Γ ⊢[PRAAx] le (D*v) (C*scale) := by
  have first := le_mul_mono (le_refl D) h
  have second := le_mul_mono hAD (le_refl scale)
  have first' : Γ ⊢[PRAAx] le (B*(D*v)) ((A*D)*scale) := le_congr (by ipra_ring) (by ipra_ring) first
  have second' : Γ ⊢[PRAAx] le ((A*D)*scale) (B*(C*scale)) := le_congr (.eqRefl _) (by ipra_ring) second
  exact positive_cancel hB (le_trans first' second')

theorem coordinate_mono {x y k A B C D : PTm n} (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] coordinateRadius x y k A B) (hAD : Γ ⊢[PRAAx] le (A*D) (C*B)) :
    Γ ⊢[PRAAx] coordinateRadius x y k C D := fraction_mono hB h hAD

theorem coordinate_cancel {x y k A B c : PTm n} (hc : Γ ⊢[PRAAx] le one c)
    (h : Γ ⊢[PRAAx] coordinateRadius x y k (c*A) (c*B)) :
    Γ ⊢[PRAAx] coordinateRadius x y k A B :=
  positive_cancel hc (le_congr (by ipra_ring) (by ipra_ring) h)

theorem point_cancel (x y d A B c : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (h : Γ ⊢[PRAAx] pointRadius x y d (c*A) (c*B)) : Γ ⊢[PRAAx] pointRadius x y d A B := by
  refine .allI (.impI ?_)
  have cp : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift c) := by
    simpa only [Fm.shift, subst_le, Syn.shift, one, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hc.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] pointRadius (Syn.shift x) (Syn.shift y) (Syn.shift d)
      (Syn.shift c*Syn.shift A) (Syn.shift c*Syn.shift B) := by
    simpa only [Fm.shift, subst_pointRadius, PTm.subst_mul, Syn.shift] using h.shift
  exact coordinate_cancel cp.wk (pointRadius_at _ _ _ _ _ _ h'.wk Prf.hyp0)

theorem point_mono (x y d A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] pointRadius x y d A B) (hAD : Γ ⊢[PRAAx] le (A*D) (C*B)) :
    Γ ⊢[PRAAx] pointRadius x y d C D := by
  refine .allI (.impI ?_)
  have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift, subst_le, Syn.shift, one, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using hB.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] pointRadius (Syn.shift x) (Syn.shift y) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_pointRadius, Syn.shift] using h.shift
  have ad : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A*Syn.shift D) (Syn.shift C*Syn.shift B) := by
    simpa only [Fm.shift, subst_le, PTm.subst_mul, Syn.shift] using hAD.shift
  exact coordinate_mono b.wk (pointRadius_at _ _ _ _ _ _ h'.wk Prf.hyp0) ad.wk

theorem coordinate_symmetric (x y k A B : PTm n) (h : Γ ⊢[PRAAx] coordinateRadius x y k A B) :
    Γ ⊢[PRAAx] coordinateRadius y x k A B := by
  have crossed : Γ ⊢[PRAAx] zabs (crossNumerator y x k) ≐ zabs (crossNumerator x y k) :=
    (zabs_congr (u := crossNumerator y x k) (v := -(crossNumerator x y k))
      (by simp only [crossNumerator, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg]; ring)).eqTrans (zabs_neg _)
  exact le_congr (congrMul (.eqRefl _) crossed).eqSymm
    (congrMul (.eqRefl _) (mul_comm _ _)) h

theorem point_symmetric (x y d A B : PTm n) (h : Γ ⊢[PRAAx] pointRadius x y d A B) :
    Γ ⊢[PRAAx] pointRadius y x d A B := by
  refine .allI (.impI ?_)
  have h' : Γ.map Fm.shift ⊢[PRAAx] pointRadius (Syn.shift x) (Syn.shift y) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, subst_pointRadius, Syn.shift] using h.shift
  exact coordinate_symmetric _ _ _ _ _ (pointRadius_at _ _ _ _ _ _ h'.wk Prf.hyp0)

theorem unit_zero : Γ ⊢[PRAAx] unit (zero : PTm n) ≐ one := pw_zero _
theorem unit_succ (r : PTm n) : Γ ⊢[PRAAx] unit (succ r) ≐ two*unit r :=
  (pw_succ _ _).eqTrans (mul_comm _ _)
theorem unit_add (r t : PTm n) : Γ ⊢[PRAAx] unit (r+t) ≐ unit r*unit t := pw_add _ _ _

/-- Persistent data: start precision, initial entry index, dimension, input data. -/
def data (s i d x : PTm n) : PTm n := pairT s (pairT i (pairT d x))
def indexBase : PTm 1 := fstT (sndT (var 0))
def indexStep (S : PR 2) : PTm 3 :=
  selected
    (sample S (fstT (var 2)+var 0) (sndT (sndT (sndT (var 2)))))
    (sample S (fstT (var 2)+succ (var 0)) (sndT (sndT (sndT (var 2)))))
    (fstT (sndT (sndT (var 2)))) (var 1)
def indexF (S : PR 2) : PR 2 := rec2 indexBase (indexStep S)
def index (S : PR 2) (r s i d x : PTm n) : PTm n := ap2 (indexF S) r (data s i d x)
def point (S : PR 2) (r s i d x : PTm n) : PTm n := entry (sample S (s+r) x) (index S r s i d x)
def name (S : PR 2) (t s i d x : PTm n) : PTm n := point S (succ (succ t)) s i d x

ipra_subst data
ipra_subst index
ipra_subst point
ipra_subst name

theorem selected_congr {S S' T T' d d' i i' : PTm n}
    (hS : Γ ⊢[PRAAx] S ≐ S') (hT : Γ ⊢[PRAAx] T ≐ T')
    (hd : Γ ⊢[PRAAx] d ≐ d') (hi : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] selected S T d i ≐ selected S' T' d' i' := by
  have h := Prf.eqCongr (Γ := Γ) (selected (var 0) (var 1) (var 2) (var 3))
    (σ := ![S,T,d,i]) (σ' := ![S',T',d',i']) (fun j => by fin_cases j <;> assumption)
  simpa using h

theorem index_zero (S : PR 2) (s i d x : PTm n) : Γ ⊢[PRAAx] index S zero s i d x ≐ i := by
  have h := rec2_zero (Γ := Γ) indexBase (indexStep S) (data s i d x)
  simp only [indexBase, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero] at h
  exact h.eqTrans (snd_pair _ _).fstE

theorem index_succ (S : PR 2) (r s i d x : PTm n) :
    Γ ⊢[PRAAx] index S (succ r) s i d x ≐
      selected (sample S (s+r) x) (sample S (s+succ r) x) d (index S r s i d x) := by
  have h := rec2_succ (Γ := Γ) indexBase (indexStep S) r (data s i d x)
  simp only [indexStep, subst_selected, subst_sample, PTm.subst_add,
    ConciseIPRA.PTm.subst_succ, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  have ss : Γ ⊢[PRAAx] fstT (data s i d x) ≐ s := fst_pair _ _
  have dd : Γ ⊢[PRAAx] fstT (sndT (sndT (data s i d x))) ≐ d :=
    (congrFst (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _).fstE
  have xx : Γ ⊢[PRAAx] sndT (sndT (sndT (data s i d x))) ≐ x :=
    (congrSnd (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _).sndE
  exact h.eqTrans (selected_congr (congrAp2 S (congrAdd ss (.eqRefl _)) xx)
    (congrAp2 S (congrAdd ss (.eqRefl _)) xx) dd (.eqRefl _))

theorem point_zero (S : PR 2) (s i d x : PTm n) :
    Γ ⊢[PRAAx] point S zero s i d x ≐ entry (sample S s x) i :=
  entry_congr (congrAp2 S (add_zero s) (.eqRefl _)) (index_zero S s i d x)

theorem point_succ (S : PR 2) (r s i d x : PTm n) :
    Γ ⊢[PRAAx] point S (succ r) s i d x ≐
      entry (sample S (s+succ r) x)
        (selected (sample S (s+r) x) (sample S (s+succ r) x) d (index S r s i d x)) :=
  entry_congr (.eqRefl _) (index_succ S r s i d x)

/-- QF induction tracks only an actual index in its current finite list. -/
theorem index_in_range (S : PR 2) (r s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] lt (index S r s i d x) (length (sample S (s+r) x)) := by
  have all : Γ ⊢[PRAAx] .all (lt
      (index S (var 0) (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x))
      (length (sample S (Syn.shift s+var 0) (Syn.shift x)))) := by
    ipra_qfind (lt_QF _ _) [subst_lt, subst_index, Foundations.SequenceComposition.subst_length, subst_sample]
    · exact lt_congr (index_zero S _ _ _ _).eqSymm (congrFst (congrAp2 S (add_zero _) (.eqRefl _))).eqSymm hi
    · have ne : Γ.map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift x) := by
        simpa only [Fm.shift, subst_nonempty, Syn.shift] using hS.shift
      exact lt_congr (index_succ S _ _ _ _ _).eqSymm (.eqRefl _)
        (selected_spec _ _ _ _ (nonempty_at S _ _ ne).wk)
  simpa only [subst_lt, subst_index, Foundations.SequenceComposition.subst_length, subst_sample,
    PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE r all

theorem point_index_congr (S : PR 2) {r r' : PTm n} (s i d x : PTm n) (h : Γ ⊢[PRAAx] r ≐ r') :
    Γ ⊢[PRAAx] point S r s i d x ≐ point S r' s i d x :=
  entry_congr (congrAp2 S (congrAdd (.eqRefl _) h) (.eqRefl _))
    (congrAp2 (indexF S) h (.eqRefl _))

theorem adjacent_raw (S : PR 2) (r s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] pointRadius (point S r s i d x) (point S (succ r) s i d x) d
      (unit (s+r)+unit (s+succ r)) (unit (s+r)*unit (s+succ r)) := by
  have chosen := cover_selected_radius (sample S (s+r) x) (sample S (s+succ r) x) d
    (index S r s i d x) _ _ (index_in_range S r s i d x hS hi)
    (nonempty_at S (s+succ r) x hS) (regular_at S (s+r) (s+succ r) d x hR)
  exact point_congr (.eqRefl _) (point_succ S r s i d x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) chosen

theorem unit_next (s r : PTm n) : Γ ⊢[PRAAx] unit (s+succ r) ≐ two*unit (s+r) :=
  (congrAp2 powF (add_succ s r) (.eqRefl _)).eqTrans (unit_succ _)

theorem adjacent (S : PR 2) (r s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] pointRadius (point S r s i d x) (point S (succ r) s i d x) d
      (num 3) (unit (s+succ r)) := by
  have numerator : Γ ⊢[PRAAx] unit (s+r)+unit (s+succ r) ≐ unit (s+r)*num 3 := by
    ipra_lc natEq (unit_next (Γ := Γ) s r)
  exact point_cancel _ _ _ _ _ _ (unit_positive (s+r))
    (point_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) numerator (.eqRefl _) (adjacent_raw S r s i d x hS hR hi))

def tailNumerator (r : PTm n) : PTm n := num 3*monus (unit r) one
def tailDenominator (s j r : PTm n) : PTm n := unit (s+j)*unit r

ipra_subst tailNumerator
ipra_subst tailDenominator

theorem tailNumerator_zero : Γ ⊢[PRAAx] tailNumerator (zero : PTm n) ≐ zero :=
  (congrMul (.eqRefl _) ((congrMonus unit_zero (.eqRefl _)).eqTrans (monus_self _))).eqTrans (mul_zero _)

theorem tailNumerator_succ (r : PTm n) :
    Γ ⊢[PRAAx] tailNumerator (succ r) ≐ two*tailNumerator r+num 3 := by
  unfold tailNumerator
  ipra_lc -3*natEq (eq_add_of_le (unit_positive (Γ := Γ) (succ r))) +
    6*natEq (eq_add_of_le (unit_positive (Γ := Γ) r)) + 3*natEq (unit_succ (Γ := Γ) r)

theorem tailDenominator_succ (s j r : PTm n) :
    Γ ⊢[PRAAx] tailDenominator s j (succ r) ≐ two*tailDenominator s j r :=
  (congrMul (.eqRefl _) (unit_succ r)).eqTrans (by unfold tailDenominator; ipra_ring)

theorem tailDenominator_positive (s j r : PTm n) : Γ ⊢[PRAAx] le one (tailDenominator s j r) :=
  le_congr (one_mul one) (.eqRefl _) (le_mul_mono (unit_positive (s+j)) (unit_positive r))

theorem next_denominator (s j r : PTm n) :
    Γ ⊢[PRAAx] unit (s+succ (j+r)) ≐ two*tailDenominator s j r :=
  (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] s+succ (j+r) ≐ succ ((s+j)+r)) (.eqRefl _)).eqTrans
    ((unit_succ _).eqTrans (congrMul (.eqRefl _) (unit_add _ _)))

theorem coordinate_half_step (x y z k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hxy : Γ ⊢[PRAAx] coordinateRadius x y k A B)
    (hyz : Γ ⊢[PRAAx] coordinateRadius y z k (num 3) (two*B)) :
    Γ ⊢[PRAAx] coordinateRadius x z k (two*A+num 3) (two*B) :=
  coordinate_cancel hB (coordinate_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (by ipra_ring) (.eqRefl _) (coordinateRadius_triangle x y z k A B (num 3) (two*B) hxy hyz))

/-- The sharp telescope is proved by QF induction for one arbitrary
coordinate; the global name contracts remain in the fixed context. -/
theorem coordinate_tail (S : PR 2) (r j s i d x k : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) (hk : Γ ⊢[PRAAx] lt k d) :
    Γ ⊢[PRAAx] coordinateRadius (point S j s i d x) (point S (j+r) s i d x) k
      (tailNumerator r) (tailDenominator s j r) := by
  have all : Γ ⊢[PRAAx] .all (coordinateRadius
      (point S (Syn.shift j) (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x))
      (point S (Syn.shift j+var 0) (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x))
      (Syn.shift k) (tailNumerator (var 0)) (tailDenominator (Syn.shift s) (Syn.shift j) (var 0))) := by
    ipra_qfind (le_QF _ _) [subst_coordinateRadius, subst_point, subst_tailNumerator, subst_tailDenominator]
    · have diagonal := pointRadius_at _ _ _ _ _ _
        (pointRadius_diagonal (Γ := Γ) (point S j s i d x) d zero (tailDenominator s j zero)) hk
      exact coordinate_congr (.eqRefl _) (point_index_congr S s i d x (add_zero j).eqSymm)
        (.eqRefl _) tailNumerator_zero.eqSymm (.eqRefl _) diagonal
    · let IH : Fm PTm (n+1) := coordinateRadius
        (point S (Syn.shift j) (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x))
        (point S (Syn.shift j+var 0) (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x))
        (Syn.shift k) (tailNumerator (var 0)) (tailDenominator (Syn.shift s) (Syn.shift j) (var 0))
      let Δ := IH :: Γ.map Fm.shift
      have ne : Γ.map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift x) := by
        simpa only [Fm.shift, subst_nonempty, Syn.shift] using hS.shift
      have reg : Γ.map Fm.shift ⊢[PRAAx] regular S (Syn.shift d) (Syn.shift x) := by
        simpa only [Fm.shift, subst_regular, Syn.shift] using hR.shift
      have seed : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (sample S (Syn.shift s) (Syn.shift x))) := by
        simpa only [Fm.shift, subst_lt, Foundations.SequenceComposition.subst_length, subst_sample, Syn.shift] using hi.shift
      have coord : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift k) (Syn.shift d) := by
        simpa only [Fm.shift, subst_lt, Syn.shift] using hk.shift
      have edge := adjacent (Γ := Δ) S (Syn.shift j+var 0) (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x)
        ne.wk reg.wk seed.wk
      have edgeCoordinate := pointRadius_at _ _ _ _ _ _ edge coord.wk
      have adjusted := coordinate_congr (.eqRefl _)
        (point_index_congr S (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x)
          (add_succ (Syn.shift j) (var 0)).eqSymm) (.eqRefl _) (.eqRefl _)
        (next_denominator (Syn.shift s) (Syn.shift j) (var 0)) edgeCoordinate
      have joined := coordinate_half_step (Γ := Δ) _ _ _ _ _ _
        (tailDenominator_positive (Syn.shift s) (Syn.shift j) (var 0)) Prf.hyp0 adjusted
      exact coordinate_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (tailNumerator_succ (var 0)).eqSymm
        (tailDenominator_succ (Syn.shift s) (Syn.shift j) (var 0)).eqSymm joined
  simpa only [subst_coordinateRadius, subst_point, subst_tailNumerator, subst_tailDenominator,
    PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE r all

/-- Exact source `eq:chain-tail`, at arbitrary internal start/window lengths:
`3*(2^r-1)/(2^(s+j)*2^r)`. -/
theorem sharp_tail (S : PR 2) (r j s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] pointRadius (point S j s i d x) (point S (j+r) s i d x) d
      (tailNumerator r) (tailDenominator s j r) := by
  refine .allI (.impI ?_)
  have ne : Γ.map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift x) := by
    simpa only [Fm.shift, subst_nonempty, Syn.shift] using hS.shift
  have reg : Γ.map Fm.shift ⊢[PRAAx] regular S (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift, subst_regular, Syn.shift] using hR.shift
  have seed : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (sample S (Syn.shift s) (Syn.shift x))) := by
    simpa only [Fm.shift, subst_lt, Foundations.SequenceComposition.subst_length, subst_sample, Syn.shift] using hi.shift
  have result := coordinate_tail S (Syn.shift r) (Syn.shift j) (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x)
    (var 0) ne.wk reg.wk seed.wk Prf.hyp0
  simpa only [Syn.shift, subst_point, subst_tailNumerator, subst_tailDenominator, PTm.subst_add] using result

theorem tail_budget (s j r : PTm n) :
    Γ ⊢[PRAAx] le (tailNumerator r*unit (s+j)) (num 3*tailDenominator s j r) := by
  have small : Γ ⊢[PRAAx] le (monus (unit r) one) (unit r) :=
    le_of_eq_add (d := one) ((eq_add_of_le (unit_positive r)).eqTrans (add_comm _ _))
  exact le_congr (.eqRefl _) (by unfold tailDenominator; ipra_ring)
    (le_mul_mono (le_mul_mono (le_refl (num 3)) small) (le_refl (unit (s+j))))

theorem coarse_tail (S : PR 2) (r j s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] pointRadius (point S j s i d x) (point S (j+r) s i d x) d (num 3) (unit (s+j)) :=
  point_mono _ _ _ _ _ _ _ (tailDenominator_positive s j r) (sharp_tail S r j s i d x hS hR hi) (tail_budget s j r)

theorem unit_two_later (s t : PTm n) :
    Γ ⊢[PRAAx] unit (s+succ (succ t)) ≐ num 4*unit s*unit t :=
  (unit_add _ _).eqTrans ((congrMul (.eqRefl _)
    ((unit_succ _).eqTrans (congrMul (.eqRefl _) (unit_succ _)))).eqTrans (by ipra_ring))

theorem name_precision_budget (s t : PTm n) :
    Γ ⊢[PRAAx] le (num 3*unit t) (unit (s+succ (succ t))) := by
  have first : Γ ⊢[PRAAx] le (num 3*unit t) (num 4*unit t) :=
    le_mul_mono (le_succ_self (num 3)) (le_refl _)
  have second : Γ ⊢[PRAAx] le (num 4*unit t) (num 4*unit s*unit t) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (le_mul_mono (le_refl (num 4*unit t)) (unit_positive s))
  exact le_trans first (le_congr (.eqRefl _) (unit_two_later s t).eqSymm second)

/-- The prescribed two-bit shift gives the stronger ordered-name bound. -/
theorem name_ordered (S : PR 2) (t u s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) (htu : Γ ⊢[PRAAx] le t u) :
    Γ ⊢[PRAAx] pointRadius (name S t s i d x) (name S u s i d x) d one (unit t) := by
  have endpoint : Γ ⊢[PRAAx] succ (succ t)+monus u t ≐ succ (succ u) := by
    ipra_lc -natEq (eq_add_of_le htu)
  have tail := point_congr (.eqRefl _) (point_index_congr S s i d x endpoint) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (coarse_tail S (monus u t) (succ (succ t)) s i d x hS hR hi)
  exact point_mono _ _ _ _ _ _ _ (unit_positive _) tail
    (le_congr (.eqRefl _) (one_mul _).eqSymm (name_precision_budget s t))

/-- Every output sample lies within the source's `3*2^-s` of the initial entry. -/
theorem name_near_initial (S : PR 2) (t s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] pointRadius (name S t s i d x) (entry (sample S s x) i) d (num 3) (unit s) := by
  have initialToName := point_congr (point_zero S s i d x)
    (point_index_congr S s i d x (zero_add _)) (.eqRefl _) (.eqRefl _)
    (congrAp2 powF (add_zero s) (.eqRefl _)) (coarse_tail S (succ (succ t)) zero s i d x hS hR hi)
  exact point_symmetric _ _ _ _ _ initialToName

theorem name_regular (S : PR 2) (t u s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] pointRadius (name S t s i d x) (name S u s i d x) d
      (unit t+unit u) (unit t*unit u) := by
  refine .orE (le_total t u) ?_ ?_
  · let Δ := le t u :: Γ
    have ordered := name_ordered (Γ := Δ) S t u s i d x hS.wk hR.wk hi.wk Prf.hyp0
    exact point_mono _ _ _ _ _ _ _ (unit_positive t) ordered
      (le_of_eq_add (d := unit t*unit t) (by ipra_ring))
  · let Δ := le u t :: Γ
    have ordered := name_ordered (Γ := Δ) S u t s i d x hS.wk hR.wk hi.wk Prf.hyp0
    exact point_mono _ _ _ _ _ _ _ (unit_positive u) (point_symmetric _ _ _ _ _ ordered)
      (le_of_eq_add (d := unit u*unit u) (by ipra_ring))

theorem unit_three_later (s k : PTm n) :
    Γ ⊢[PRAAx] unit (s+succ (succ (succ k))) ≐ num 8*unit s*unit k :=
  (unit_add _ _).eqTrans ((congrMul (.eqRefl _)
    ((unit_succ _).eqTrans (congrMul (.eqRefl _)
      ((unit_succ _).eqTrans (congrMul (.eqRefl _) (unit_succ _)))))).eqTrans (by ipra_ring))

/-- Exact arithmetic behind `(e_(s+k+3)+e_(k+1)) ≤ (5/8)e_k`. -/
theorem distance_precision_budget (s k : PTm n) :
    Γ ⊢[PRAAx] le
      ((unit (s+succ (succ (succ k)))+unit (succ k))*(num 8*unit k))
      (num 5*(unit (s+succ (succ (succ k)))*unit (succ k))) := by
  apply le_of_eq_add (d := num 16*unit k*unit k*monus (unit s) one)
  have first := natEq (unit_three_later (Γ := Γ) s k)
  have second := natEq (unit_succ (Γ := Γ) k)
  have start := natEq (eq_add_of_le (unit_positive (Γ := Γ) s))
  apply deriveNat
  ipra_simps
  rw [first, second]
  linear_combination 16*(Groth.ι (Q.mk Γ (unit k)))^2*start

def distanceSource (S : PR 2) (k s x : PTm n) : PTm n := sample S (s+succ (succ (succ k))) x
def distanceTarget (S : PR 2) (k x : PTm n) : PTm n := sample S (succ k) x
def distanceIndex (S : PR 2) (k s i d x : PTm n) : PTm n := index S (succ (succ (succ k))) s i d x
def distanceNeighbor (S : PR 2) (k s i d x : PTm n) : PTm n :=
  selected (distanceSource S k s x) (distanceTarget S k x) d (distanceIndex S k s i d x)

/-- Numerator of the actual nearest-distance sample, with its own pair pool. -/
def distanceNumerator (S : PR 2) (k s i d x : PTm n) : PTm n :=
  Foundations.FiniteHausdorff.distanceTo RationalSupMetric.metricF
    (entry (grid .left (distanceSource S k s x) (distanceTarget S k x) d) (distanceIndex S k s i d x))
    (grid .right (distanceSource S k s x) (distanceTarget S k x) d)
    (parameter (distanceSource S k s x) (distanceTarget S k x) d)

def distanceDenominator (S : PR 2) (k s d x : PTm n) : PTm n :=
  denominator (distanceSource S k s x) (distanceTarget S k x) d

/-- Raw numerator/positive-denominator pair for the distance name. -/
def distanceSample (S : PR 2) (k s i d x : PTm n) : PTm n :=
  pairT (distanceNumerator S k s i d x) (distanceDenominator S k s d x)

ipra_subst distanceSource
ipra_subst distanceTarget
ipra_subst distanceIndex
ipra_subst distanceNeighbor
ipra_subst distanceNumerator
ipra_subst distanceDenominator
ipra_subst distanceSample

theorem distance_neighbor_range (S : PR 2) (k s i d x : PTm n) (hS : Γ ⊢[PRAAx] nonempty S x) :
    Γ ⊢[PRAAx] lt (distanceNeighbor S k s i d x) (length (distanceTarget S k x)) :=
  selected_spec _ _ _ _ (nonempty_at S _ _ hS)

/-- One actual original target index witnesses the source membership estimate. -/
theorem distance_neighbor_radius (S : PR 2) (k s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] pointRadius (name S (succ k) s i d x)
      (entry (distanceTarget S k x) (distanceNeighbor S k s i d x)) d (num 5) (num 8*unit k) := by
  have hB : Γ ⊢[PRAAx] le one (unit (s+succ (succ (succ k)))*unit (succ k)) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (unit_positive _) (unit_positive _))
  have chosen := cover_selected_radius (distanceSource S k s x) (distanceTarget S k x) d
    (distanceIndex S k s i d x) _ _ (index_in_range S _ _ _ _ _ hS hi)
    (nonempty_at S _ _ hS) (regular_at S _ _ d x hR)
  exact point_mono _ _ _ _ _ _ _ hB chosen (distance_precision_budget s k)

theorem distance_sample_zero (S : PR 2) (k s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] le ((num 8*unit k)*distanceNumerator S k s i d x)
      (num 5*distanceDenominator S k s d x) := by
  have hB : Γ ⊢[PRAAx] le one (unit (s+succ (succ (succ k)))*unit (succ k)) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (unit_positive _) (unit_positive _))
  have range := index_in_range S (succ (succ (succ k))) s i d x hS hi
  have close := regular_at S (s+succ (succ (succ k))) (succ k) d x hR
  have hit := originalCover_at .left .right (distanceSource S k s x) (distanceTarget S k x) d _ _
    (distanceIndex S k s i d x) (Prf.andE₁ close) range
  have bound := minimum_bound_of_original_hit .left .right (distanceSource S k s x) (distanceTarget S k x) d
    (distanceIndex S k s i d x) _ _ range hit
  exact fraction_mono hB bound (distance_precision_budget s k)

theorem distance_sample_positive (S : PR 2) (k s i d x : PTm n) :
    Γ ⊢[PRAAx] le one (sndT (distanceSample S k s i d x)) :=
  le_congr (.eqRefl _) (snd_pair _ _).eqSymm (RationalSupMetric.commonDenominator_one_le _ _)

theorem distance_code_zero (S : PR 2) (k s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] le ((num 8*unit k)*fstT (distanceSample S k s i d x))
      (num 5*sndT (distanceSample S k s i d x)) :=
  le_congr (congrMul (.eqRefl _) (fst_pair _ _).eqSymm)
    (congrMul (.eqRefl _) (snd_pair _ _).eqSymm) (distance_sample_zero S k s i d x hS hR hi)

theorem distance_sample_unit_bound (S : PR 2) (k s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] le (unit k*distanceNumerator S k s i d x) (distanceDenominator S k s d x) := by
  have eight : Γ ⊢[PRAAx] le one (num 8) := le_of_eq_add (d := num 7) (by ipra_ring)
  have five : Γ ⊢[PRAAx] le (num 5) (num 8) := le_of_eq_add (d := num 3) (by ipra_ring)
  have scaled : Γ ⊢[PRAAx] le (num 8*(unit k*distanceNumerator S k s i d x))
      (num 8*distanceDenominator S k s d x) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (distance_sample_zero S k s i d x hS hR hi))
      (le_mul_mono five (le_refl _))
  exact positive_cancel eight scaled

private theorem abs_nat (a : PTm n) : Γ ⊢[PRAAx] zabs (ZT.ofNat a) ≐ a :=
  (congrAdd (monus_zero a) (zero_monus a)).eqTrans (add_zero a)

private theorem abs_pair_bound (a b : PTm n) : Γ ⊢[PRAAx] le (zabs (⟨a,b⟩ : ZT n)) (a+b) := by
  have bound := Foundations.GapDecision.zabs_tri (Γ := Γ) (u := ZT.ofNat a) (v := -(ZT.ofNat b))
    (w := (⟨a,b⟩ : ZT n)) (by
      rw [ZT.toZ_neg, ZT.toZ_ofNat, ZT.toZ_ofNat]
      change Groth.ι (Q.mk Γ a) - Groth.ι (Q.mk Γ b) = _
      ring)
  exact le_congr (.eqRefl _) (congrAdd (abs_nat a) ((zabs_neg _).eqTrans (abs_nat b))) bound

def distanceRegular (S : PR 2) (k l s i d x : PTm n) : Fm PTm n :=
  le (unit k*unit l*zabs (⟨distanceNumerator S k s i d x*distanceDenominator S l s d x,
      distanceNumerator S l s i d x*distanceDenominator S k s d x⟩ : ZT n))
    ((unit k+unit l)*distanceDenominator S k s d x*distanceDenominator S l s d x)

/-- The actual nonnegative distance samples form a regular rational name of zero. -/
theorem distance_regular (S : PR 2) (k l s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] distanceRegular S k l s i d x := by
  have first := distance_sample_unit_bound S k s i d x hS hR hi
  have second := distance_sample_unit_bound S l s i d x hS hR hi
  have triangle := le_mul_mono (le_refl (unit k*unit l))
    (abs_pair_bound (Γ := Γ) (distanceNumerator S k s i d x*distanceDenominator S l s d x)
      (distanceNumerator S l s i d x*distanceDenominator S k s d x))
  have sum := add_le_add₂
    (le_mul_mono (le_refl (unit l*distanceDenominator S l s d x)) first)
    (le_mul_mono (le_refl (unit k*distanceDenominator S k s d x)) second)
  have bounds : Γ ⊢[PRAAx] le
      ((unit k*unit l)*(distanceNumerator S k s i d x*distanceDenominator S l s d x+
        distanceNumerator S l s i d x*distanceDenominator S k s d x))
      ((unit k+unit l)*distanceDenominator S k s d x*distanceDenominator S l s d x) :=
    le_congr (by ipra_ring) (by ipra_ring) sum
  exact le_trans triangle bounds

/-! ## Actual fixed PR output programs and closed source endpoints -/

def indexProgramF (S : PR 2) : PR 5 := PTm.toPR (index S (var 0) (var 1) (var 2) (var 3) (var 4))
def nameF (S : PR 2) : PR 5 := PTm.toPR (name S (var 0) (var 1) (var 2) (var 3) (var 4))
def distanceF (S : PR 2) : PR 5 := PTm.toPR (distanceSample S (var 0) (var 1) (var 2) (var 3) (var 4))
def neighborF (S : PR 2) : PR 5 := PTm.toPR (distanceNeighbor S (var 0) (var 1) (var 2) (var 3) (var 4))

theorem index_program_at (S : PR 2) (r s i d x : PTm n) :
    Γ ⊢[PRAAx] apply5 (indexProgramF S) r s i d x ≐ index S r s i d x := by
  have h := toPR_eq (Γ := Γ) (index S (var 0) (var 1) (var 2) (var 3) (var 4)) ![r,s,i,d,x]
  simpa [indexProgramF, apply5] using h
theorem name_program_at (S : PR 2) (t s i d x : PTm n) :
    Γ ⊢[PRAAx] apply5 (nameF S) t s i d x ≐ name S t s i d x := by
  have h := toPR_eq (Γ := Γ) (name S (var 0) (var 1) (var 2) (var 3) (var 4)) ![t,s,i,d,x]
  simpa [nameF, apply5] using h
theorem distance_program_at (S : PR 2) (k s i d x : PTm n) :
    Γ ⊢[PRAAx] apply5 (distanceF S) k s i d x ≐ distanceSample S k s i d x := by
  have h := toPR_eq (Γ := Γ) (distanceSample S (var 0) (var 1) (var 2) (var 3) (var 4)) ![k,s,i,d,x]
  simpa [distanceF, apply5] using h
theorem neighbor_program_at (S : PR 2) (k s i d x : PTm n) :
    Γ ⊢[PRAAx] apply5 (neighborF S) k s i d x ≐ distanceNeighbor S k s i d x := by
  have h := toPR_eq (Γ := Γ) (distanceNeighbor S (var 0) (var 1) (var 2) (var 3) (var 4)) ![k,s,i,d,x]
  simpa [neighborF, apply5] using h

def supportAt (S : PR 2) (k s i d x : PTm n) : Fm PTm n :=
  lt (distanceNeighbor S k s i d x) (length (distanceTarget S k x)) ⋏
    (pointRadius (name S (succ k) s i d x)
      (entry (distanceTarget S k x) (distanceNeighbor S k s i d x)) d (num 5) (num 8*unit k) ⋏
    (le one (sndT (distanceSample S k s i d x)) ⋏
      le ((num 8*unit k)*fstT (distanceSample S k s i d x)) (num 5*sndT (distanceSample S k s i d x))))

theorem support_at (S : PR 2) (k s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) : Γ ⊢[PRAAx] supportAt S k s i d x :=
  .andI (distance_neighbor_range S k s i d x hS)
    (.andI (distance_neighbor_radius S k s i d x hS hR hi)
      (.andI (distance_sample_positive S k s i d x) (distance_code_zero S k s i d x hS hR hi)))

def nameRegular (S : PR 2) (s i d x : PTm n) : Fm PTm n :=
  .all (.all (pointRadius
    (name S (var 1) (Syn.shift (Syn.shift s)) (Syn.shift (Syn.shift i)) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)))
    (name S (var 0) (Syn.shift (Syn.shift s)) (Syn.shift (Syn.shift i)) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)))
    (Syn.shift (Syn.shift d)) (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

def initialBound (S : PR 2) (s i d x : PTm n) : Fm PTm n :=
  .all (pointRadius (name S (var 0) (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x))
    (entry (sample S (Syn.shift s) (Syn.shift x)) (Syn.shift i)) (Syn.shift d) (num 3) (unit (Syn.shift s)))

def supportAll (S : PR 2) (s i d x : PTm n) : Fm PTm n :=
  .all (supportAt S (var 0) (Syn.shift s) (Syn.shift i) (Syn.shift d) (Syn.shift x))

def sourceResult (S : PR 2) (s i d x : PTm n) : Fm PTm n :=
  nameRegular S s i d x ⋏ (initialBound S s i d x ⋏ supportAll S s i d x)

theorem name_regular_all (S : PR 2) (s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) : Γ ⊢[PRAAx] nameRegular S s i d x := by
  refine .allI (.allI ?_)
  have ne : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift, subst_nonempty, Syn.shift] using hS.shift.shift
  have reg : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] regular S (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift, subst_regular, Syn.shift] using hR.shift.shift
  have seed : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      lt (Syn.shift (Syn.shift i)) (length (sample S (Syn.shift (Syn.shift s)) (Syn.shift (Syn.shift x)))) := by
    simpa only [Fm.shift, subst_lt, Foundations.SequenceComposition.subst_length, subst_sample, Syn.shift] using hi.shift.shift
  exact name_regular S (var 1) (var 0) _ _ _ _ ne reg seed

theorem initial_bound_all (S : PR 2) (s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) : Γ ⊢[PRAAx] initialBound S s i d x := by
  refine .allI ?_
  have ne : Γ.map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift x) := by
    simpa only [Fm.shift, subst_nonempty, Syn.shift] using hS.shift
  have reg : Γ.map Fm.shift ⊢[PRAAx] regular S (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift, subst_regular, Syn.shift] using hR.shift
  have seed : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (sample S (Syn.shift s) (Syn.shift x))) := by
    simpa only [Fm.shift, subst_lt, Foundations.SequenceComposition.subst_length, subst_sample, Syn.shift] using hi.shift
  exact name_near_initial S (var 0) _ _ _ _ ne reg seed

theorem support_all (S : PR 2) (s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) : Γ ⊢[PRAAx] supportAll S s i d x := by
  refine .allI ?_
  have ne : Γ.map Fm.shift ⊢[PRAAx] nonempty S (Syn.shift x) := by
    simpa only [Fm.shift, subst_nonempty, Syn.shift] using hS.shift
  have reg : Γ.map Fm.shift ⊢[PRAAx] regular S (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift, subst_regular, Syn.shift] using hR.shift
  have seed : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (sample S (Syn.shift s) (Syn.shift x))) := by
    simpa only [Fm.shift, subst_lt, Foundations.SequenceComposition.subst_length, subst_sample, Syn.shift] using hi.shift
  exact support_at S (var 0) _ _ _ _ ne reg seed

theorem aggregate_chain (S : PR 2) (s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) : Γ ⊢[PRAAx] sourceResult S s i d x :=
  .andI (name_regular_all S s i d x hS hR hi)
    (.andI (initial_bound_all S s i d x hS hR hi) (support_all S s i d x hS hR hi))

/-- Full internal finite-observation endpoint of `thm:aggregate-chain`. -/
theorem aggregate_chain_closed (S : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (nonempty S (var 3) ⟶ regular S (var 2) (var 3) ⟶
        lt (var 1) (length (sample S (var 0) (var 3))) ⟶
        sourceResult S (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (aggregate_chain S _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem sharp_tail_closed (S : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (nonempty S (var 5) ⟶ regular S (var 4) (var 5) ⟶
        lt (var 3) (length (sample S (var 2) (var 5))) ⟶
        pointRadius (point S (var 1) (var 2) (var 3) (var 4) (var 5))
          (point S (var 1+var 0) (var 2) (var 3) (var 4) (var 5)) (var 4)
          (tailNumerator (var 0)) (tailDenominator (var 2) (var 1) (var 0))) :=
  closeUniv 6 (.impI (.impI (.impI (sharp_tail S _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem distance_regular_closed (S : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (nonempty S (var 5) ⟶ regular S (var 4) (var 5) ⟶
        lt (var 3) (length (sample S (var 2) (var 5))) ⟶
        distanceRegular S (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (distance_regular S _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem chain_programs_closed (S : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((apply5 (indexProgramF S) (var 0) (var 1) (var 2) (var 3) (var 4) ≐ index S (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((apply5 (nameF S) (var 0) (var 1) (var 2) (var 3) (var 4) ≐ name S (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((apply5 (distanceF S) (var 0) (var 1) (var 2) (var 3) (var 4) ≐ distanceSample S (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        (apply5 (neighborF S) (var 0) (var 1) (var 2) (var 3) (var 4) ≐ distanceNeighbor S (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.andI (index_program_at S _ _ _ _ _) (.andI (name_program_at S _ _ _ _ _)
    (.andI (distance_program_at S _ _ _ _ _) (neighbor_program_at S _ _ _ _ _))))

/-! ## Optional source coding contract for genuinely stored `d`-vectors -/

def shaped (S : PR 2) (d x : PTm n) : Fm PTm n :=
  .all (.all (lt (var 0) (length (sample S (var 1) (Syn.shift (Syn.shift x)))) ⟶
    (length (entry (sample S (var 1) (Syn.shift (Syn.shift x))) (var 0)) ≐ Syn.shift (Syn.shift d))))

ipra_subst shaped [Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_lt, Foundations.SequenceComposition.subst_length,
    Foundations.MasterCertificate.subst_entry, subst_sample, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst, Syn.shift_var, Fin.succ_zero_eq_one]

theorem shaped_at (S : PR 2) (t j d x : PTm n) (h : Γ ⊢[PRAAx] shaped S d x)
    (hj : Γ ⊢[PRAAx] lt j (length (sample S t x))) :
    Γ ⊢[PRAAx] length (entry (sample S t x) j) ≐ d := by
  have a := Prf.allE t h
  simp [shaped, Syn.up, Syn.subst_shift, ← Syn.shift_subst] at a
  have b := Prf.allE j a
  simp at b
  have hx : Syn.subst (Syn.inst j) (Syn.subst (fun a => var a.succ) x) = x := Syn.subst_inst_shift j x
  have hd : Syn.subst (Syn.inst j) (Syn.subst (fun a => var a.succ) d) = d := Syn.subst_inst_shift j d
  simp only [hx, hd] at b
  exact .impE b hj

theorem point_length (S : PR 2) (r s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hshape : Γ ⊢[PRAAx] shaped S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] length (point S r s i d x) ≐ d :=
  shaped_at S _ _ d x hshape (index_in_range S r s i d x hS hi)

theorem name_length (S : PR 2) (t s i d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hshape : Γ ⊢[PRAAx] shaped S d x)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] length (name S t s i d x) ≐ d := point_length S _ _ _ _ _ hS hshape hi

theorem name_length_closed (S : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (nonempty S (var 4) ⟶ shaped S (var 3) (var 4) ⟶
        lt (var 2) (length (sample S (var 1) (var 4))) ⟶
        (length (name S (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (name_length S _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.AggregateChain
