import IPRADerivations.Analysis.Barnes.Logarithms.FiniteRows.GaussianBarnesCanonicalLogRow
import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianScaledReciprocalSquareInterval

/-!
# Sharp finite sums of the original Barnes logarithms

The actual rational finite sum consists of the cubic Barnes rows at
k=N+1 through N+r. Their reciprocal-square norm estimates telescope
inside iPRA. At the corrected Barnes cutoff the norm is at most
2^(-p-5), for every internal sum length and Taylor degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogTail

open_ipra
open GaussianBarnesCanonicalLogRow (finiteValue boundNumerator boundDenominator subst_finiteValue subst_boundNumerator)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qzero qadd positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianCoefficientNameBounds (bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "nativeBound" => ComplexLogarithmRemainder.bounded

def source (z R B N : PTm n) : Fm PTm n := GaussianBarnesCanonicalLogRow.source z R B N

def data (z B N L : PTm n) : PTm n := pairT z (pairT B (pairT N L))

def body : PTm 2 := finiteValue (fstT (var 1)) (fstT (sndT (var 1)))
  (succ (fstT (sndT (sndT (var 1)))+var 0)) (sndT (sndT (sndT (var 1))))

def value (z B N r L : PTm n) : PTm n := sum body r (data z B N L)

def intervalDenominator (N r : PTm n) : PTm n := num 3*N*(N+r)
def tailDenominator (N : PTm n) : PTm n := num 3*N

ipra_subst source

ipra_subst data

ipra_subst value

ipra_subst intervalDenominator

ipra_subst tailDenominator

theorem body_at (z B N L i : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (data z B N L) ≐ finiteValue z B (succ (N+i)) L := by
  let X := data z B N L
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (finiteValue (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT X,fstT (sndT X),succ (fstT (sndT (sndT X))+i),sndT (sndT (sndT X))])
    (σ' := ![z,B,succ (N+i),L]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact congrSucc (congrAdd
          ((congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)) (.eqRefl _))
      · exact (congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))
  simpa only [body,inst2,subst_finiteValue,subst_fstT,subst_sndT,PTm.subst_add,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,X] using fields

theorem value_zero (z B N L : PTm n) : Γ ⊢[PRAAx] value z B N zero L ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _

theorem value_succ (z B N r L : PTm n) :
    Γ ⊢[PRAAx] value z B N (succ r) L ≐ qadd (value z B N r L) (finiteValue z B (succ (N+r)) L) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (body_at z B N L r))

private theorem three_positive : Γ ⊢[PRAAx] le one (num 3 : PTm n) :=
  le_of_eq_add (d := two) (by ipra_ring)

theorem tail_denominator_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (tailDenominator N) :=
  positive_product _ _ three_positive hN

theorem interval_denominator_positive (N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (intervalDenominator N r) :=
  positive_product _ _ (tail_denominator_positive N hN) (le_trans hN (le_add_right N r))

theorem row_source (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalLogRow.source z R B (succ (N+r)) :=
  .andI h.andE₁ (.andI (zero_lt_succ _) (.andI h.andE₂.andE₂.andE₁
    (le_trans h.andE₂.andE₂.andE₂ (le_trans (le_add_right _ _) (le_succ_self _)))))

private theorem rows_bounded (z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianScaledReciprocalSquareInterval.rows body N (boundNumerator R) (num 3) (data z B N L) := by
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
  have next := GaussianBarnesCanonicalLogRow.finite_bound (sh z) (sh R) (sh B) (succ (sh N+i)) (sh L)
    (row_source (sh z) (sh R) (sh B) (sh N) i hs)
  have rebracket : Δ ⊢[PRAAx] boundDenominator (succ (sh N+i)) ≐
      num 3*(succ (sh N+i)*succ (sh N+i)) := by
    unfold boundDenominator
    ipra_ring
  simpa only [GaussianScaledReciprocalSquareInterval.rows,Syn.shift,sh,Δ,i,subst_data,subst_boundNumerator,PTm.subst_num]
    using bound_congr (body_at (sh z) (sh B) (sh N) (sh L) i).eqSymm (.eqRefl _) rebracket next

theorem interval_bound (z R B N r L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (value z B N r L) (boundNumerator R*r) (intervalDenominator N r) :=
  bound_congr (.eqRefl _) (.eqRefl _)
    (by unfold intervalDenominator GaussianReciprocalSquareInterval.denominator; ipra_ring)
    (GaussianScaledReciprocalSquareInterval.interval_bound body N r (boundNumerator R) (num 3) (data z B N L)
      h.andE₂.andE₁ three_positive (rows_bounded z R B N L h))

theorem tail_bound (z R B N r L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (value z B N r L) (boundNumerator R) (tailDenominator N) :=
  GaussianScaledReciprocalSquareInterval.tail_bound body N r (boundNumerator R) (num 3) (data z B N L)
    h.andE₂.andE₁ three_positive (rows_bounded z R B N L h)

theorem cutoff_bound (z R B p r L : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hR : Γ ⊢[PRAAx] le one R) (hz : Γ ⊢[PRAAx] nativeBound z (R*B)) :
    Γ ⊢[PRAAx] bounded (value z B (BarnesCutoff.cutoff R p) r L) one (BarnesCutoff.budget p) := by
  let N := BarnesCutoff.cutoff R p
  have hN : Γ ⊢[PRAAx] le one N := BarnesCutoff.cutoff_positive p hR
  have h := BarnesCutoff.cutoff_guards (Γ := Γ) R p
  have hP : Γ ⊢[PRAAx] le one (BarnesCutoff.budget p) := GaussianCoefficientNameBounds.unit_positive (p+num 5)
  have fit : Γ ⊢[PRAAx] le (boundNumerator R*BarnesCutoff.budget p) (one*tailDenominator N) :=
    le_congr ((BarnesCutoff.scale_budget R p).eqTrans (by unfold boundNumerator; ipra_ring))
      (by unfold tailDenominator BarnesCutoff.three; ipra_ring) h.andE₂
  exact bounded_radius_mono _ _ _ _ _ (tail_denominator_positive N hN) hP fit
    (tail_bound z R B N r L (.andI hB (.andI hN (.andI hz h.andE₁))))

theorem actual_finite_Barnes_logarithm_tail_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) ⟶ bounded (value (var 0) (var 2) (var 3) (var 4) (var 5))
        (boundNumerator (var 1)) (tailDenominator (var 3))) :=
  closeUniv 6 (.impI (tail_bound _ _ _ _ _ _ Prf.hyp0))

theorem actual_finite_Barnes_corrected_cutoff_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (le one (var 2) ⟶ le one (var 1) ⟶ nativeBound (var 0) (var 1*var 2) ⟶
        bounded (value (var 0) (var 2) (BarnesCutoff.cutoff (var 1) (var 3)) (var 4) (var 5))
          one (BarnesCutoff.budget (var 3))) :=
  closeUniv 6 (.impI (.impI (.impI (cutoff_bound _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogTail
