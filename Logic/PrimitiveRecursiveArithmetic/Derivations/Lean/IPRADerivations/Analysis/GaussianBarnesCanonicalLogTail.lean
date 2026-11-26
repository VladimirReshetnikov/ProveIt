import IPRADerivations.Analysis.GaussianBarnesCanonicalLogRow
import IPRADerivations.Analysis.GaussianRationalFiniteSum
import IPRADerivations.Core.CongruenceTactic

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogRow (finiteValue boundNumerator boundDenominator subst_finiteValue subst_boundNumerator)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qzero qadd positive_product zero_represents)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalReciprocal (bounded_sum bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "nativeBound" => ComplexLogarithmRemainder.bounded

def source (z R B N : PTm n) : Fm PTm n := GaussianBarnesCanonicalLogRow.source z R B N

def data (z B N L : PTm n) : PTm n := pairT z (pairT B (pairT N L))

def body : PTm 2 := finiteValue (fstT (var 1)) (fstT (sndT (var 1)))
  (succ (fstT (sndT (sndT (var 1)))+var 0)) (sndT (sndT (sndT (var 1))))

def value (z B N r L : PTm n) : PTm n := sum body r (data z B N L)

def intervalDenominator (N r : PTm n) : PTm n := num 3*N*(N+r)
def tailDenominator (N : PTm n) : PTm n := num 3*N

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    (source z R B N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [source]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B N L : PTm n) :
    Syn.subst σ (data z B N L) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ L) := by simp [data]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z B N r L : PTm n) :
    Syn.subst σ (value z B N r L) =
      value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ L) := by simp [value]

@[simp] theorem subst_intervalDenominator {m : ℕ} (σ : Fin n → PTm m) (N r : PTm n) :
    Syn.subst σ (intervalDenominator N r) = intervalDenominator (Syn.subst σ N) (Syn.subst σ r) := by
  simp [intervalDenominator]

@[simp] theorem subst_tailDenominator {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (tailDenominator N) = tailDenominator (Syn.subst σ N) := by simp [tailDenominator]

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

theorem tail_denominator_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (tailDenominator N) :=
  positive_product _ _ (le_of_eq_add (d := two) (by ipra_ring)) hN

theorem interval_denominator_positive (N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (intervalDenominator N r) :=
  positive_product _ _ (tail_denominator_positive N hN) (le_trans hN (le_add_right N r))

theorem row_source (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalLogRow.source z R B (succ (N+r)) :=
  .andI h.andE₁ (.andI (zero_lt_succ _) (.andI h.andE₂.andE₂.andE₁
    (le_trans h.andE₂.andE₂.andE₂ (le_trans (le_add_right _ _) (le_succ_self _)))))

private theorem interval_zero (z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (value z B N zero L) (boundNumerator R*zero) (intervalDenominator N zero) := by
  let A := boundNumerator R
  let D := intervalDenominator N zero
  have hD := interval_denominator_positive N zero h.andE₂.andE₁
  have h0 : Γ ⊢[PRAAx] bounded qzero zero D :=
    bounded_of_cleared qzero ComplexLogarithmRemainder.zeroCode one zero D (le_refl one) hD (zero_represents _)
      (le_congr (mul_zero _).eqSymm (.eqRefl _) (zero_le _)
        |> le_congr (congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_zero).eqSymm (.eqRefl _))
  exact bound_congr (value_zero z B N L).eqSymm (mul_zero A).eqSymm (.eqRefl _) h0

private theorem interval_step (z R B N r L : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (ih : Γ ⊢[PRAAx] bounded (value z B N r L) (boundNumerator R*r) (intervalDenominator N r)) :
    Γ ⊢[PRAAx] bounded (value z B N (succ r) L) (boundNumerator R*succ r) (intervalDenominator N (succ r)) := by
  let A := boundNumerator R
  let k := succ (N+r)
  let D := intervalDenominator N r
  let E := boundDenominator k
  let F := intervalDenominator N (succ r)
  have hD := interval_denominator_positive N r h.andE₂.andE₁
  have hE := GaussianBarnesCanonicalLogRow.bound_denominator_positive (Γ := Γ) k (zero_lt_succ _)
  have hF := interval_denominator_positive N (succ r) h.andE₂.andE₁
  have next := GaussianBarnesCanonicalLogRow.finite_bound z R B k L (row_source z R B N r h)
  have added := bounded_sum (value z B N r L) (finiteValue z B k L) (A*r) D A E hD hE ih next
  have budget : Γ ⊢[PRAAx] le ((A*r*E+A*D)*F) ((A*succ r)*(D*E)) := by
    apply le_of_eq_add (d := num 9*A*N*N*k)
    dsimp only [D,E,F,k,intervalDenominator,boundDenominator]
    ipra_ring
  exact bound_congr (value_succ z B N r L).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hE) hF budget added)

theorem interval_bound (z R B N r L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (value z B N r L) (boundNumerator R*r) (intervalDenominator N r) := by
  let sh (x : PTm n) := Syn.shift x
  have all : Γ ⊢[PRAAx] .all (bounded (value (sh z) (sh B) (sh N) (var 0) (sh L))
      (boundNumerator (sh R)*var 0) (intervalDenominator (sh N) (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [GaussianRationalMetric.subst_bounded, subst_value, subst_boundNumerator, subst_intervalDenominator,
        PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, sh] using interval_zero z R B N L h
    · have shifted : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by
        simpa [Fm.shift,Syn.shift,sh] using h.shift
      simpa only [GaussianRationalMetric.subst_bounded, subst_value, subst_boundNumerator, subst_intervalDenominator,
        PTm.subst_mul, Syn.subst_var, Syn.repl_zero, subst_repl_shift, sh] using
        interval_step (sh z) (sh R) (sh B) (sh N) (var 0) (sh L) shifted.wk Prf.hyp0
  simpa only [GaussianRationalMetric.subst_bounded, subst_value, subst_boundNumerator, subst_intervalDenominator,
    PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, sh] using all.allE r

theorem tail_bound (z R B N r L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (value z B N r L) (boundNumerator R) (tailDenominator N) :=
  bounded_radius_mono _ _ _ _ _ (interval_denominator_positive N r h.andE₂.andE₁)
    (tail_denominator_positive N h.andE₂.andE₁)
    (le_of_eq_add (d := boundNumerator R*tailDenominator N*N) (by unfold intervalDenominator tailDenominator; ipra_ring))
    (interval_bound z R B N r L h)

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
