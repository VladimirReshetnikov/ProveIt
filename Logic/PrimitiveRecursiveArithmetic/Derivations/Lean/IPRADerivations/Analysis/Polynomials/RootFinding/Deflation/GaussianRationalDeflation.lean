import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticDivision
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianDescentClock
import IPRADerivations.Foundations.SequenceEquality

/-!
# The actual runtime outer deflation loop

Finite-demand source04 thm:approx-factor, the finite constructor itself.
Every stage computes its approximate root with the actual remaining degree,
current polynomial and supplied rational tolerance, then constructs the actual
normalized synthetic quotient and appends that root to the output list.
All counters, degrees, coefficients and tolerance data are internal inputs.

The structural degree, monicity, canonical-coefficient and root-list invariants
are proved independently of residual estimates. No quotient, factorization,
coefficient bound, radius bound, residual estimate or RD contract is assumed
for these structural conclusions. Error estimates remain separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDeflation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (quotient canonicalCoefficients qone)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition
  (length empty append empty_length append_length append_left append_right subst_length subst_empty subst_append entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def singleton (z : PTm n) : PTm n := sequence (var 1 : PTm 2) one z
def data (C N e f : PTm n) : PTm n := pairT N (pairT C (pairT e f))
def remaining (N j : PTm n) : PTm n := monus N j

def next (step : PR 3) (j s N e f : PTm n) : PTm n :=
  let z := GaussianDescentClock.approximateRoot step (remaining N j) (fstT s) e f
  pairT (quotient (fstT s) z (remaining N j)) (append (sndT s) (singleton z))
def initialBody : PTm 1 := pairT (fstT (sndT (var 0))) empty
def stepBody (step : PR 3) : PTm 3 := next step (var 0) (var 1)
  (fstT (var 2)) (fstT (sndT (sndT (var 2)))) (sndT (sndT (sndT (var 2))))
def stateF (step : PR 3) : PR 2 := rec2 initialBody (stepBody step)
def state (step : PR 3) (C N e f j : PTm n) : PTm n := ap2 (stateF step) j (data C N e f)
def polynomial (step : PR 3) (C N e f j : PTm n) : PTm n := fstT (state step C N e f j)
def roots (step : PR 3) (C N e f j : PTm n) : PTm n := sndT (state step C N e f j)
def rootAt (step : PR 3) (C N e f j : PTm n) : PTm n :=
  GaussianDescentClock.approximateRoot step (remaining N j) (polynomial step C N e f j) e f

@[simp] theorem subst_singleton {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (singleton z) = singleton (Syn.subst σ z) := by simp [singleton]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (C N e f : PTm n) :
    Syn.subst σ (data C N e f) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ e) (Syn.subst σ f) := by simp [data]
@[simp] theorem subst_remaining {m : ℕ} (σ : Fin n → PTm m) (N j : PTm n) :
    Syn.subst σ (remaining N j) = remaining (Syn.subst σ N) (Syn.subst σ j) := by simp [remaining]
@[simp] theorem subst_next {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (j s N e f : PTm n) :
    Syn.subst σ (next step j s N e f) = next step (Syn.subst σ j) (Syn.subst σ s)
      (Syn.subst σ N) (Syn.subst σ e) (Syn.subst σ f) := by simp [next]
@[simp] theorem subst_state {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N e f j : PTm n) :
    Syn.subst σ (state step C N e f j) = state step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ j) := by simp [state]
@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N e f j : PTm n) :
    Syn.subst σ (polynomial step C N e f j) = polynomial step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ j) := by simp [polynomial]
@[simp] theorem subst_roots {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N e f j : PTm n) :
    Syn.subst σ (roots step C N e f j) = roots step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ j) := by simp [roots]
@[simp] theorem subst_rootAt {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N e f j : PTm n) :
    Syn.subst σ (rootAt step C N e f j) = rootAt step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ j) := by simp [rootAt]

theorem singleton_length (z : PTm n) : Γ ⊢[PRAAx] length (singleton z) ≐ one := sequence_length _ _ _
theorem singleton_entry (z : PTm n) : Γ ⊢[PRAAx] entry (singleton z) zero ≐ z := by
  have h := sequence_decode (Γ := Γ) (var 1 : PTm 2) (x := z) (zero_lt_succ zero)
  simpa only [singleton,inst2,Syn.subst_var,Matrix.cons_val_one,Matrix.cons_val_zero] using h

theorem state_zero (step : PR 3) (C N e f : PTm n) : Γ ⊢[PRAAx]
    state step C N e f zero ≐ pairT C empty := by
  have h := rec2_zero (Γ := Γ) initialBody (stepBody step) (data C N e f)
  have input : Γ ⊢[PRAAx] fstT (sndT (data C N e f)) ≐ C :=
    (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  exact h.eqTrans (by
    simpa only [initialBody,subst_pairT,subst_fstT,subst_sndT,subst_empty,Syn.subst_var,
      Matrix.cons_val_zero] using congrPairT input (.eqRefl (empty : PTm n)))

theorem step_body_at (step : PR 3) (j s C N e f : PTm n) : Γ ⊢[PRAAx]
    Syn.subst ![j,s,data C N e f] (stepBody step) ≐ next step j s N e f := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (next step (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![j,s,fstT (data C N e f),fstT (sndT (sndT (data C N e f))),sndT (sndT (sndT (data C N e f)))])
    (σ' := ![j,s,N,e,f]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst (congrSnd (snd_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
      · exact (congrSnd (congrSnd (snd_pair _ _))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
  simpa only [stepBody,subst_next,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using h

theorem state_succ (step : PR 3) (C N e f j : PTm n) : Γ ⊢[PRAAx]
    state step C N e f (succ j) ≐ next step j (state step C N e f j) N e f :=
  (rec2_succ initialBody (stepBody step) j (data C N e f)).eqTrans (step_body_at step j _ C N e f)

theorem polynomial_zero (step : PR 3) (C N e f : PTm n) : Γ ⊢[PRAAx]
    polynomial step C N e f zero ≐ C := (congrFst (state_zero step C N e f)).eqTrans (fst_pair _ _)
theorem roots_zero (step : PR 3) (C N e f : PTm n) : Γ ⊢[PRAAx]
    roots step C N e f zero ≐ empty := (congrSnd (state_zero step C N e f)).eqTrans (snd_pair _ _)

theorem polynomial_succ (step : PR 3) (C N e f j : PTm n) : Γ ⊢[PRAAx]
    polynomial step C N e f (succ j) ≐ quotient (polynomial step C N e f j) (rootAt step C N e f j) (remaining N j) :=
  (congrFst (state_succ step C N e f j)).eqTrans (fst_pair _ _)
theorem roots_succ (step : PR 3) (C N e f j : PTm n) : Γ ⊢[PRAAx]
    roots step C N e f (succ j) ≐ append (roots step C N e f j) (singleton (rootAt step C N e f j)) :=
  (congrSnd (state_succ step C N e f j)).eqTrans (snd_pair _ _)

/-- The remaining degree decreases by exactly one at every active stage. -/
theorem remaining_step (N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] remaining N j ≐ succ (remaining N (succ j)) := by
  have h : Γ ⊢[PRAAx] N ≐ j+succ (monus N (succ j)) := (eq_add_of_le hj).eqTrans (by ipra_ring)
  exact (congrMonus h (.eqRefl _)).eqTrans (add_monus' _ _)

theorem remaining_positive (N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] le one (remaining N j) :=
  le_of_eq_add (d := remaining N (succ j)) ((remaining_step N j hj).eqTrans (by ipra_ring))

def invariant (step : PR 3) (C N e f j : PTm n) : Fm PTm n := le j N ⟶
  (length (polynomial step C N e f j) ≐ succ (remaining N j) ⋏
    (entry (polynomial step C N e f j) zero ≐ qone))

@[simp] theorem subst_invariant {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N e f j : PTm n) :
    (invariant step C N e f j).subst σ = invariant step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ j) := by simp [invariant]

theorem invariant_zero (step : PR 3) (C N e f : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx]
    length (polynomial step C N e f zero) ≐ succ (remaining N zero) ⋏
      (entry (polynomial step C N e f zero) zero ≐ qone) :=
  .andI ((congrFst (polynomial_zero step C N e f)).eqTrans (hC.eqTrans (congrSucc (monus_zero N)).eqSymm))
    ((entry_congr (polynomial_zero step C N e f) (.eqRefl _)).eqTrans hm)

theorem invariant_step (step : PR 3) (C N e f j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (ih : Γ ⊢[PRAAx] length (polynomial step C N e f j) ≐ succ (remaining N j) ⋏
      (entry (polynomial step C N e f j) zero ≐ qone)) : Γ ⊢[PRAAx]
    length (polynomial step C N e f (succ j)) ≐ succ (remaining N (succ j)) ⋏
      (entry (polynomial step C N e f (succ j)) zero ≐ qone) := by
  have monic := GaussianRationalSyntheticDivision.quotient_monic
    (polynomial step C N e f j) (rootAt step C N e f j) (remaining N j) (remaining_positive N j hj) (Prf.andE₂ ih)
  exact .andI
    ((congrFst (polynomial_succ step C N e f j)).eqTrans
      ((GaussianRationalSyntheticDivision.quotient_length _ _ _).eqTrans (remaining_step N j hj)))
    ((entry_congr (polynomial_succ step C N e f j) (.eqRefl _)).eqTrans (Prf.andE₂ monic))

theorem polynomial_invariant (step : PR 3) (C N e f j : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    length (polynomial step C N e f j) ≐ succ (remaining N j) ⋏
      (entry (polynomial step C N e f j) zero ≐ qone) := by
  have all : Γ ⊢[PRAAx] .all (invariant step (Syn.shift C) (Syn.shift N) (Syn.shift e) (Syn.shift f) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨trivial,trivial⟩⟩ ?_ ?_
    · simp only [subst_invariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (invariant_zero step C N e f hC.wk hm.wk)
    · simp only [subst_invariant,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := invariant step (Syn.shift C) (Syn.shift N) (Syn.shift e) (Syn.shift f) (var 0)
      let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
      exact invariant_step _ _ _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] invariant step C N e f j := by
    simpa only [subst_invariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j all
  exact .impE rule hj

/-- The actual accumulated root list has exactly one entry per stage,
even outside the active-degree range where no polynomial claim is made. -/
theorem roots_length (step : PR 3) (C N e f j : PTm n) : Γ ⊢[PRAAx]
    length (roots step C N e f j) ≐ j := by
  have all : Γ ⊢[PRAAx] .all (length (roots step (Syn.shift C) (Syn.shift N) (Syn.shift e) (Syn.shift f) (var 0)) ≐ var 0) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_length,subst_roots,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (congrFst (roots_zero step C N e f)).eqTrans empty_length
    · simp only [Fm.subst_eq,subst_length,subst_roots,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (roots_succ _ _ _ _ _ _)).eqTrans ((append_length _ _).eqTrans
        ((congrAdd Prf.hyp0 (singleton_length _)).eqTrans (by ipra_ring)))
  simpa only [Fm.subst_eq,subst_length,subst_roots,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j all

theorem coefficients_congr {C D : PTm n} (h : Γ ⊢[PRAAx] C ≐ D)
    (hd : Γ ⊢[PRAAx] canonicalCoefficients D) : Γ ⊢[PRAAx] canonicalCoefficients C := by
  have p := Prf.eqSubst (canonicalCoefficients (var 0) : Fm PTm 1) ![D] ![C]
    (fun i => by fin_cases i; exact h.eqSymm) (by simpa using hd)
  simpa using p

/-- Canonical quotient storage follows from the actual preceding stage,
without induction on the bounded universal storage guard. -/
theorem polynomial_canonical (step : PR 3) (C N e f j : PTm n)
    (hj : Γ ⊢[PRAAx] le one j) : Γ ⊢[PRAAx] canonicalCoefficients (polynomial step C N e f j) := by
  have counter := congrFst (congrAp2 (stateF step) (RationalIntegerNormalization.positive_form hj) (.eqRefl (data C N e f)))
  have p : Γ ⊢[PRAAx] polynomial step C N e f j ≐
      quotient (polynomial step C N e f (pred j)) (rootAt step C N e f (pred j)) (remaining N (pred j)) :=
    counter.eqTrans (polynomial_succ step C N e f (pred j))
  exact coefficients_congr p (GaussianRationalSyntheticDivision.quotient_canonical _ _ _)

theorem root_canonical (step : PR 3) (C N e f j : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (rootAt step C N e f j) :=
  GaussianDescentClock.iterate_canonical _ _ _ _

/-- The newly stored point is literally the computed approximate root. -/
theorem roots_new_entry (step : PR 3) (C N e f j : PTm n) : Γ ⊢[PRAAx]
    entry (roots step C N e f (succ j)) j ≐ rootAt step C N e f j := by
  have pos : Γ ⊢[PRAAx] lt zero (length (singleton (rootAt step C N e f j))) :=
    lt_congr (.eqRefl _) (singleton_length _).eqSymm (le_refl one)
  have index : Γ ⊢[PRAAx] j ≐ length (roots step C N e f j)+zero :=
    (roots_length step C N e f j).eqSymm.eqTrans (add_zero _).eqSymm
  exact (entry_congr (roots_succ step C N e f j) (.eqRefl _)).eqTrans
    ((entry_congr (.eqRefl _) index).eqTrans
      ((append_right (a := roots step C N e f j) pos).eqTrans (singleton_entry _)))

theorem roots_preserve_entry (step : PR 3) (C N e f j i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    entry (roots step C N e f (succ j)) i ≐ entry (roots step C N e f j) i :=
  (entry_congr (roots_succ step C N e f j) (.eqRefl _)).eqTrans
    (append_left (lt_congr (.eqRefl _) (roots_length step C N e f j).eqSymm hi))

/-- Exactly N iterations produce N roots and a monic constant polynomial. -/
theorem final_shape (step : PR 3) (C N e f : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) :
    Γ ⊢[PRAAx] length (roots step C N e f N) ≐ N ⋏
      (length (polynomial step C N e f N) ≐ one ⋏
        (entry (polynomial step C N e f N) zero ≐ qone)) := by
  have h := polynomial_invariant step C N e f N hC hm (le_refl _)
  exact .andI (roots_length step C N e f N) (.andI
    ((Prf.andE₁ h).eqTrans (congrSucc (monus_self N))) (Prf.andE₂ h))

/-- For represented degree one, the actual constructed quotient is the
literal singleton-one polynomial, not just a list with equal decoded values. -/
theorem constant_quotient (C z : PTm n) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) :
    Γ ⊢[PRAAx] quotient C z one ≐ singleton qone := by
  have agree : Γ ⊢[PRAAx] Foundations.SequenceEquality.agree
      GaussianRationalSyntheticDivision.quotientBody (var 1 : PTm 2) one (pairT C z) qone := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) one :: Γ.map Fm.shift
    have index : Δ ⊢[PRAAx] var 0 ≐ zero := le_antisymm
      ((succ_monus_succ (var 0) zero).eqSymm.eqTrans Prf.hyp0) (zero_le _)
    have monic : Δ ⊢[PRAAx] entry (Syn.shift C) zero ≐ qone := by
      simpa only [Δ,Fm.shift,Fm.subst_eq,subst_entry,GaussianRationalSyntheticDivision.subst_qone,
        ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift.wk
    have leading := Prf.andE₂ (GaussianRationalSyntheticDivision.quotient_monic (Syn.shift C) (Syn.shift z) one (le_refl one) monic)
    have first : Δ ⊢[PRAAx] GaussianRationalHorner.horner (Syn.shift C) (Syn.shift z) (succ zero) ≐ qone :=
      (GaussianRationalSyntheticDivision.quotient_lookup _ _ _ zero (le_refl one)).eqSymm.eqTrans leading
    have value : Δ ⊢[PRAAx] inst2 GaussianRationalSyntheticDivision.quotientBody (var 0) (pairT (Syn.shift C) (Syn.shift z)) ≐ qone :=
      (GaussianRationalSyntheticDivision.quotient_body_at _ _ _).eqTrans
        ((congrAp3 GaussianRationalHorner.hornerF (congrSucc index) (.eqRefl _) (.eqRefl _)).eqTrans first)
    simpa only [Δ,Syn.shift,subst_pairT,GaussianRationalSyntheticDivision.subst_qone,
      inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using value
  exact Foundations.SequenceEquality.sequence_equal _ _ _ _ _ agree

/-- The final monic constant is literally the canonical singleton-one
sequence. Positivity ensures the last polynomial was actually constructed;
no extensionality of malformed original list codes is used. -/
theorem final_polynomial_one (step : PR 3) (C N e f : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] polynomial step C N e f N ≐ singleton qone := by
  have pos := RationalIntegerNormalization.positive_form hN
  have bound : Γ ⊢[PRAAx] le (pred N) N := le_congr (.eqRefl _) pos.eqSymm (le_succ_self _)
  have leading := Prf.andE₂ (polynomial_invariant step C N e f (pred N) hC hm bound)
  have rem : Γ ⊢[PRAAx] remaining N (pred N) ≐ one :=
    (congrMonus (pos.eqTrans (by ipra_ring)) (.eqRefl _)).eqTrans (add_monus' one (pred N))
  have counter : Γ ⊢[PRAAx] polynomial step C N e f N ≐ polynomial step C N e f (succ (pred N)) :=
    congrFst (congrAp2 (stateF step) pos (.eqRefl _))
  have q := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (quotient (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![polynomial step C N e f (pred N),rootAt step C N e f (pred N),remaining N (pred N)])
    (σ' := ![polynomial step C N e f (pred N),rootAt step C N e f (pred N),one])
    (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact rem)
  have reduced : Γ ⊢[PRAAx]
      quotient (polynomial step C N e f (pred N)) (rootAt step C N e f (pred N)) (remaining N (pred N)) ≐
      quotient (polynomial step C N e f (pred N)) (rootAt step C N e f (pred N)) one := by simpa using q
  exact counter.eqTrans ((polynomial_succ _ _ _ _ _ _).eqTrans (reduced.eqTrans (constant_quotient _ _ leading)))

/-- Every stored root retains its exact stage index and actual computation. -/
theorem rootAt_congr (step : PR 3) (C N e f : PTm n) {i j : PTm n}
    (h : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] rootAt step C N e f i ≐ rootAt step C N e f j := by
  have p := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (rootAt step (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![C,N,e,f,i]) (σ' := ![C,N,e,f,j]) (fun k => by fin_cases k <;> first | exact h | exact .eqRefl _)
  simpa only [subst_rootAt,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using p

def lookupLaw (step : PR 3) (C N e f i j : PTm n) : Fm PTm n := lt i j ⟶
  (entry (roots step C N e f j) i ≐ rootAt step C N e f i)
@[simp] theorem subst_lookupLaw {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (C N e f i j : PTm n) :
    (lookupLaw step C N e f i j).subst σ = lookupLaw step (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ i) (Syn.subst σ j) := by simp [lookupLaw]

theorem roots_lookup_step (step : PR 3) (C N e f i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ j))
    (ih : Γ ⊢[PRAAx] lookupLaw step C N e f i j) : Γ ⊢[PRAAx]
    entry (roots step C N e f (succ j)) i ≐ rootAt step C N e f i := by
  refine .orE (lt_or_le i j) ?_ ?_
  · exact (roots_preserve_entry step C N e f j i Prf.hyp0).eqTrans (.impE ih.wk Prf.hyp0)
  · have eq : (le j i) :: Γ ⊢[PRAAx] i ≐ j :=
      le_antisymm ((succ_monus_succ i j).eqSymm.eqTrans hi.wk) Prf.hyp0
    exact (entry_congr (.eqRefl _) eq).eqTrans
      ((roots_new_entry step C N e f j).eqTrans (rootAt_congr step C N e f eq.eqSymm))

theorem roots_lookup (step : PR 3) (C N e f j i : PTm n) (hi : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    entry (roots step C N e f j) i ≐ rootAt step C N e f i := by
  have all : Γ ⊢[PRAAx] .all (lookupLaw step (Syn.shift C) (Syn.shift N) (Syn.shift e) (Syn.shift f) (Syn.shift i) (var 0)) := by
    refine PRA.qfInd _ ⟨lt_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_lookupLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (lt_zero_absurd _ Prf.hyp0)
    · simp only [subst_lookupLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (roots_lookup_step _ _ _ _ _ _ _ Prf.hyp0 Prf.hyp1)
  have rule : Γ ⊢[PRAAx] lookupLaw step C N e f i j := by
    simpa only [subst_lookupLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j all
  exact .impE rule hi

theorem roots_canonical (step : PR 3) (C N e f j : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (roots step C N e f j) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (roots step C N e f j))) :: Γ.map Fm.shift
  have input : Δ ⊢[PRAAx] lt (var 0) (length (roots step (Syn.shift C) (Syn.shift N) (Syn.shift e) (Syn.shift f) (Syn.shift j))) := by
    simpa only [Δ,Syn.shift,subst_roots] using Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift)
      (φ := lt (var 0) (length (Syn.shift (roots step C N e f j))))
  have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift j) := lt_congr (.eqRefl _) (roots_length _ _ _ _ _ _) input
  have h := GaussianRationalHorner.canonical_congr
    (roots_lookup step (Syn.shift C) (Syn.shift N) (Syn.shift e) (Syn.shift f) (Syn.shift j) (var 0) range)
    (root_canonical step (Syn.shift C) (Syn.shift N) (Syn.shift e) (Syn.shift f) (var 0))
  simpa only [Δ,Syn.shift,subst_roots] using h

/-- Each active actual stage satisfies the exact synthetic-division identity;
this is derived from the computed quotient, not a deflation-law assumption. -/
theorem stage_division (step : PR 3) (C N e f j y : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (polynomial step C N e f j) y ≐
      GaussianRationalHorner.qadd
        (GaussianRationalHorner.qmul (GaussianRationalMetric.qsub y (rootAt step C N e f j))
          (GaussianRationalHorner.evaluate (polynomial step C N e f (succ j)) y))
        (GaussianRationalHorner.evaluate (polynomial step C N e f j) (rootAt step C N e f j)) := by
  have shape := Prf.andE₁ (polynomial_invariant step C N e f j hC hm (le_trans (le_succ_self _) hj))
  have division := GaussianRationalSyntheticDivision.division_evaluation
    (polynomial step C N e f j) (rootAt step C N e f j) y (remaining N j) shape
  have eval := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (GaussianRationalHorner.evaluate (var 0) (var 1) : PTm 2)
    (σ := ![quotient (polynomial step C N e f j) (rootAt step C N e f j) (remaining N j),y])
    (σ' := ![polynomial step C N e f (succ j),y])
    (fun i => by fin_cases i; exact (polynomial_succ step C N e f j).eqSymm; exact .eqRefl _)
  have eqEval : Γ ⊢[PRAAx]
      GaussianRationalHorner.evaluate (quotient (polynomial step C N e f j) (rootAt step C N e f j) (remaining N j)) y ≐
      GaussianRationalHorner.evaluate (polynomial step C N e f (succ j)) y := by simpa using eval
  exact division.eqTrans (GaussianRationalSyntheticDivision.qadd_congr
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) eqEval) (.eqRefl _))

def outputF (step : PR 3) : PR 4 := PTm.toPR (state step (var 0) (var 1) (var 2) (var 3) (var 1))
def run (step : PR 3) (C N e f : PTm n) : PTm n := PTm.app (outputF step) ![C,N,e,f]

theorem program_at (step : PR 3) (C N e f : PTm n) : Γ ⊢[PRAAx]
    run step C N e f ≐ state step C N e f N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (state step (var 0) (var 1) (var 2) (var 3) (var 1) : PTm 4) ![C,N,e,f]
theorem output_polynomial (step : PR 3) (C N e f : PTm n) : Γ ⊢[PRAAx]
    fstT (run step C N e f) ≐ polynomial step C N e f N := congrFst (program_at step C N e f)
theorem output_roots (step : PR 3) (C N e f : PTm n) : Γ ⊢[PRAAx]
    sndT (run step C N e f) ≐ roots step C N e f N := congrSnd (program_at step C N e f)

theorem deflation_structure_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((length (var 0) ≐ succ (var 1)) ⟶ (entry (var 0) zero ≐ qone) ⟶ le (var 4) (var 1) ⟶
      ((length (polynomial step (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ succ (remaining (var 1) (var 4))) ⋏
        (entry (polynomial step (var 0) (var 1) (var 2) (var 3) (var 4)) zero ≐ qone))) :=
  closeUniv 5 (.impI (.impI (.impI (polynomial_invariant _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem deflation_root_list_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((length (roots step (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 4) ⋏
      (lt (var 5) (var 4) ⟶ (entry (roots step (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐
        rootAt step (var 0) (var 1) (var 2) (var 3) (var 5)))) :=
  closeUniv 6 (.andI (roots_length _ _ _ _ _ _) (.impI (roots_lookup _ _ _ _ _ _ _ Prf.hyp0)))

theorem deflation_stage_division_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((length (var 0) ≐ succ (var 1)) ⟶ (entry (var 0) zero ≐ qone) ⟶ lt (var 4) (var 1) ⟶
      (GaussianRationalHorner.evaluate (polynomial step (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐
        GaussianRationalHorner.qadd
          (GaussianRationalHorner.qmul (GaussianRationalMetric.qsub (var 5) (rootAt step (var 0) (var 1) (var 2) (var 3) (var 4)))
            (GaussianRationalHorner.evaluate (polynomial step (var 0) (var 1) (var 2) (var 3) (succ (var 4))) (var 5)))
          (GaussianRationalHorner.evaluate (polynomial step (var 0) (var 1) (var 2) (var 3) (var 4))
            (rootAt step (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 6 (.impI (.impI (.impI (stage_division _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem deflation_final_polynomial_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (var 0) ≐ succ (var 1)) ⟶ (entry (var 0) zero ≐ qone) ⟶ le one (var 1) ⟶
      (polynomial step (var 0) (var 1) (var 2) (var 3) (var 1) ≐ singleton qone)) :=
  closeUniv 4 (.impI (.impI (.impI (final_polynomial_one _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem deflation_program_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (run step (var 0) (var 1) (var 2) (var 3)) ≐ polynomial step (var 0) (var 1) (var 2) (var 3) (var 1)) ⋏
      (sndT (run step (var 0) (var 1) (var 2) (var 3)) ≐ roots step (var 0) (var 1) (var 2) (var 3) (var 1))) :=
  closeUniv 4 (.andI (output_polynomial _ _ _ _ _) (output_roots _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRationalDeflation
