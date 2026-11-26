import IPRADerivations.Foundations.BackwardViability
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.InductionTactic

/-!
# Finite solvability without a coherent branch (`ipra_categorical_methods`, `thm:tree`)

Packet: `foundations/ipra_categorical_methods`, Section 5, Subsection "Every finite horizon may
be solvable without a computable branch", theorem `thm:tree`: "There is a uniformly PR sequence
of nonempty finite sets `A_n` of binary words of length `n`, with PR restriction maps
`A_{n+1} → A_n` and a PR selector choosing one element of each `A_n`, but no computable binary
sequence whose length-`n` prefix belongs to `A_n` for every `n`."

The construction is derived for an arbitrary observation term `o(n, e)` (in the packet: `0` when
`φ_e(e)` has not halted within `n` steps, `1` when it has halted with output `0`, `2` when it has
halted with output `1`) that is persistent (`Persist`: a nonzero observation is kept at the next
step; "halted configurations are absorbing").

* `Adm n c`: the word `c` is admissible at level `n`, condition (T): for every `e < n`,
  `o(n, e) = 1` gives bit `e` of `c` equal to `1`, and `o(n, e) = 2` gives it equal to `0`
  (`adm_elim`);
* `selc n`: the selector, the word with bits `[o(n, e) = 1]`; `sel_word`: it is a word of length
  `n`; `sel_adm`: it is admissible, so every `A_n` is inhabited by a primitive recursive element;
* `restrict_adm`: the prefix `c mod 2^n` of a word admissible at level `n + 1` is admissible at
  level `n` (`bit_rem`, `restrict_pt`, `restrict_word`);
* `persist_add`, `persist_le`: a nonzero observation is kept at all later times;
* `no_coherent`: the diagonal step. If `c` is admissible at level `n`, `d < n`, `t ≤ n`, and the
  observation at time `t` of index `d` is the bit `d` of `c` (bit `0` observed as `1`, bit `1`
  observed as `2`), a contradiction follows.

The packet's conclusion, that no computable sequence has all prefixes admissible, applies
`no_coherent` to an index `d` of the sequence and its halting time `t`; the existence of that
index is a fact about the fixed simulator and is not an iPRA sentence. It is not formalized.

Instance: the constant observation `1` is persistent (`allHalt_persist`), and its admissible
words have all bits equal to `1` (`allHalt_bit`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.CoherenceObstruction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.ProductPower (dg dg_low rem_lt'')
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases one_ne_zero)
open LeanProofs.IPRA.Foundations.BackwardViability (lt_two_of_bit bit_of_lt_two)
open LeanProofs.IPRA.Foundations.FiniteSetExponential
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

theorem two_pos : Γ ⊢[PRAAx] (two : PTm k) ≐ succ (pred two) :=
  pos_of_eq_succ (c := one) (.eqRefl _)

private theorem up_shift {m j : ℕ} (σ : Fin m → PTm j) (t : PTm m) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

/-- Persistence of a nonzero observation at the next step. -/
structure Persist (o : PTm 2) : Prop where
  keep : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {n e : PTm k},
    (Γ ⊢[PRAAx] inst2 o n e ≐ succ (pred (inst2 o n e))) →
      (Γ ⊢[PRAAx] inst2 o (succ n) e ≐ inst2 o n e)

variable (o : PTm 2)

/-! ## Admissible words -/

/-- Condition (T): the word `c` is admissible at level `n`. -/
def Adm (n c : PTm k) : Fm PTm k :=
  Fm.all (lt (var 0) (Syn.shift n) ⟶
    (((inst2 o (Syn.shift n) (var 0) ≐ one) ⟶ (dg two (var 0) (Syn.shift c) ≐ one)) ⋏
      ((inst2 o (Syn.shift n) (var 0) ≐ two) ⟶ (dg two (var 0) (Syn.shift c) ≐ zero))))

@[simp] theorem subst_Adm {m : ℕ} (σ : Fin k → PTm m) (n c : PTm k) :
    (Adm o n c).subst σ = Adm o (Syn.subst σ n) (Syn.subst σ c) := by
  simp [Adm, up_shift]

theorem shift_Adm (n c : PTm k) :
    Fm.shift (Adm o n c) = Adm o (Syn.shift n) (Syn.shift c) := by
  simp [Fm.shift, Syn.shift]

/-- The two clauses of (T) at an index below the level. -/
theorem adm_elim {n c e : PTm k} (h : Γ ⊢[PRAAx] Adm o n c) (he : Γ ⊢[PRAAx] lt e n) :
    Γ ⊢[PRAAx] ((inst2 o n e ≐ one) ⟶ (dg two e c ≐ one)) ⋏
      ((inst2 o n e ≐ two) ⟶ (dg two e c ≐ zero)) := by
  have a : Γ ⊢[PRAAx] lt e n ⟶
      (((inst2 o n e ≐ one) ⟶ (dg two e c ≐ one)) ⋏
        ((inst2 o n e ≐ two) ⟶ (dg two e c ≐ zero))) := by
    simpa [Adm] using Prf.allE e h
  exact .impE a he

/-! ## The selector -/

/-- The selector bit `[o(n, e) = 1]`; variables `0 = e`, `1 = n`. -/
def sT : PTm 2 := eqb (inst2 o (var 1) (var 0)) one

theorem inst2_sT (e n : PTm k) : inst2 (sT o) e n = eqb (inst2 o n e) one := by
  show Syn.subst ![e, n] (sT o) = _
  simp [sT]

/-- The selected word of level `n`. -/
abbrev selc (n : PTm k) : PTm k := code (sT o) n two n

theorem shift_selc (n : PTm k) : Syn.shift (selc o n) = selc o (Syn.shift n) := by
  simp [Syn.shift]

/-- The bits of the selected word. -/
theorem sel_bit {n e : PTm k} (he : Γ ⊢[PRAAx] lt e n) :
    Γ ⊢[PRAAx] dg two e (selc o n) ≐ eqb (inst2 o n e) one := by
  have r := ev_curry_of_lt (sT o) (N := n) (j := e) (p := n) two_pos he
    (by rw [inst2_sT]; exact lt_two_of_bit (eqb_cases _ _))
  rw [inst2_sT] at r
  exact r

/-- The selected word is a word of length `n`. -/
theorem sel_word (n : PTm k) : Γ ⊢[PRAAx] lt (selc o n) (pw two n) :=
  code_lt (sT o) two_pos n n

theorem sel_pt {n e : PTm k} (he : Γ ⊢[PRAAx] lt e n) :
    Γ ⊢[PRAAx] ((inst2 o n e ≐ one) ⟶ (dg two e (selc o n) ≐ one)) ⋏
      ((inst2 o n e ≐ two) ⟶ (dg two e (selc o n) ≐ zero)) :=
  .andI (.impI ((sel_bit o he).wk.eqTrans (eqb_of_eq Prf.hyp0)))
    (.impI ((sel_bit o he).wk.eqTrans
      (eqb_zero_of_gt (lt_congr (.eqRefl _) Prf.hyp0.eqSymm (le_refl two)))))

/-- The selected word is admissible: every level is inhabited by a primitive recursive word. -/
theorem sel_adm (n : PTm k) : Γ ⊢[PRAAx] Adm o n (selc o n) := by
  refine .allI (.impI ?_)
  rw [shift_selc]
  exact sel_pt o Prf.hyp0

/-- Every level is inhabited, as a closed sentence. Variable: `0 = n`. -/
theorem sel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (lt (selc o (var 0)) (pw two (var 0)) ⋏ Adm o (var 0) (selc o (var 0))) :=
  closeUniv 1 (.andI (sel_word o _) (sel_adm o _))

/-! ## Restriction to a prefix -/

/-- The bits below `n` of the prefix `c mod 2^n` are those of `c`. -/
theorem bit_rem {n c e : PTm k} (he : Γ ⊢[PRAAx] lt e n) :
    Γ ⊢[PRAAx] dg two e (rem c (pw two n)) ≐ dg two e c := by
  have d := pair_eta (pw_pos' (two_pos (Γ := Γ)) n) c
  exact ((congrAp2 remF (congrAp2 quoF d (.eqRefl _)) (.eqRefl _)).eqTrans
    (dg_low two_pos he)).eqSymm

/-- The prefix is a word of length `n`. -/
theorem restrict_word (n c : PTm k) : Γ ⊢[PRAAx] lt (rem c (pw two n)) (pw two n) :=
  rem_lt'' (pw_pos' two_pos n) c

variable {o}

theorem restrict_pt (P : Persist o) {n c e : PTm k} (h : Γ ⊢[PRAAx] Adm o (succ n) c)
    (he : Γ ⊢[PRAAx] lt e n) :
    Γ ⊢[PRAAx] ((inst2 o n e ≐ one) ⟶ (dg two e (rem c (pw two n)) ≐ one)) ⋏
      ((inst2 o n e ≐ two) ⟶ (dg two e (rem c (pw two n)) ≐ zero)) := by
  have a := adm_elim o h (le_trans he (le_succ_self n))
  refine .andI (.impI ?_) (.impI ?_)
  · have h1 : ((inst2 o n e ≐ one) :: Γ) ⊢[PRAAx] inst2 o n e ≐ one := Prf.hyp0
    have up := (P.keep (pos_of_eq_succ (c := zero) h1)).eqTrans h1
    exact (bit_rem he.wk).eqTrans (.impE (Prf.andE₁ a.wk) up)
  · have h2 : ((inst2 o n e ≐ two) :: Γ) ⊢[PRAAx] inst2 o n e ≐ two := Prf.hyp0
    have up := (P.keep (pos_of_eq_succ (c := one) h2)).eqTrans h2
    exact (bit_rem he.wk).eqTrans (.impE (Prf.andE₂ a.wk) up)

/-- The prefix of a word admissible at level `n + 1` is admissible at level `n`. -/
theorem restrict_adm (P : Persist o) {n c : PTm k} (h : Γ ⊢[PRAAx] Adm o (succ n) c) :
    Γ ⊢[PRAAx] Adm o n (rem c (pw two n)) := by
  refine .allI (.impI ?_)
  have h' := h.shift
  rw [shift_Adm] at h'
  have e₁ : Syn.shift (rem c (pw two n)) = rem (Syn.shift c) (pw two (Syn.shift n)) := by
    simp [Syn.shift]
  have e₂ : Syn.shift (succ n) = succ (Syn.shift n) := by simp [Syn.shift]
  rw [e₁]
  rw [e₂] at h'
  exact restrict_pt P h'.wk Prf.hyp0

/-! ## Persistence in time -/

/-- Variables: `0 = d`, `1 = n`, `2 = e`. -/
private abbrev perF (o : PTm 2) : Fm PTm 3 :=
  (inst2 o (var 1) (var 2) ≐ succ (pred (inst2 o (var 1) (var 2)))) ⟶
    (inst2 o (var 1 + var 0) (var 2) ≐ inst2 o (var 1) (var 2))

private theorem per₀ (P : Persist o) : ([] : List (Fm PTm 3)) ⊢[PRAAx] perF o := by
  ipra_ind (⟨trivial, trivial⟩) [subst_inst2]
  · exact .impI (congrInst2 o (add_zero _) (.eqRefl _))
  · refine .impI ?_
    have hp : [inst2 o (var 1 : PTm 3) (var 2) ≐ succ (pred (inst2 o (var 1) (var 2))), perF o]
        ⊢[PRAAx] inst2 o (var 1 : PTm 3) (var 2) ≐ succ (pred (inst2 o (var 1) (var 2))) :=
      Prf.hyp0
    have ih : [inst2 o (var 1 : PTm 3) (var 2) ≐ succ (pred (inst2 o (var 1) (var 2))), perF o]
        ⊢[PRAAx] inst2 o (var 1 + var 0 : PTm 3) (var 2) ≐ inst2 o (var 1) (var 2) :=
      .impE Prf.hyp1 hp
    have st := P.keep (pos_of_eq_succ (c := pred (inst2 o (var 1 : PTm 3) (var 2)))
      (ih.eqTrans hp))
    exact ((congrInst2 o (by ipra_ring) (.eqRefl _)).eqTrans st).eqTrans ih

/-- A nonzero observation is kept `d` steps later. -/
theorem persist_add (P : Persist o) {n e : PTm k} (d : PTm k)
    (h : Γ ⊢[PRAAx] inst2 o n e ≐ succ (pred (inst2 o n e))) :
    Γ ⊢[PRAAx] inst2 o (n + d) e ≐ inst2 o n e := by
  have i := inst (Γ := Γ) (per₀ P) (![d, n, e] : Fin 3 → PTm k)
  simp at i
  exact .impE i h

/-- A nonzero observation at time `t` is kept at every later time `n`. -/
theorem persist_le (P : Persist o) {t n e : PTm k} (ht : Γ ⊢[PRAAx] le t n)
    (h : Γ ⊢[PRAAx] inst2 o t e ≐ succ (pred (inst2 o t e))) :
    Γ ⊢[PRAAx] inst2 o n e ≐ inst2 o t e :=
  (congrInst2 o (eq_add_of_le ht) (.eqRefl _)).eqTrans (persist_add P (monus n t) h)

/-! ## The diagonal step -/

/-- No admissible word carries, at an index `d` below its level, the bit that the observation
of index `d` reports: bit `0` observed as `1` ("halted with output `0`") and bit `1` observed as
`2` ("halted with output `1`") are both excluded by condition (T). -/
theorem no_coherent (P : Persist o) {n c d t : PTm k} (hc : Γ ⊢[PRAAx] Adm o n c)
    (hd : Γ ⊢[PRAAx] lt d n) (ht : Γ ⊢[PRAAx] le t n)
    (h0 : Γ ⊢[PRAAx] (dg two d c ≐ zero) ⟶ (inst2 o t d ≐ one))
    (h1 : Γ ⊢[PRAAx] (dg two d c ≐ one) ⟶ (inst2 o t d ≐ two)) :
    Γ ⊢[PRAAx] Fm.bot := by
  have a := adm_elim o hc hd
  refine .orE (bit_of_lt_two (dg_lt two_pos d c)) ?_ ?_
  · have b0 : ((dg two d c ≐ zero) :: Γ) ⊢[PRAAx] dg two d c ≐ zero := Prf.hyp0
    have ot := Prf.impE h0.wk b0
    have on := (persist_le P ht.wk (pos_of_eq_succ (c := zero) ot)).eqTrans ot
    exact one_ne_zero _ ((Prf.impE (Prf.andE₁ a.wk) on).eqSymm.eqTrans b0)
  · have b1 : ((dg two d c ≐ one) :: Γ) ⊢[PRAAx] dg two d c ≐ one := Prf.hyp0
    have ot := Prf.impE h1.wk b1
    have on := (persist_le P ht.wk (pos_of_eq_succ (c := one) ot)).eqTrans ot
    exact one_ne_zero _ (b1.eqSymm.eqTrans (Prf.impE (Prf.andE₂ a.wk) on))

/-! ## An instance: every index observed as halted with output zero -/

/-- The constant observation `1`. -/
def allHalt : PTm 2 := one

theorem inst2_allHalt (n e : PTm k) : inst2 allHalt n e = one := by simp [inst2, allHalt]

theorem allHalt_persist : Persist allHalt where
  keep := fun _ => by rw [inst2_allHalt, inst2_allHalt]; exact .eqRefl _

/-- For the constant observation `1`, every bit below the level of an admissible word is `1`. -/
theorem allHalt_bit {n c e : PTm k} (h : Γ ⊢[PRAAx] Adm allHalt n c) (he : Γ ⊢[PRAAx] lt e n) :
    Γ ⊢[PRAAx] dg two e c ≐ one := by
  have a := Prf.andE₁ (adm_elim allHalt h he)
  rw [inst2_allHalt] at a
  exact .impE a (.eqRefl _)

end LeanProofs.IPRA.Foundations.CoherenceObstruction
