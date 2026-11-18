import IPRADerivations.Foundations.DemandClosure
import IPRADerivations.Foundations.ChainViability
import IPRADerivations.Foundations.SequenceComposition

/-!
# A concrete cyclic two-coordinate demand closure

The actual operator is (min B (y+1), min C (x+1)). Its cap preservation
and monotonicity are derived from arithmetic, not provided as contracts.
The checked finite-demand orbit therefore stabilizes after B+C steps and
is the least capped prefixed point. Both caps, including zero, are runtime
data. This is a cyclic precision-demand instance, not certificate execution.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.TwoCoordinateDemandClosure

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.DemandClosure
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def two : PTm n := succ one
def clip (B x : PTm n) : PTm n := monus B (monus B x)
def value (a b i : PTm n) : PTm n := a*monus one i+b*monus one (monus one i)
def vectorBody : PTm 2 := value (fstT (var 1)) (sndT (var 1)) (var 0)
def vector (a b : PTm n) : PTm n := sequence vectorBody two (pairT a b)
def update (B C v : PTm n) : PTm n := vector
  (clip B (succ (entry v one))) (clip C (succ (entry v zero)))
def operator : PTm 2 := update (fstT (var 1)) (sndT (var 1)) (var 0)

@[simp] theorem subst_two {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (two : PTm n) = two := by simp [two]
@[simp] theorem subst_clip {m : ℕ} (σ : Fin n → PTm m) (B x : PTm n) :
    Syn.subst σ (clip B x) = clip (Syn.subst σ B) (Syn.subst σ x) := by simp [clip]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (a b i : PTm n) :
    Syn.subst σ (value a b i) = value (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ i) := by simp [value]
@[simp] theorem subst_vector {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (vector a b) = vector (Syn.subst σ a) (Syn.subst σ b) := by simp [vector]
@[simp] theorem subst_update {m : ℕ} (σ : Fin n → PTm m) (B C v : PTm n) :
    Syn.subst σ (update B C v) = update (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ v) := by simp [update]

theorem clip_le (B x : PTm n) : Γ ⊢[PRAAx] le (clip B x) B := ChainViability.monus_le _ _
theorem clip_of_above (B x : PTm n) (h : Γ ⊢[PRAAx] le B x) : Γ ⊢[PRAAx] clip B x ≐ B :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)
theorem clip_of_below (B x : PTm n) (h : Γ ⊢[PRAAx] le x B) : Γ ⊢[PRAAx] clip B x ≐ x := by
  have e := (eq_add_of_le h).eqTrans (add_comm _ _)
  exact (congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _)
theorem clip_mono (B x y : PTm n) (h : Γ ⊢[PRAAx] le x y) : Γ ⊢[PRAAx] le (clip B x) (clip B y) := by
  refine .orE (le_total B y) ?_ ?_
  · exact le_congr (.eqRefl _) (clip_of_above B y Prf.hyp0).eqSymm (clip_le B x)
  · exact le_congr (clip_of_below B x (le_trans h.wk Prf.hyp0)).eqSymm
      (clip_of_below B y Prf.hyp0).eqSymm h.wk

theorem vector_congr {a b c d : PTm n} (h : Γ ⊢[PRAAx] a ≐ c) (k : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] vector a b ≐ vector c d := by
  simpa only [subst_vector,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (Prf.eqCongr (vector (var 0) (var 1) : PTm 2) (σ := ![a,b]) (σ' := ![c,d])
      (fun i => by fin_cases i <;> assumption))
theorem update_congr {B C v B' C' v' : PTm n}
    (hB : Γ ⊢[PRAAx] B ≐ B') (hC : Γ ⊢[PRAAx] C ≐ C') (hv : Γ ⊢[PRAAx] v ≐ v') :
    Γ ⊢[PRAAx] update B C v ≐ update B' C' v' := by
  simpa only [subst_update,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    (Prf.eqCongr (update (var 0) (var 1) (var 2) : PTm 3) (σ := ![B,C,v]) (σ' := ![B',C',v'])
      (fun i => by fin_cases i <;> assumption))
theorem value_at (a b i : PTm n) : Γ ⊢[PRAAx] inst2 vectorBody i (pairT a b) ≐ value a b i := by
  simp only [vectorBody,inst2,subst_value,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAdd (congrMul (fst_pair _ _) (.eqRefl _)) (congrMul (snd_pair _ _) (.eqRefl _))
theorem vector_lookup (a b i : PTm n) (hi : Γ ⊢[PRAAx] lt i two) :
    Γ ⊢[PRAAx] entry (vector a b) i ≐ value a b i :=
  (MasterCertificate.sequence_decode vectorBody hi).eqTrans (value_at a b i)
theorem vector_zero (a b : PTm n) : Γ ⊢[PRAAx] entry (vector a b) zero ≐ a := by
  refine (vector_lookup a b zero (zero_lt_succ one)).eqTrans ?_
  exact (congrAdd (congrMul (.eqRefl _) (monus_zero one))
    (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (monus_zero one)).eqTrans (monus_self one)))).eqTrans
      (by ipra_ring)
theorem vector_one (a b : PTm n) : Γ ⊢[PRAAx] entry (vector a b) one ≐ b := by
  refine (vector_lookup a b one (le_refl two)).eqTrans ?_
  exact (congrAdd (congrMul (.eqRefl _) (monus_self one))
    (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (monus_self one)).eqTrans (monus_zero one)))).eqTrans
      (by ipra_ring)
theorem vector_length (a b : PTm n) : Γ ⊢[PRAAx] length (vector a b) ≐ two :=
  MasterCertificate.sequence_length _ _ _
theorem ordered_vector {a b c d : PTm n} (ha : Γ ⊢[PRAAx] le a c) (hb : Γ ⊢[PRAAx] le b d) :
    Γ ⊢[PRAAx] ordered two (vector a b) (vector c d) := by
  apply ordered_intro
  refine .allI (.impI ?_)
  have ha' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using ha.shift
  have hb' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift b) (Syn.shift d) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hb.shift
  have h : (lt (var 0) (two : PTm (n+1)) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (value (Syn.shift a) (Syn.shift b) (var 0)) (value (Syn.shift c) (Syn.shift d) (var 0)) :=
    add_le_add₂ (mul_le_mul_right _ ha'.wk) (mul_le_mul_right _ hb'.wk)
  simpa only [Syn.shift,subst_vector,subst_two] using
    (le_congr (vector_lookup (Syn.shift a) (Syn.shift b) (var 0) Prf.hyp0).eqSymm
      (vector_lookup (Syn.shift c) (Syn.shift d) (var 0) Prf.hyp0).eqSymm h)
theorem operator_at (B C v : PTm n) : Γ ⊢[PRAAx] inst2 operator v (pairT B C) ≐ update B C v := by
  simp only [operator,inst2,subst_update,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact update_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)
theorem update_bounded (B C v : PTm n) : Γ ⊢[PRAAx] ordered two (update B C v) (vector B C) :=
  ordered_vector (clip_le _ _) (clip_le _ _)
theorem succ_mono {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (succ a) (succ b) :=
  le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one h)
theorem update_mono (B C v w : PTm n) (h : Γ ⊢[PRAAx] ordered two v w) :
    Γ ⊢[PRAAx] ordered two (update B C v) (update B C w) :=
  ordered_vector (clip_mono _ _ _ (succ_mono (ordered_at h (le_refl two))))
    (clip_mono _ _ _ (succ_mono (ordered_at h (zero_lt_succ one))))
private theorem ordered_congr {r r' a a' b b' : PTm n}
    (hr : Γ ⊢[PRAAx] r ≐ r') (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (h : Γ ⊢[PRAAx] ordered r a b) : Γ ⊢[PRAAx] ordered r' a' b' := by
  have hs : Γ ⊢[PRAAx] (ordered (var 0) (var 1) (var 2) : Fm PTm 3).subst ![r,a,b] := by
    simpa only [subst_ordered,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h
  have ht := Prf.eqSubst (ordered (var 0) (var 1) (var 2) : Fm PTm 3)
    ![r,a,b] ![r',a',b'] (fun j => by fin_cases j <;> assumption) hs
  simpa only [subst_ordered,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using ht

theorem maps (B C : PTm n) : Γ ⊢[PRAAx] mapsInto operator two (vector B C) (pairT B C) := by
  unfold mapsInto
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_vector,subst_pairT,subst_two] using
    (ordered_congr (.eqRefl _) (operator_at (Syn.shift B) (Syn.shift C) (var 0)).eqSymm (.eqRefl _)
      (update_bounded (Γ := ordered two (var 0) (vector (Syn.shift B) (Syn.shift C)) :: Γ.map Fm.shift)
        (Syn.shift B) (Syn.shift C) (var 0)))
theorem monotone (B C : PTm n) : Γ ⊢[PRAAx] monotoneOn operator two (vector B C) (pairT B C) := by
  unfold monotoneOn
  refine .allI (.allI (.impI (.impI (.impI ?_))))
  simpa only [Syn.shift,subst_pairT,subst_two] using
    (ordered_congr (.eqRefl _)
      (operator_at (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift C)) (var 1)).eqSymm
      (operator_at (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift C)) (var 0)).eqSymm
      (update_mono _ _ _ _ (Prf.hyp0 :
        (ordered two (var 1) (var 0) ::
          ordered two (var 0) (Syn.shift (Syn.shift (vector B C))) ::
          ordered two (var 1) (Syn.shift (Syn.shift (vector B C))) ::
          (Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx] _)))

theorem rank_vector (B C : PTm n) : Γ ⊢[PRAAx] rank two (vector B C) ≐ B+C := by
  have e1 := sum_succ' (Γ := Γ) coordinateBody one (vector B C)
  have e0 := sum_succ' (Γ := Γ) coordinateBody zero (vector B C)
  rw [coordinateBody_at] at e1 e0
  have h1 := natEq e1
  have h0 := natEq e0
  have hz := natEq (sum_zero (Γ := Γ) coordinateBody (vector B C))
  have hB := natEq (vector_zero (Γ := Γ) B C)
  have hC := natEq (vector_one (Γ := Γ) B C)
  unfold rank two
  apply deriveNat; ipra_simps
  rw [h1,h0,hz,hB,hC]
  ring

theorem actual_cyclic_closure (B C : PTm n) : Γ ⊢[PRAAx]
    closureConclusion operator two (vector B C) (pairT B C) := demand_closure (maps B C) (monotone B C)

def orbit (B C k : PTm n) : PTm n := iterate operator k two (pairT B C)
def result (B C : PTm n) : PTm n := orbit B C (B+C)
def resultF : PR 2 := PTm.toPR (result (var 0) (var 1))
def run (B C : PTm n) : PTm n := ap2 resultF B C
@[simp] theorem subst_orbit {m : ℕ} (σ : Fin n → PTm m) (B C k : PTm n) :
    Syn.subst σ (orbit B C k) = orbit (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ k) := by simp [orbit]
@[simp] theorem subst_result {m : ℕ} (σ : Fin n → PTm m) (B C : PTm n) :
    Syn.subst σ (result B C) = result (Syn.subst σ B) (Syn.subst σ C) := by simp [result]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (B C : PTm n) :
    Syn.subst σ (run B C) = run (Syn.subst σ B) (Syn.subst σ C) := by simp [run]

theorem rank_stage (B C : PTm n) : Γ ⊢[PRAAx]
    iterate operator (rank two (vector B C)) two (pairT B C) ≐ result B C :=
  congrAp2 _ (rank_vector B C) (.eqRefl _)
theorem rank_next_stage (B C : PTm n) : Γ ⊢[PRAAx]
    iterate operator (succ (rank two (vector B C))) two (pairT B C) ≐ orbit B C (succ (B+C)) :=
  congrAp2 _ (congrSucc (rank_vector B C)) (.eqRefl _)
theorem result_bounded (B C : PTm n) : Γ ⊢[PRAAx] ordered two (result B C) (vector B C) :=
  iterate_bounded_at (maps B C) (B+C)
theorem result_prefixed (B C : PTm n) : Γ ⊢[PRAAx] prefixed operator two (result B C) (pairT B C) :=
  ordered_congr (.eqRefl _) (congrInst2 operator (rank_stage B C) (.eqRefl _))
    (rank_stage B C) (closure_prefixed (maps B C) (monotone B C))
theorem result_stable_at (B C i : PTm n) (hi : Γ ⊢[PRAAx] lt i two) : Γ ⊢[PRAAx]
    entry (result B C) i ≐ entry (orbit B C (succ (B+C))) i := by
  have h := Prf.allE i (closure_stable (Γ := Γ) (maps B C) (monotone B C))
  simp only [coordinatesEQ,Fm.subst_imp,Fm.subst_eq,subst_lt,MasterCertificate.subst_entry,
    subst_iterate,subst_rank,subst_vector,subst_pairT,subst_two,Syn.subst_var,Syn.inst_zero,
    Syn.subst_inst_shift,ConciseIPRA.PTm.subst_succ] at h
  exact (entry_congr (rank_stage B C).eqSymm (.eqRefl _)).eqTrans
    ((Prf.impE h hi).eqTrans (entry_congr (rank_next_stage B C) (.eqRefl _)))
theorem result_least (B C e : PTm n) (he : Γ ⊢[PRAAx] ordered two e (vector B C))
    (hp : Γ ⊢[PRAAx] prefixed operator two e (pairT B C)) : Γ ⊢[PRAAx] ordered two (result B C) e :=
  iterate_le_prefixed_at (maps B C) (monotone B C) he hp (B+C)
theorem result_program (B C : PTm n) : Γ ⊢[PRAAx] run B C ≐ result B C := by
  simpa only [run,resultF,ap2,subst_result,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (result (var 0) (var 1) : PTm 2) ![B,C]
theorem returned_bounded (B C : PTm n) : Γ ⊢[PRAAx] ordered two (run B C) (vector B C) :=
  ordered_congr (.eqRefl _) (result_program B C).eqSymm (.eqRefl _) (result_bounded B C)
theorem returned_prefixed (B C : PTm n) : Γ ⊢[PRAAx] prefixed operator two (run B C) (pairT B C) :=
  ordered_congr (.eqRefl _) (congrInst2 operator (result_program B C).eqSymm (.eqRefl _))
    (result_program B C).eqSymm (result_prefixed B C)
theorem returned_stable_at (B C i : PTm n) (hi : Γ ⊢[PRAAx] lt i two) : Γ ⊢[PRAAx]
    entry (run B C) i ≐ entry (orbit B C (succ (B+C))) i :=
  (entry_congr (result_program B C) (.eqRefl _)).eqTrans (result_stable_at B C i hi)
theorem returned_least (B C e : PTm n) (he : Γ ⊢[PRAAx] ordered two e (vector B C))
    (hp : Γ ⊢[PRAAx] prefixed operator two e (pairT B C)) : Γ ⊢[PRAAx] ordered two (run B C) e :=
  ordered_congr (.eqRefl _) (result_program B C).eqSymm (.eqRefl _) (result_least B C e he hp)

theorem actual_cap_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rank two (vector (var 0) (var 1)) ≐ var 0+var 1) := closeUniv 2 (rank_vector _ _)
theorem actual_operator_contracts_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (mapsInto operator two (vector (var 0) (var 1)) (pairT (var 0) (var 1)) ⋏
      monotoneOn operator two (vector (var 0) (var 1)) (pairT (var 0) (var 1))) :=
  closeUniv 2 (.andI (maps _ _) (monotone _ _))
theorem actual_cyclic_closure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (closureConclusion operator two (vector (var 0) (var 1)) (pairT (var 0) (var 1))) :=
  closeUniv 2 (actual_cyclic_closure _ _)
theorem actual_result_bounded_prefixed_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ordered two (run (var 0) (var 1)) (vector (var 0) (var 1)) ⋏
      prefixed operator two (run (var 0) (var 1)) (pairT (var 0) (var 1))) :=
  closeUniv 2 (.andI (returned_bounded _ _) (returned_prefixed _ _))
theorem actual_sum_budget_stability_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) two ⟶ entry (run (var 0) (var 1)) (var 2) ≐
      entry (orbit (var 0) (var 1) (succ (var 0+var 1))) (var 2)) :=
  closeUniv 3 (.impI (returned_stable_at _ _ _ Prf.hyp0))
theorem actual_least_prefixed_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ordered two (var 2) (vector (var 0) (var 1)) ⟶
      prefixed operator two (var 2) (pairT (var 0) (var 1)) ⟶ ordered two (run (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (returned_least _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_result_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ orbit (var 0) (var 1) (var 0+var 1)) := closeUniv 2 (result_program _ _)

end LeanProofs.IPRA.Foundations.TwoCoordinateDemandClosure
