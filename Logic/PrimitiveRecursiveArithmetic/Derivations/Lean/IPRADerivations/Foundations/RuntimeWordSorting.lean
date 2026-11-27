import IPRADerivations.Foundations.RuntimeAdjacentPermutationSwap

/-!
# Actual bounded adjacent sorting of numerical words

The least strict adjacent descent drives the existing numeric swap program.
The actual recursion has fuel `succ (m*m)`; its quantifier-free rank alternative
proves inactivity, rather than assuming termination or a sorting invariant.
No Analysis object, external finite rank or abstract permutation is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RuntimeWordSorting

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_zero sel_one)


variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def descentSyntax (m w i : PTm n) : BFm n :=
  .and (.lt (succ i) m) (.lt (RuntimePermutationWords.digit m w (succ i)) (RuntimePermutationWords.digit m w i))
def descentF : PR 3 := BoundedSyntax.bitF (descentSyntax (var 0) (var 1) (var 2))
def descentBit (m w i : PTm n) : PTm n := app descentF ![m,w,i]
def descentBody : PTm 2 := descentBit (sndT (var 1)) (fstT (var 1)) (var 0)
def active (m w : PTm n) : PTm n := BoundedReflection.exB descentBody m (RuntimePermutationWords.data m w)
def inactive (m w : PTm n) : PTm n := monus one (active m w)
def descentIndex (m w : PTm n) : PTm n := BoundedReflection.wit descentBody m (RuntimePermutationWords.data m w)
def sortStep (m w : PTm n) : PTm n := sel (active m w) (RuntimeAdjacentPermutationSwap.swapWord m w (descentIndex m w)) w
def stateStep : PTm 3 := sortStep (sndT (var 2)) (var 1)
def stateF : PR 2 := rec2 (fstT (var 0)) stateStep
def state (m w j : PTm n) : PTm n := ap2 stateF j (RuntimePermutationWords.data m w)
def fuel (m : PTm n) : PTm n := succ (m*m)
def final (m w : PTm n) : PTm n := state m w (fuel m)
def identityCode (m : PTm n) : PTm n := RuntimePermutationWords.encode (RuntimePermutationWords.identity m) m

@[simp] theorem subst_descentBit {l : ℕ} (σ : Fin n → PTm l) (m w i : PTm n) :
    Syn.subst σ (descentBit m w i) = descentBit (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ i) := by
  simp only [descentBit,ConciseIPRA.PTm.subst_app]
  congr 1
  funext k
  fin_cases k <;> rfl
@[simp] theorem subst_active {l : ℕ} (σ : Fin n → PTm l) (m w : PTm n) :
    Syn.subst σ (active m w) = active (Syn.subst σ m) (Syn.subst σ w) := by simp [active]
ipra_subst inactive
ipra_subst descentIndex
ipra_subst sortStep [sel]
ipra_subst state
ipra_subst fuel
ipra_subst final
ipra_subst identityCode

theorem descent_at (m w i : PTm n) : Γ ⊢[PRAAx] descentBit m w i ≐
    BoundedSyntax.bit (descentSyntax (var 0) (var 1) (var 2)) ![m,w,i] :=
  BoundedSyntax.program_correct _ _
theorem descent_reflection (m w i : PTm n) : Γ ⊢[PRAAx] Fm.iff (descentBit m w i ≐ one)
    (lt (succ i) m ⋏ lt (RuntimePermutationWords.digit m w (succ i)) (RuntimePermutationWords.digit m w i)) := by
  have r : Γ ⊢[PRAAx] Fm.iff
      (BoundedSyntax.bit (descentSyntax (var 0) (var 1) (var 2)) ![m,w,i] ≐ one)
      (lt (succ i) m ⋏ lt (RuntimePermutationWords.digit m w (succ i)) (RuntimePermutationWords.digit m w i)) := by
    simpa [descentSyntax,formula,BFm.lt,BFm.le,lt,le] using
      BoundedSyntax.bounded_reflection (descentSyntax (var 0) (var 1) (var 2)) ![m,w,i]
  exact .iffI (.impI (r.wk.iffMp ((descent_at _ _ _).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((descent_at _ _ _).eqTrans (r.wk.iffMpr Prf.hyp0)))
theorem descent_cases (m w i : PTm n) : Γ ⊢[PRAAx] (descentBit m w i ≐ zero) ⋎ (descentBit m w i ≐ one) :=
  .orE (BoundedSyntax.bit_cases (descentSyntax (var 0) (var 1) (var 2)) ![m,w,i])
    (.orI₁ ((descent_at _ _ _).eqTrans Prf.hyp0)) (.orI₂ ((descent_at _ _ _).eqTrans Prf.hyp0))
theorem descent_body_at (m w i : PTm n) : Γ ⊢[PRAAx]
    inst2 descentBody i (RuntimePermutationWords.data m w) ≐ descentBit m w i := by
  simp only [descentBody,inst2,subst_descentBit,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,RuntimePermutationWords.data]
  ipra_congr (descentBit (var 0) (var 1) (var 2) : PTm 3) with [snd_pair _ _, fst_pair _ _, .eqRefl i]
theorem active_cases (m w : PTm n) : Γ ⊢[PRAAx] (active m w ≐ zero) ⋎ (active m w ≐ one) := BoundedReflection.ex_cases _ _ _
theorem inactive_of_active_zero (m w : PTm n) (h : Γ ⊢[PRAAx] active m w ≐ zero) :
    Γ ⊢[PRAAx] inactive m w ≐ one := (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)
theorem active_zero_of_inactive (m w : PTm n) (h : Γ ⊢[PRAAx] inactive m w ≐ one) :
    Γ ⊢[PRAAx] active m w ≐ zero := by
  refine .orE (active_cases m w) Prf.hyp0 ?_
  exact BoundedReflection.one_ne_zero _ (h.wk.eqSymm.eqTrans ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_self _)))
theorem descent_found (m w : PTm n) (h : Γ ⊢[PRAAx] active m w ≐ one) : Γ ⊢[PRAAx]
    lt (succ (descentIndex m w)) m ⋏ lt (RuntimePermutationWords.digit m w (succ (descentIndex m w))) (RuntimePermutationWords.digit m w (descentIndex m w)) := by
  have hn : Γ ⊢[PRAAx] neg (descentBit m w (descentIndex m w) ≐ zero) :=
    .impI (.impE (Prf.andE₂ (BoundedReflection.ex_elim descentBody h)).wk
      ((descent_body_at _ _ _).eqTrans Prf.hyp0))
  refine .orE (descent_cases m w (descentIndex m w)) (.botE _ (.impE hn.wk Prf.hyp0)) ?_
  exact (descent_reflection _ _ _).iffMp Prf.hyp0
theorem descent_least (m w i : PTm n) (hi : Γ ⊢[PRAAx] lt i (descentIndex m w)) :
    Γ ⊢[PRAAx] descentBit m w i ≐ zero :=
  (descent_body_at _ _ _).eqSymm.eqTrans (BoundedReflection.ex_least descentBody hi)
theorem descent_none (m w i : PTm n) (h : Γ ⊢[PRAAx] inactive m w ≐ one)
    (hi : Γ ⊢[PRAAx] lt (succ i) m) : Γ ⊢[PRAAx] le (RuntimePermutationWords.digit m w i) (RuntimePermutationWords.digit m w (succ i)) := by
  have hz : Γ ⊢[PRAAx] descentBit m w i ≐ zero := (descent_body_at _ _ _).eqSymm.eqTrans
    (BoundedReflection.ex_none descentBody (active_zero_of_inactive _ _ h) (lt_of_le_of_lt (le_succ_self _) hi))
  refine .orE (lt_or_le (RuntimePermutationWords.digit m w (succ i)) (RuntimePermutationWords.digit m w i)) ?_ Prf.hyp0
  have ho := (descent_reflection m w i).iffMpr (.andI hi.wk Prf.hyp0)
  exact BoundedReflection.one_ne_zero _ (ho.eqSymm.eqTrans hz.wk)
theorem step_active (m w : PTm n) (h : Γ ⊢[PRAAx] active m w ≐ one) :
    Γ ⊢[PRAAx] sortStep m w ≐ RuntimeAdjacentPermutationSwap.swapWord m w (descentIndex m w) := sel_one h
theorem step_inactive (m w : PTm n) (h : Γ ⊢[PRAAx] inactive m w ≐ one) :
    Γ ⊢[PRAAx] sortStep m w ≐ w := sel_zero (active_zero_of_inactive _ _ h)
theorem step_bound (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] lt (sortStep m w) (RuntimePermutationWords.horizon m) := by
  refine .orE (active_cases m w) ?_ ?_
  · exact lt_congr (step_inactive _ _ (inactive_of_active_zero _ _ Prf.hyp0)).eqSymm (.eqRefl _) hw.wk
  · exact lt_congr (step_active _ _ Prf.hyp0).eqSymm (.eqRefl _)
      (RuntimeAdjacentPermutationSwap.swapped_bound _ _ _ (.andE₁ (descent_found _ _ Prf.hyp0)))
theorem active_inversion_drop (m w : PTm n) (h : Γ ⊢[PRAAx] active m w ≐ one) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversions m (sortStep m w)+one ≐ RuntimePermutationWords.inversions m w := by
  have df := descent_found m w h
  have ho := RuntimeAdjacentPermutationSwap.old_pair_one m w (descentIndex m w) (.andE₂ df)
  have hz : Γ ⊢[PRAAx] RuntimePermutationWords.inversionBit m (RuntimeAdjacentPermutationSwap.swapWord m w (descentIndex m w)) (descentIndex m w) (succ (descentIndex m w)) ≐ zero := by
    refine .orE (RuntimePermutationWords.inversion_cases m (RuntimeAdjacentPermutationSwap.swapWord m w (descentIndex m w)) (descentIndex m w) (succ (descentIndex m w))) Prf.hyp0 ?_
    have hr : (RuntimePermutationWords.inversionBit m (RuntimeAdjacentPermutationSwap.swapWord m w (descentIndex m w)) (descentIndex m w) (succ (descentIndex m w)) ≐ one) :: Γ ⊢[PRAAx]
        lt (RuntimePermutationWords.digit m w (descentIndex m w)) (RuntimePermutationWords.digit m w (succ (descentIndex m w))) :=
      RuntimeAdjacentPermutationSwap.new_pair_lt m w (descentIndex m w) (.andE₁ df.wk) Prf.hyp0
    exact lt_irrefl _ _ (lt_of_lt_of_le hr (le_of_lt (.andE₂ df.wk)))
  have se : Γ ⊢[PRAAx] RuntimePermutationWords.inversions m (sortStep m w) ≐ RuntimePermutationWords.inversions m (RuntimeAdjacentPermutationSwap.swapWord m w (descentIndex m w)) := by
    ipra_congr (RuntimePermutationWords.inversions (var 0) (var 1) : PTm 2) with [.eqRefl m, step_active _ _ h]
  exact (congrAdd se ho.eqSymm).eqTrans ((RuntimeAdjacentPermutationSwap.inversion_balance _ _ _ (.andE₁ df)).eqTrans
    ((congrAdd (.eqRefl _) hz).eqTrans (add_zero _)))

theorem inversion_bit_bound (m w i j : PTm n) : Γ ⊢[PRAAx] le (RuntimePermutationWords.inversionBit m w i j) one := by
  refine .orE (RuntimePermutationWords.inversion_cases m w i j) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl _)
theorem inversion_row_bound (m w i t : PTm n) : Γ ⊢[PRAAx] le (RuntimePermutationWords.rowPrefix m w i t) t := by
  have all : Γ ⊢[PRAAx] .all (le (RuntimePermutationWords.rowPrefix (Syn.shift m) (Syn.shift w) (Syn.shift i) (var 0)) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le,RuntimePermutationWords.subst_rowPrefix,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact le_congr (RuntimePermutationWords.row_zero _ _ _).eqSymm (.eqRefl _) (le_refl _)
    · simp only [subst_le,RuntimePermutationWords.subst_rowPrefix,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      have hb := inversion_bit_bound (Γ := le (RuntimePermutationWords.rowPrefix (Syn.shift m) (Syn.shift w) (Syn.shift i) (var 0)) (var 0) :: Γ.map Fm.shift)
        (Syn.shift m) (Syn.shift w) (Syn.shift i) (var 0)
      exact le_congr (RuntimePermutationWords.row_succ _ _ _ _).eqSymm (.eqRefl _) (by ipra_le sl Prf.hyp0 + sl hb)
  simpa only [subst_le,RuntimePermutationWords.subst_rowPrefix,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
theorem inversion_prefix_bound (m w t : PTm n) : Γ ⊢[PRAAx] le (RuntimePermutationWords.inversionPrefix m w t) (t*m) := by
  have all : Γ ⊢[PRAAx] .all (le (RuntimePermutationWords.inversionPrefix (Syn.shift m) (Syn.shift w) (var 0)) (var 0*Syn.shift m)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le,RuntimePermutationWords.subst_inversionPrefix,PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact le_congr (RuntimePermutationWords.inversion_prefix_zero _ _).eqSymm (zero_mul _).eqSymm (le_refl _)
    · simp only [subst_le,RuntimePermutationWords.subst_inversionPrefix,PTm.subst_mul,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      have hb := inversion_row_bound (Γ := le (RuntimePermutationWords.inversionPrefix (Syn.shift m) (Syn.shift w) (var 0)) (var 0*Syn.shift m) :: Γ.map Fm.shift)
        (Syn.shift m) (Syn.shift w) (var 0) (Syn.shift m)
      exact le_congr (RuntimePermutationWords.inversion_prefix_succ _ _ _).eqSymm (.eqRefl _) (by ipra_le sl Prf.hyp0 + sl hb)
  simpa only [subst_le,RuntimePermutationWords.subst_inversionPrefix,PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
theorem inversion_bound (m w : PTm n) : Γ ⊢[PRAAx] le (RuntimePermutationWords.inversions m w) (m*m) := inversion_prefix_bound _ _ _

theorem state_zero (m w : PTm n) : Γ ⊢[PRAAx] state m w zero ≐ w := by
  have h := rec2_zero (Γ := Γ) (fstT (var 0)) stateStep (RuntimePermutationWords.data m w)
  simp only [subst_fstT,Syn.subst_var,Matrix.cons_val_zero] at h
  exact h.eqTrans (fst_pair _ _)
theorem state_succ (m w j : PTm n) : Γ ⊢[PRAAx] state m w (succ j) ≐ sortStep m (state m w j) := by
  have h := rec2_succ (Γ := Γ) (fstT (var 0)) stateStep j (RuntimePermutationWords.data m w)
  simp only [stateStep,subst_sortStep,subst_sndT,Syn.subst_var,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] at h
  have e : Γ ⊢[PRAAx] sortStep (sndT (RuntimePermutationWords.data m w)) (state m w j) ≐ sortStep m (state m w j) := by
    simpa only [subst_sortStep,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      (Prf.eqCongr (Γ := Γ) (sortStep (var 0) (var 1) : PTm 2)
        (σ := ![sndT (RuntimePermutationWords.data m w),state m w j]) (σ' := ![m,state m w j])
        (fun k => by fin_cases k; exact snd_pair _ _; exact .eqRefl _))
  exact h.eqTrans e

theorem inactive_congr {m m' w w' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hw : Γ ⊢[PRAAx] w ≐ w') :
    Γ ⊢[PRAAx] inactive m w ≐ inactive m' w' := by
  ipra_congr (inactive (var 0) (var 1) : PTm 2) with [hm, hw]
theorem inversions_congr {m m' w w' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hw : Γ ⊢[PRAAx] w ≐ w') :
    Γ ⊢[PRAAx] RuntimePermutationWords.inversions m w ≐ RuntimePermutationWords.inversions m' w' := by
  ipra_congr (RuntimePermutationWords.inversions (var 0) (var 1) : PTm 2) with [hm, hw]
theorem checker_congr {m m' w w' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hw : Γ ⊢[PRAAx] w ≐ w') :
    Γ ⊢[PRAAx] RuntimePermutationWords.permutationBit m w ≐ RuntimePermutationWords.permutationBit m' w' := by
  simpa [RuntimePermutationWords.permutationBit] using congrAp2 RuntimePermutationWords.checkerF hm hw

theorem step_rank (m w j R : PTm n)
    (h : Γ ⊢[PRAAx] (inactive m w ≐ one) ⋎ le (RuntimePermutationWords.inversions m w+j) R) :
    Γ ⊢[PRAAx] (inactive m (sortStep m w) ≐ one) ⋎ le (RuntimePermutationWords.inversions m (sortStep m w)+succ j) R := by
  refine .orE (active_cases m w) ?_ ?_
  · have hi := inactive_of_active_zero m w (Prf.hyp0 (Γ := Γ))
    exact .orI₁ ((inactive_congr (.eqRefl _) (step_inactive m w hi)).eqTrans hi)
  · refine .orE h.wk ?_ ?_
    · exact BoundedReflection.one_ne_zero _
        ((Prf.hyp1 : (inactive m w ≐ one) :: (active m w ≐ one) :: Γ ⊢[PRAAx] active m w ≐ one).eqSymm.eqTrans
          (active_zero_of_inactive _ _ Prf.hyp0))
    · have drop : le (RuntimePermutationWords.inversions m w+j) R :: (active m w ≐ one) :: Γ ⊢[PRAAx]
          RuntimePermutationWords.inversions m (sortStep m w)+one ≐ RuntimePermutationWords.inversions m w :=
        active_inversion_drop m w Prf.hyp1
      have e := natEq drop
      ipra_simps
      exact .orI₂ (by ipra_le sl Prf.hyp0 with e)

def stateInvariant (m w j : PTm n) : Fm PTm n :=
  lt (state m w j) (RuntimePermutationWords.horizon m) ⋏
    ((inactive m (state m w j) ≐ one) ⋎ le (RuntimePermutationWords.inversions m (state m w j)+j) (RuntimePermutationWords.inversions m w))
ipra_subst stateInvariant
theorem invariant_zero (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] stateInvariant m w zero :=
  .andI (lt_congr (state_zero _ _).eqSymm (.eqRefl _) hw)
    (.orI₂ (le_congr ((congrAdd (inversions_congr (.eqRefl m) (state_zero m w)) (.eqRefl zero)).eqTrans (add_zero _)).eqSymm (.eqRefl _) (le_refl _)))
theorem invariant_succ (m w j : PTm n) (h : Γ ⊢[PRAAx] stateInvariant m w j) :
    Γ ⊢[PRAAx] stateInvariant m w (succ j) := by
  refine .andI (lt_congr (state_succ _ _ _).eqSymm (.eqRefl _) (step_bound _ _ (.andE₁ h))) ?_
  have hr := step_rank m (state m w j) j (RuntimePermutationWords.inversions m w) (.andE₂ h)
  have ih : Γ ⊢[PRAAx] inactive m (sortStep m (state m w j)) ≐ inactive m (state m w (succ j)) :=
    inactive_congr (.eqRefl m) (state_succ m w j).eqSymm
  have ir : Γ ⊢[PRAAx] RuntimePermutationWords.inversions m (sortStep m (state m w j)) ≐ RuntimePermutationWords.inversions m (state m w (succ j)) :=
    inversions_congr (.eqRefl m) (state_succ m w j).eqSymm
  exact .orE hr (.orI₁ (ih.wk.eqSymm.eqTrans Prf.hyp0))
    (.orI₂ (le_congr (congrAdd ir.wk (.eqRefl _)) (.eqRefl _) Prf.hyp0))
theorem state_invariant (m w j : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] stateInvariant m w j := by
  have all : Γ ⊢[PRAAx] .all (stateInvariant (Syn.shift m) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ ⟨lt_QF _ _,⟨trivial,le_QF _ _⟩⟩ ?_ ?_
    · simpa only [subst_stateInvariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using invariant_zero m w hw
    · simpa only [subst_stateInvariant,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        invariant_succ (Syn.shift m) (Syn.shift w) (var 0) Prf.hyp0
  simpa only [subst_stateInvariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
theorem state_bound (m w j : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] lt (state m w j) (RuntimePermutationWords.horizon m) := .andE₁ (state_invariant _ _ _ hw)
theorem final_inactive (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] inactive m (final m w) ≐ one := by
  refine .orE (.andE₂ (state_invariant m w (fuel m) hw)) Prf.hyp0 ?_
  have hi := inversion_bound (Γ := le (RuntimePermutationWords.inversions m (final m w)+fuel m) (RuntimePermutationWords.inversions m w) :: Γ) m w
  have bad : le (RuntimePermutationWords.inversions m (final m w)+fuel m) (RuntimePermutationWords.inversions m w) :: Γ ⊢[PRAAx] le (succ (m*m)) (m*m) := by
    unfold fuel at *
    ipra_le sl Prf.hyp0 + sl hi + 𝔟 (RuntimePermutationWords.inversions m (final m w))
  exact lt_irrefl _ _ bad

theorem swap_checker_preserved (m w i : PTm n)
    (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) (hi : Γ ⊢[PRAAx] lt (succ i) m) :
    Γ ⊢[PRAAx] RuntimePermutationWords.permutationBit m (RuntimeAdjacentPermutationSwap.swapWord m w i) ≐ RuntimePermutationWords.permutationBit m w := by
  refine .orE (RuntimePermutationWords.checker_cases m w) ?_ ?_
  · refine .orE (RuntimePermutationWords.checker_cases m (RuntimeAdjacentPermutationSwap.swapWord m w i)) ?_ ?_
    · exact Prf.hyp0.eqTrans Prf.hyp1.eqSymm
    · let Δ := (RuntimePermutationWords.permutationBit m (RuntimeAdjacentPermutationSwap.swapWord m w i) ≐ one) ::
        (RuntimePermutationWords.permutationBit m w ≐ zero) :: Γ
      have hp : Δ ⊢[PRAAx] RuntimePermutationWords.permutation m
          (RuntimeAdjacentPermutationSwap.swapWord m (RuntimeAdjacentPermutationSwap.swapWord m w i) i) :=
        RuntimeAdjacentPermutationSwap.swapped_permutation m (RuntimeAdjacentPermutationSwap.swapWord m w i) i
          ((RuntimePermutationWords.checker_reflection _ _).iffMp Prf.hyp0) hi.wk.wk
      have inv : Δ ⊢[PRAAx] RuntimeAdjacentPermutationSwap.swapWord m (RuntimeAdjacentPermutationSwap.swapWord m w i) i ≐ w :=
        RuntimeAdjacentPermutationSwap.word_involution m w i hw.wk.wk hi.wk.wk
      have he : Δ ⊢[PRAAx] RuntimePermutationWords.permutationBit m
          (RuntimeAdjacentPermutationSwap.swapWord m (RuntimeAdjacentPermutationSwap.swapWord m w i) i) ≐ RuntimePermutationWords.permutationBit m w :=
        checker_congr (.eqRefl m) inv
      have ho : Δ ⊢[PRAAx] RuntimePermutationWords.permutationBit m
          (RuntimeAdjacentPermutationSwap.swapWord m (RuntimeAdjacentPermutationSwap.swapWord m w i) i) ≐ one :=
        (RuntimePermutationWords.checker_reflection _ _).iffMpr hp
      exact BoundedReflection.one_ne_zero _ (ho.eqSymm.eqTrans (he.eqTrans Prf.hyp1))
  · have hp := RuntimeAdjacentPermutationSwap.swapped_permutation m w i
      ((RuntimePermutationWords.checker_reflection _ _).iffMp Prf.hyp0) hi.wk
    exact ((RuntimePermutationWords.checker_reflection _ _).iffMpr hp).eqTrans Prf.hyp0.eqSymm
theorem step_checker_preserved (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] RuntimePermutationWords.permutationBit m (sortStep m w) ≐ RuntimePermutationWords.permutationBit m w := by
  refine .orE (active_cases m w) ?_ ?_
  · exact checker_congr (.eqRefl _) (step_inactive _ _ (inactive_of_active_zero _ _ Prf.hyp0))
  · exact (checker_congr (.eqRefl _) (step_active _ _ Prf.hyp0)).eqTrans
      (swap_checker_preserved _ _ _ hw.wk (.andE₁ (descent_found _ _ Prf.hyp0)))
theorem checker_preserved (m w j : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] RuntimePermutationWords.permutationBit m (state m w j) ≐ RuntimePermutationWords.permutationBit m w := by
  have all : Γ ⊢[PRAAx] .all (RuntimePermutationWords.permutationBit (Syn.shift m) (state (Syn.shift m) (Syn.shift w) (var 0)) ≐
      RuntimePermutationWords.permutationBit (Syn.shift m) (Syn.shift w)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [Fm.subst_eq,RuntimePermutationWords.subst_permutationBit,subst_state,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        checker_congr (.eqRefl m) (state_zero m w)
    · simp only [Fm.subst_eq,RuntimePermutationWords.subst_permutationBit,subst_state,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      have hs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift w) (RuntimePermutationWords.horizon (Syn.shift m)) := by
        simpa only [Fm.shift,subst_lt,RuntimePermutationWords.subst_horizon,Syn.shift] using hw.shift
      exact (checker_congr (.eqRefl _) (state_succ _ _ _)).eqTrans
        ((step_checker_preserved _ _ (state_bound _ _ _ hs.wk)).eqTrans Prf.hyp0)
  simpa only [Fm.subst_eq,RuntimePermutationWords.subst_permutationBit,subst_state,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def sorted (m w : PTm n) : Fm PTm n := .all
  (lt (succ (var 0)) (Syn.shift m) ⟶ le (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (var 0))
    (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (succ (var 0))))
def strictSorted (m w : PTm n) : Fm PTm n := .all
  (lt (succ (var 0)) (Syn.shift m) ⟶ lt (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (var 0))
    (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (succ (var 0))))
ipra_subst sorted [Syn.subst_shift, Syn.shift_subst]
ipra_subst strictSorted [Syn.subst_shift, Syn.shift_subst]
theorem sorted_at (m w i : PTm n) (h : Γ ⊢[PRAAx] sorted m w) (hi : Γ ⊢[PRAAx] lt (succ i) m) :
    Γ ⊢[PRAAx] le (RuntimePermutationWords.digit m w i) (RuntimePermutationWords.digit m w (succ i)) := by
  have hh := h.allE i
  simp only [sorted,Fm.subst_imp,subst_lt,subst_le,ConciseIPRA.PTm.subst_succ,RuntimePermutationWords.subst_digit,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at hh
  exact .impE hh hi
theorem strict_at (m w i : PTm n) (h : Γ ⊢[PRAAx] strictSorted m w) (hi : Γ ⊢[PRAAx] lt (succ i) m) :
    Γ ⊢[PRAAx] lt (RuntimePermutationWords.digit m w i) (RuntimePermutationWords.digit m w (succ i)) := by
  have hh := h.allE i
  simp only [strictSorted,Fm.subst_imp,subst_lt,ConciseIPRA.PTm.subst_succ,RuntimePermutationWords.subst_digit,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at hh
  exact .impE hh hi
theorem final_sorted (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] sorted m (final m w) := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] inactive (Syn.shift m) (final (Syn.shift m) (Syn.shift w)) ≐ one := by
    simpa only [Fm.shift,Fm.subst_eq,subst_inactive,subst_final,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using (final_inactive m w hw).shift
  simpa only [Syn.shift,subst_final] using descent_none (Syn.shift m) (final (Syn.shift m) (Syn.shift w)) (var 0) hs.wk Prf.hyp0

/-! Strict adjacent increase is converted to literal identity digits by
numeric prefix and tail bounds, not a fixed external finite order. -/
theorem strict_gap (m w i d : PTm n) (h : Γ ⊢[PRAAx] strictSorted m w)
    (hi : Γ ⊢[PRAAx] lt (i+d) m) :
    Γ ⊢[PRAAx] le (RuntimePermutationWords.digit m w i+d) (RuntimePermutationWords.digit m w (i+d)) := by
  have all : Γ ⊢[PRAAx] .all (lt (Syn.shift i+var 0) (Syn.shift m) ⟶
      le (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (Syn.shift i)+var 0)
        (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (Syn.shift i+var 0))) := by
    refine PRA.qfInd _ ⟨lt_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp,subst_lt,subst_le,PTm.subst_add,RuntimePermutationWords.subst_digit,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI ?_
      exact le_congr (add_zero _).eqSymm (RuntimeAdjacentPermutationSwap.digit_congr (.eqRefl _) (.eqRefl _) (add_zero i)).eqSymm (le_refl _)
    · simp only [Fm.subst_imp,subst_lt,subst_le,PTm.subst_add,RuntimePermutationWords.subst_digit,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := lt (Syn.shift i+succ (var 0)) (Syn.shift m) ::
        (lt (Syn.shift i+var 0) (Syn.shift m) ⟶
          le (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (Syn.shift i)+var 0)
            (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (Syn.shift i+var 0))) :: Γ.map Fm.shift
      have hr : Δ ⊢[PRAAx] lt (Syn.shift i+var 0) (Syn.shift m) :=
        lt_of_le_of_lt (le_succ_self _) (lt_congr (add_succ _ _) (.eqRefl _) Prf.hyp0)
      have ih : Δ ⊢[PRAAx] le (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (Syn.shift i)+var 0)
          (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (Syn.shift i+var 0)) := .impE Prf.hyp1 hr
      have hs : Γ.map Fm.shift ⊢[PRAAx] strictSorted (Syn.shift m) (Syn.shift w) := by
        simpa only [Fm.shift,subst_strictSorted,Syn.shift] using h.shift
      have hn : Δ ⊢[PRAAx] lt (succ (Syn.shift i+var 0)) (Syn.shift m) :=
        lt_congr (add_succ _ _) (.eqRefl _) Prf.hyp0
      have hv := strict_at (Syn.shift m) (Syn.shift w) (Syn.shift i+var 0) hs.wk.wk hn
      have he : Δ ⊢[PRAAx] RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (Syn.shift i+succ (var 0)) ≐
          RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (succ (Syn.shift i+var 0)) :=
        RuntimeAdjacentPermutationSwap.digit_congr (.eqRefl (Syn.shift m)) (.eqRefl (Syn.shift w)) (add_succ (Syn.shift i) (var 0))
      exact le_congr (.eqRefl _) he.eqSymm (by ipra_le sl ih + sl hv)
  have hh := all.allE d
  simp only [Fm.subst_imp,subst_lt,subst_le,PTm.subst_add,RuntimePermutationWords.subst_digit,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at hh
  exact .impE hh hi
theorem strict_identity_at (m w i : PTm n) (h : Γ ⊢[PRAAx] strictSorted m w)
    (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] RuntimePermutationWords.digit m w i ≐ i := by
  have hg := strict_gap m w zero i h (lt_congr (zero_add _).eqSymm (.eqRefl _) hi)
  have hn : Γ ⊢[PRAAx] le i (RuntimePermutationWords.digit m w i) := by
    have he : Γ ⊢[PRAAx] RuntimePermutationWords.digit m w (zero+i) ≐ RuntimePermutationWords.digit m w i :=
      RuntimeAdjacentPermutationSwap.digit_congr (.eqRefl m) (.eqRefl w) (zero_add i)
    exact le_trans (le_add_left i (RuntimePermutationWords.digit m w zero)) (le_congr (.eqRefl _) he hg)
  have hd : Γ ⊢[PRAAx] m ≐ succ i+monus m (succ i) := eq_add_of_le hi
  have he : Γ ⊢[PRAAx] i+monus m (succ i)+one ≐ m := by
    ipra_lc -natEq hd
  have hb : Γ ⊢[PRAAx] lt (i+monus m (succ i)) m :=
    le_congr (succ_eq_add_one _).eqSymm he (le_refl _)
  have ht := strict_gap m w i (monus m (succ i)) h hb
  have hu := RuntimePermutationWords.digit_bound m w (i+monus m (succ i)) hb
  have hl : Γ ⊢[PRAAx] le (RuntimePermutationWords.digit m w i) i := by
    have ee := natEq he
    ipra_simps
    ipra_le sl ht + sl hu with ee
  exact le_antisymm hl hn

theorem identity_code_bound (m : PTm n) : Γ ⊢[PRAAx] lt (identityCode m) (RuntimePermutationWords.horizon m) :=
  RuntimePermutationWords.encode_bound _ _ (.andE₁ (.andE₂ (RuntimePermutationWords.identity_tuple _)))
theorem identity_code_digit (m i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] RuntimePermutationWords.digit m (identityCode m) i ≐ i :=
  (RuntimePermutationWords.encode_decode _ _ _ (.andE₁ (.andE₂ (RuntimePermutationWords.identity_tuple _))) hi).eqTrans
    (RuntimePermutationWords.identity_lookup _ _ hi)
theorem identity_code_permutation (m : PTm n) : Γ ⊢[PRAAx] RuntimePermutationWords.permutation m (identityCode m) :=
  RuntimePermutationWords.encoded_tuple _ _ (RuntimePermutationWords.identity_tuple _)
theorem strict_identity_code (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m))
    (hs : Γ ⊢[PRAAx] strictSorted m w) : Γ ⊢[PRAAx] w ≐ identityCode m := by
  apply RuntimePermutationWords.word_unique m w (identityCode m) hw (identity_code_bound _)
  refine .allI (.impI ?_)
  have hh : Γ.map Fm.shift ⊢[PRAAx] strictSorted (Syn.shift m) (Syn.shift w) := by
    simpa only [Fm.shift,subst_strictSorted,Syn.shift] using hs.shift
  simpa only [Syn.shift,subst_identityCode,RuntimePermutationWords.subst_word] using
    (RuntimePermutationWords.word_lookup (Syn.shift m) (Syn.shift w) (var 0) Prf.hyp0).eqTrans
      ((strict_identity_at _ _ _ hh.wk Prf.hyp0).eqTrans
        ((identity_code_digit _ _ Prf.hyp0).eqSymm.eqTrans
          (RuntimePermutationWords.word_lookup (Syn.shift m) (identityCode (Syn.shift m)) (var 0) Prf.hyp0).eqSymm))
theorem sorted_permutation_strict (m w : PTm n) (hs : Γ ⊢[PRAAx] sorted m w)
    (hp : Γ ⊢[PRAAx] RuntimePermutationWords.permutation m w) : Γ ⊢[PRAAx] strictSorted m w := by
  refine .allI (.impI ?_)
  have ss : Γ.map Fm.shift ⊢[PRAAx] sorted (Syn.shift m) (Syn.shift w) := by
    simpa only [Fm.shift,subst_sorted,Syn.shift] using hs.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] RuntimePermutationWords.permutation (Syn.shift m) (Syn.shift w) := by
    simpa only [Fm.shift,RuntimePermutationWords.subst_permutation,Syn.shift] using hp.shift
  have hl := sorted_at (Syn.shift m) (Syn.shift w) (var 0) ss.wk Prf.hyp0
  have hd := RuntimeAdjacentPermutationSwap.adjacent_digits_different (Syn.shift m) (Syn.shift w) (var 0) ps.wk Prf.hyp0
  exact .orE (lt_or_eq_of_le hl) Prf.hyp0 (.botE _ (.impE hd.wk Prf.hyp0))
theorem permutation_final_identity (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] RuntimePermutationWords.permutationBit m w ≐ one) :
    Γ ⊢[PRAAx] final m w ≐ identityCode m :=
  strict_identity_code _ _ (state_bound _ _ _ hw) (sorted_permutation_strict _ _ (final_sorted _ _ hw)
    ((RuntimePermutationWords.checker_reflection _ _).iffMp ((checker_preserved _ _ _ hw).eqTrans hp)))

def tieSyntax (m w i : PTm n) : BFm n :=
  .and (.lt (succ i) m) (.eq (RuntimePermutationWords.digit m w i) (RuntimePermutationWords.digit m w (succ i)))
def tieF : PR 3 := BoundedSyntax.bitF (tieSyntax (var 0) (var 1) (var 2))
def tieBit (m w i : PTm n) : PTm n := app tieF ![m,w,i]
def tieBody : PTm 2 := tieBit (sndT (var 1)) (fstT (var 1)) (var 0)
def tieExists (m w : PTm n) : PTm n := BoundedReflection.exB tieBody m (RuntimePermutationWords.data m w)
def tieIndex (m w : PTm n) : PTm n := BoundedReflection.wit tieBody m (RuntimePermutationWords.data m w)
@[simp] theorem subst_tieBit {l : ℕ} (σ : Fin n → PTm l) (m w i : PTm n) :
    Syn.subst σ (tieBit m w i) = tieBit (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ i) := by
  simp only [tieBit,ConciseIPRA.PTm.subst_app]
  congr 1
  funext k
  fin_cases k <;> rfl
@[simp] theorem subst_tieExists {l : ℕ} (σ : Fin n → PTm l) (m w : PTm n) :
    Syn.subst σ (tieExists m w) = tieExists (Syn.subst σ m) (Syn.subst σ w) := by simp [tieExists]
ipra_subst tieIndex
theorem tie_at (m w i : PTm n) : Γ ⊢[PRAAx] tieBit m w i ≐
    BoundedSyntax.bit (tieSyntax (var 0) (var 1) (var 2)) ![m,w,i] := BoundedSyntax.program_correct _ _
theorem tie_reflection (m w i : PTm n) : Γ ⊢[PRAAx] Fm.iff (tieBit m w i ≐ one)
    (lt (succ i) m ⋏ RuntimePermutationWords.digit m w i ≐ RuntimePermutationWords.digit m w (succ i)) := by
  have r : Γ ⊢[PRAAx] Fm.iff
      (BoundedSyntax.bit (tieSyntax (var 0) (var 1) (var 2)) ![m,w,i] ≐ one)
      (lt (succ i) m ⋏ RuntimePermutationWords.digit m w i ≐ RuntimePermutationWords.digit m w (succ i)) := by
    simpa [tieSyntax,formula,BFm.lt,BFm.le,lt,le] using
      BoundedSyntax.bounded_reflection (tieSyntax (var 0) (var 1) (var 2)) ![m,w,i]
  exact .iffI (.impI (r.wk.iffMp ((tie_at _ _ _).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((tie_at _ _ _).eqTrans (r.wk.iffMpr Prf.hyp0)))
theorem tie_cases (m w i : PTm n) : Γ ⊢[PRAAx] (tieBit m w i ≐ zero) ⋎ (tieBit m w i ≐ one) :=
  .orE (BoundedSyntax.bit_cases (tieSyntax (var 0) (var 1) (var 2)) ![m,w,i])
    (.orI₁ ((tie_at _ _ _).eqTrans Prf.hyp0)) (.orI₂ ((tie_at _ _ _).eqTrans Prf.hyp0))
theorem tie_body_at (m w i : PTm n) : Γ ⊢[PRAAx] inst2 tieBody i (RuntimePermutationWords.data m w) ≐ tieBit m w i := by
  simp only [tieBody,inst2,subst_tieBit,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,RuntimePermutationWords.data]
  ipra_congr (tieBit (var 0) (var 1) (var 2) : PTm 3) with [snd_pair _ _, fst_pair _ _, .eqRefl i]
theorem tie_exists_cases (m w : PTm n) : Γ ⊢[PRAAx] (tieExists m w ≐ zero) ⋎ (tieExists m w ≐ one) :=
  BoundedReflection.ex_cases _ _ _
theorem tie_found (m w : PTm n) (h : Γ ⊢[PRAAx] tieExists m w ≐ one) : Γ ⊢[PRAAx]
    lt (succ (tieIndex m w)) m ⋏ RuntimePermutationWords.digit m w (tieIndex m w) ≐ RuntimePermutationWords.digit m w (succ (tieIndex m w)) := by
  have hn : Γ ⊢[PRAAx] neg (tieBit m w (tieIndex m w) ≐ zero) :=
    .impI (.impE (Prf.andE₂ (BoundedReflection.ex_elim tieBody h)).wk ((tie_body_at _ _ _).eqTrans Prf.hyp0))
  refine .orE (tie_cases m w (tieIndex m w)) (.botE _ (.impE hn.wk Prf.hyp0)) ?_
  exact (tie_reflection _ _ _).iffMp Prf.hyp0
theorem tie_least (m w i : PTm n) (hi : Γ ⊢[PRAAx] lt i (tieIndex m w)) :
    Γ ⊢[PRAAx] tieBit m w i ≐ zero := (tie_body_at _ _ _).eqSymm.eqTrans (BoundedReflection.ex_least tieBody hi)
theorem sorted_strict_of_no_tie (m w : PTm n) (hs : Γ ⊢[PRAAx] sorted m w)
    (hz : Γ ⊢[PRAAx] tieExists m w ≐ zero) : Γ ⊢[PRAAx] strictSorted m w := by
  refine .allI (.impI ?_)
  have ss : Γ.map Fm.shift ⊢[PRAAx] sorted (Syn.shift m) (Syn.shift w) := by
    simpa only [Fm.shift,subst_sorted,Syn.shift] using hs.shift
  have zs : Γ.map Fm.shift ⊢[PRAAx] tieExists (Syn.shift m) (Syn.shift w) ≐ zero := by
    simpa only [Fm.shift,Fm.subst_eq,subst_tieExists,ConciseIPRA.PTm.subst_zero,Syn.shift] using hz.shift
  have hl := sorted_at (Syn.shift m) (Syn.shift w) (var 0) ss.wk Prf.hyp0
  have ht : lt (succ (var 0)) (Syn.shift m) :: Γ.map Fm.shift ⊢[PRAAx] tieBit (Syn.shift m) (Syn.shift w) (var 0) ≐ zero :=
    (tie_body_at _ _ _).eqSymm.eqTrans (BoundedReflection.ex_none tieBody zs.wk (lt_of_le_of_lt (le_succ_self _) Prf.hyp0))
  refine .orE (lt_or_eq_of_le hl) Prf.hyp0 ?_
  have ho : (RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (var 0) ≐ RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (succ (var 0))) ::
      lt (succ (var 0)) (Syn.shift m) :: Γ.map Fm.shift ⊢[PRAAx] tieBit (Syn.shift m) (Syn.shift w) (var 0) ≐ one :=
    (tie_reflection (Syn.shift m) (Syn.shift w) (var 0)).iffMpr (.andI Prf.hyp1 Prf.hyp0)
  exact BoundedReflection.one_ne_zero _ (ho.eqSymm.eqTrans ht.wk)
theorem nonpermutation_final_tie (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] RuntimePermutationWords.permutationBit m w ≐ zero) : Γ ⊢[PRAAx]
    lt (succ (tieIndex m (final m w))) m ⋏
      RuntimePermutationWords.digit m (final m w) (tieIndex m (final m w)) ≐
        RuntimePermutationWords.digit m (final m w) (succ (tieIndex m (final m w))) := by
  apply tie_found
  refine .orE (tie_exists_cases m (final m w)) ?_ Prf.hyp0
  have hs := sorted_strict_of_no_tie m (final m w) (final_sorted _ _ hw.wk) Prf.hyp0
  have he := strict_identity_code m (final m w) (state_bound _ _ _ hw.wk) hs
  have hc := checker_congr (.eqRefl m) he
  have ho : (tieExists m (final m w) ≐ zero) :: Γ ⊢[PRAAx] RuntimePermutationWords.permutationBit m (identityCode m) ≐ one :=
    (RuntimePermutationWords.checker_reflection m (identityCode m)).iffMpr (identity_code_permutation m)
  exact BoundedReflection.one_ne_zero _
    (ho.eqSymm.eqTrans (hc.eqSymm.eqTrans ((checker_preserved _ _ _ hw.wk).eqTrans hp.wk)))

theorem sortStep_congr {m m' w w' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hw : Γ ⊢[PRAAx] w ≐ w') :
    Γ ⊢[PRAAx] sortStep m w ≐ sortStep m' w' := by
  ipra_congr (sortStep (var 0) (var 1) : PTm 2) with [hm, hw]
theorem state_from_inactive (m w j : PTm n) (h : Γ ⊢[PRAAx] inactive m w ≐ one) :
    Γ ⊢[PRAAx] state m w j ≐ w := by
  have all : Γ ⊢[PRAAx] .all (state (Syn.shift m) (Syn.shift w) (var 0) ≐ Syn.shift w) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [Fm.subst_eq,subst_state,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using state_zero m w
    · simp only [Fm.subst_eq,subst_state,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      have hs : Γ.map Fm.shift ⊢[PRAAx] inactive (Syn.shift m) (Syn.shift w) ≐ one := by
        simpa only [Fm.shift,Fm.subst_eq,subst_inactive,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using h.shift
      exact (state_succ _ _ _).eqTrans ((sortStep_congr (.eqRefl _) Prf.hyp0).eqTrans (step_inactive _ _ hs.wk))
  simpa only [Fm.subst_eq,subst_state,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
theorem inactive_small (m w : PTm n) (hm : Γ ⊢[PRAAx] le m one) : Γ ⊢[PRAAx] inactive m w ≐ one := by
  refine .orE (active_cases m w) (inactive_of_active_zero _ _ Prf.hyp0) ?_
  have hi := Prf.andE₁ (descent_found m w (Prf.hyp0 (Γ := Γ)))
  have bad : (active m w ≐ one) :: Γ ⊢[PRAAx] le (succ one) one := by
    ipra_le sl hi + sl hm.wk + 𝔟 (descentIndex m w)
  exact lt_irrefl one _ bad
theorem final_zero_dimension (w : PTm n) : Γ ⊢[PRAAx] final zero w ≐ w :=
  state_from_inactive _ _ _ (inactive_small _ _ (zero_le _))
theorem final_one_dimension (w : PTm n) : Γ ⊢[PRAAx] final one w ≐ w :=
  state_from_inactive _ _ _ (inactive_small _ _ (le_refl _))

def adjacentTie (m w i : PTm n) : Fm PTm n := lt (succ i) m ⋏
  RuntimePermutationWords.digit m w i ≐ RuntimePermutationWords.digit m w (succ i)
ipra_subst adjacentTie
theorem adjacent_tie_congr {m m' w w' i i' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m')
    (hw : Γ ⊢[PRAAx] w ≐ w') (hi : Γ ⊢[PRAAx] i ≐ i') (h : Γ ⊢[PRAAx] adjacentTie m w i) :
    Γ ⊢[PRAAx] adjacentTie m' w' i' := by
  have hh : Γ ⊢[PRAAx] (adjacentTie (var 0) (var 1) (var 2) : Fm PTm 3).subst ![m,w,i] := by
    simpa only [subst_adjacentTie,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h
  simpa only [subst_adjacentTie,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using Prf.eqSubst (adjacentTie (var 0) (var 1) (var 2) : Fm PTm 3)
    ![m,w,i] ![m',w',i'] (fun k => by fin_cases k; exact hm; exact hw; exact hi) hh

def certificate (m w : PTm n) : Fm PTm n :=
  lt (final m w) (RuntimePermutationWords.horizon m) ⋏ (sorted m (final m w) ⋏
    (RuntimePermutationWords.permutationBit m (final m w) ≐ RuntimePermutationWords.permutationBit m w ⋏
      ((RuntimePermutationWords.permutationBit m w ≐ one ⟶ final m w ≐ identityCode m) ⋏
        (RuntimePermutationWords.permutationBit m w ≐ zero ⟶ adjacentTie m (final m w) (tieIndex m (final m w))))))
ipra_subst certificate
theorem sorting_correct (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] certificate m w :=
  .andI (state_bound _ _ _ hw) (.andI (final_sorted _ _ hw) (.andI (checker_preserved _ _ _ hw)
    (.andI (.impI (permutation_final_identity _ _ hw.wk Prf.hyp0))
      (.impI (nonpermutation_final_tie _ _ hw.wk Prf.hyp0)))))

/-! The actual PR2 output retains the final word, both checker bits,
inversion count, actual least tie index and the numerical fuel. -/
def output (m w : PTm n) : PTm n := pairT (final m w)
  (pairT (RuntimePermutationWords.word m (final m w))
    (pairT (RuntimePermutationWords.permutationBit m w)
      (pairT (RuntimePermutationWords.permutationBit m (final m w))
        (pairT (RuntimePermutationWords.inversions m (final m w)) (pairT (tieIndex m (final m w)) (fuel m))))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (m w : PTm n) : PTm n := ap2 outputF m w
ipra_subst output
ipra_subst run
theorem program_at (m w : PTm n) : Γ ⊢[PRAAx] run m w ≐ output m w := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1)) ![m,w]



theorem returned_final (m w : PTm n) : Γ ⊢[PRAAx] fstT (run m w) ≐ final m w :=
  (congrFst (program_at m w)).eqTrans (fst_pair _ _)
theorem returned_word (m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run m w)) ≐ RuntimePermutationWords.word m (final m w) :=
  (congrFst ((congrSnd (program_at m w)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_original_checker (m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run m w))) ≐ RuntimePermutationWords.permutationBit m w :=
  (congrFst ((congrSnd ((congrSnd (program_at m w)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_final_checker (m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run m w)))) ≐ RuntimePermutationWords.permutationBit m (final m w) :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at m w)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_inversions (m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run m w))))) ≐ RuntimePermutationWords.inversions m (final m w) :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at m w)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_tie_index (m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (sndT (run m w)))))) ≐ tieIndex m (final m w) :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at m w)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_fuel (m w : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (sndT (run m w)))))) ≐ fuel m :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at m w)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_bound (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] lt (fstT (run m w)) (RuntimePermutationWords.horizon m) :=
  lt_congr (returned_final _ _).eqSymm (.eqRefl _) (state_bound _ _ _ hw)
theorem returned_sorted (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) :
    Γ ⊢[PRAAx] sorted m (fstT (run m w)) := by
  have hs : Γ ⊢[PRAAx] (sorted (var 0) (var 1) : Fm PTm 2).subst ![m,final m w] := by
    simpa only [subst_sorted,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using final_sorted m w hw
  simpa only [subst_sorted,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqSubst (sorted (var 0) (var 1) : Fm PTm 2) ![m,final m w] ![m,fstT (run m w)]
      (fun k => by fin_cases k; exact .eqRefl _; exact (returned_final m w).eqSymm) hs
theorem returned_checkers_equal (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m)) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run m w)))) ≐ fstT (sndT (sndT (run m w))) :=
  (returned_final_checker _ _).eqTrans ((checker_preserved _ _ _ hw).eqTrans (returned_original_checker _ _).eqSymm)
theorem returned_identity (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] fstT (sndT (sndT (run m w))) ≐ one) :
    Γ ⊢[PRAAx] fstT (run m w) ≐ identityCode m :=
  (returned_final _ _).eqTrans (permutation_final_identity _ _ hw ((returned_original_checker _ _).eqSymm.eqTrans hp))
theorem returned_tie (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] fstT (sndT (sndT (run m w))) ≐ zero) : Γ ⊢[PRAAx]
    adjacentTie m (fstT (run m w)) (fstT (sndT (sndT (sndT (sndT (sndT (run m w))))))) :=
  adjacent_tie_congr (.eqRefl _) (returned_final _ _).eqSymm (returned_tie_index _ _).eqSymm
    (nonpermutation_final_tie _ _ hw ((returned_original_checker _ _).eqSymm.eqTrans hp))

/-! Ordinary closed PRA statements retain all dimensions, words, steps and
search outputs as numerical variables. -/
theorem inversion_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (RuntimePermutationWords.inversions (var 0) (var 1)) (var 0*var 0)) := closeUniv 2 (inversion_bound _ _)
theorem least_descent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (active (var 0) (var 1) ≐ one ⟶
      (lt (succ (descentIndex (var 0) (var 1))) (var 0) ⋏
        lt (RuntimePermutationWords.digit (var 0) (var 1) (succ (descentIndex (var 0) (var 1))))
          (RuntimePermutationWords.digit (var 0) (var 1) (descentIndex (var 0) (var 1))))) :=
  closeUniv 2 (.impI (descent_found _ _ Prf.hyp0))
theorem active_rank_drop_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (active (var 0) (var 1) ≐ one ⟶
      RuntimePermutationWords.inversions (var 0) (sortStep (var 0) (var 1))+one ≐ RuntimePermutationWords.inversions (var 0) (var 1)) :=
  closeUniv 2 (.impI (active_inversion_drop _ _ Prf.hyp0))
theorem clock_invariant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (RuntimePermutationWords.horizon (var 0)) ⟶ stateInvariant (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (state_invariant _ _ _ Prf.hyp0))
theorem checker_preserved_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (RuntimePermutationWords.horizon (var 0)) ⟶
      RuntimePermutationWords.permutationBit (var 0) (state (var 0) (var 1) (var 2)) ≐ RuntimePermutationWords.permutationBit (var 0) (var 1)) :=
  closeUniv 3 (.impI (checker_preserved _ _ _ Prf.hyp0))
theorem actual_sorting_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (RuntimePermutationWords.horizon (var 0)) ⟶ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (sorting_correct _ _ Prf.hyp0))
theorem permutation_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (RuntimePermutationWords.horizon (var 0)) ⟶ RuntimePermutationWords.permutationBit (var 0) (var 1) ≐ one ⟶
      final (var 0) (var 1) ≐ identityCode (var 0)) :=
  closeUniv 2 (.impI (.impI (permutation_final_identity _ _ Prf.hyp1 Prf.hyp0)))
theorem nonpermutation_tie_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (RuntimePermutationWords.horizon (var 0)) ⟶ RuntimePermutationWords.permutationBit (var 0) (var 1) ≐ zero ⟶
      adjacentTie (var 0) (final (var 0) (var 1)) (tieIndex (var 0) (final (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.impI (nonpermutation_final_tie _ _ Prf.hyp1 Prf.hyp0)))
theorem empty_singleton_sorting_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((final zero (var 0) ≐ var 0) ⋏ (final one (var 0) ≐ var 0)) :=
  closeUniv 1 (.andI (final_zero_dimension _) (final_one_dimension _))
theorem sorting_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem returned_sorting_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (RuntimePermutationWords.horizon (var 0)) ⟶
      (lt (fstT (run (var 0) (var 1))) (RuntimePermutationWords.horizon (var 0)) ⋏
        (sorted (var 0) (fstT (run (var 0) (var 1))) ⋏
          fstT (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ fstT (sndT (sndT (run (var 0) (var 1))))))) :=
  closeUniv 2 (.impI (.andI (returned_bound _ _ Prf.hyp0)
    (.andI (returned_sorted _ _ Prf.hyp0) (returned_checkers_equal _ _ Prf.hyp0))))
theorem returned_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (RuntimePermutationWords.horizon (var 0)) ⟶ fstT (sndT (sndT (run (var 0) (var 1)))) ≐ one ⟶
      fstT (run (var 0) (var 1)) ≐ identityCode (var 0)) :=
  closeUniv 2 (.impI (.impI (returned_identity _ _ Prf.hyp1 Prf.hyp0)))
theorem returned_tie_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (RuntimePermutationWords.horizon (var 0)) ⟶ fstT (sndT (sndT (run (var 0) (var 1)))) ≐ zero ⟶
      adjacentTie (var 0) (fstT (run (var 0) (var 1)))
        (fstT (sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1))))))))) :=
  closeUniv 2 (.impI (.impI (returned_tie _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.RuntimeWordSorting
