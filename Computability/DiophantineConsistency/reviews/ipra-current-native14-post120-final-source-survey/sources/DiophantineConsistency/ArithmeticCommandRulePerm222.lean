import DiophantineConsistency.ArithmeticCommandLeafPerm222

/-! Actual all-internal GEN/MP blocks of the permuted C222 machine.
GEN uses J(i), including the empty zero branch. MP cleanup retains old
counter B. The two false-cache branches halt; arbitrary saved stacks remain
part of the contract. No proof-code/compiler/history or row10 is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticCommandRulePerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticTemplates254
open ArithmeticCommandStepPerm222 ArithmeticCommandAppendPerm222
open ArithmeticCommandRunPerm222 ArithmeticCommandCompositionPerm222
open ArithmeticCommandBlockPerm222 ArithmeticCommandLeafPerm222
attribute [local irreducible] Code254.P
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def genTail (i : V) : V :=
  dropWord (appendValue (Jword i) (nipWord
    (axWord i 0 0 (appendValue (nipsWord 9) terminatorWord))))
noncomputable def genBlockWord (i p : V) : V := appendValue p (genTail i)
noncomputable def mpTail (B : V) : V :=
  nipWord (dropWord (nipWord (mpWord B
    (axWord B 0 0 (appendValue (nipsWord 10) terminatorWord)))))
noncomputable def mpBlockWord (B pa pab : V) : V :=
  appendValue pa (dropWord (appendValue pab (mpTail B)))

/-- The physical rho6 slot is (i,i), and the old counter is i. -/
noncomputable def genPrefix (i H : V) : List V :=
  [rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i,
    rho6 i i, ArithmeticTemplates222.growG i H i, rho8 i H i i]

theorem genPrefix_ne_one (i H : V) : ∀ x, x∈genPrefix i H → x≠1 := by
  intro x hx
  apply axList_ne_one i H H i i x
  change x∈genPrefix i H ++ [wal i H]
  exact List.mem_append_left _ hx

theorem gen_cleanup (i H S : V) :
    evalValue (appendValue (nipsWord 9) terminatorWord)
      (stateValue 0 (axStackValue i H H i i 0 S) 0 0)=someState (wal i H) S 0 0 := by
  have he := select_entry (genPrefix i H) (wal i H) [] 0 0 0 S
    (by simp) (by simp) (wal_ne_one i H) (genPrefix_ne_one i H) (by simp)
  have hstack : axStackValue i H H i i 0 S =
      pushL (genPrefix i H ++ wal i H :: ([] ++ [0])) S := rfl
  rw [hstack]
  simpa only [genPrefix,List.length_cons,List.length_nil,Nat.reduceAdd,
    nipsWord,terminatorWord] using he

/-- H=1 is loaded from cache0 then consumed by AX, never tested by NIP.
No positivity assumption is made on i; J(0) is the empty word. -/
theorem eval_genTail (i H S : V) :
    evalValue (genTail i) (stateValue H S 0 0)=someState (wal i H) S 0 0 := by
  rw [genTail,eval_drop,eval_J,eval_nip]
  simp only [zero_ne_one,if_false,first_cantor,second_cantor]
  rw [eval_ax]
  simp only [add_zero,gate_self]
  exact gen_cleanup i H S

/-- Cleanup AX has actual old counter B, and the saved top is also B. -/
theorem mp_cleanup (B S : V) :
    evalValue (appendValue (nipsWord 10) terminatorWord)
      (stateValue 0 (axStackValue B 0 0 B B B (cantor 0 S)) 0 0)=
        if B=1 then 0 else someState B S 0 0 := by
  rw [axStack_eq]
  have hn := eval_nips_cont 0 (cantor 0 S) 0 (axList B 0 0 B B) 0 B terminatorWord
    (by simp) (axList_ne_one B 0 0 B B)
  have hlen : (axList B 0 0 B B).length+1=10 := rfl
  rw [hlen] at hn
  rw [hn,terminatorWord,eval_drop,eval_nip]
  by_cases hb : B=1
  · simp [hb]
  · simp only [hb,if_false,first_cantor,second_cantor]
    rw [eval_nip]
    simp [someState]

/-- Exact MP suffix; A=1 and B=1 are actual machine halt branches. -/
theorem eval_mpTail (A B S : V) :
    evalValue (mpTail B) (stateValue (wim A B) (cantor A S) 0 0)=
      if A=1 ∨ B=1 then 0 else someState B S 0 0 := by
  rw [mpTail,eval_nip]
  simp only [zero_ne_one,if_false,first_cantor,second_cantor]
  rw [eval_drop,eval_nip]
  by_cases ha : A=1
  · simp [ha]
  · simp only [ha,if_false,first_cantor,second_cantor]
    rw [eval_mp]
    simp only [zero_add]
    rw [eval_ax]
    simp only [add_zero,gate_self,mp_cleanup]
    simp

theorem gen_contract (i : V) {p H : V} (hp : Contract p H) :
    Contract (genBlockWord i p) (wal i H) := by
  intro top S
  rcases hp top S with hh | hs
  · left
    exact eval_append_halt p (genTail i) (stateValue top S 0 0) hh
  · right
    rw [genBlockWord,eval_append_success _ _ _ _ hs,eval_genTail]

/-- The major is applied at top0 and precisely P(A,S); its arbitrary
saved-stack quantifier cannot be replaced by a zero-stack hypothesis. -/
theorem mp_contract {A B pa pab : V}
    (ha : Contract pa A) (hab : Contract pab (wim A B)) :
    Contract (mpBlockWord B pa pab) B := by
  intro top S
  rcases ha top S with hh | hs
  · left
    exact eval_append_halt pa _ (stateValue top S 0 0) hh
  · rw [mpBlockWord,eval_append_success _ _ _ _ hs,eval_drop]
    rcases hab 0 (cantor A S) with hh2 | hs2
    · left
      exact eval_append_halt pab (mpTail B) (stateValue 0 (cantor A S) 0 0) hh2
    · rw [eval_append_success _ _ _ _ hs2,eval_mpTail]
      by_cases hbad : A=1 ∨ B=1
      · left; exact if_pos hbad
      · right; exact if_neg hbad

end DiophantineConsistency.ArithmeticCommandRulePerm222
