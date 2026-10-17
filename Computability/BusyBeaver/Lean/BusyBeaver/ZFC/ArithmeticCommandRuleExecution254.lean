import BusyBeaver.ZFC.ArithmeticCommandLeafExecution254

/-!
Exact all-internal GEN/MP block contracts, using the actual
represented command evaluator. The two numerical block definitions are tied
back to the literal Circuit constructors. External finite lists below only
name the fixed AX entries and fixed NIP counts; no internal word is decoded
as an externally finite list. No proof-code induction or PA endpoint occurs.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho7 rho8)
open ArithmeticCommandStep254 ArithmeticCommandAppend254 ArithmeticCommandRun254
open ArithmeticCommandExecution254 ArithmeticProofWordContract254
open ArithmeticCommandBlockExecution254 ArithmeticCommandLeafExecution254
open ArithmeticCommandBlocks254 (Circuit)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def terminatorWord : V := dropWord 0 (nipWord 0 (nipWord 0 0))
noncomputable def genTail (i : V) : V :=
  dropWord 0 (nipWord 0 (axWord i i 0 0 (appendValue (nipsWord 9) terminatorWord)))
noncomputable def genBlockWord (i p : V) : V := appendValue p (genTail i)
noncomputable def mpTail (b : V) : V :=
  nipWord 0 (dropWord 0 (nipWord 0 (mpWord b
    (axWord b 0 0 0 (appendValue (nipsWord 10) terminatorWord)))))
noncomputable def mpBlockWord (b pa pab : V) : V :=
  appendValue pa (dropWord 0 (appendValue pab (mpTail b)))

lemma circuit_terminator (a b c u : V) : Circuit.terminator.eval a b c u = terminatorWord := by
  simp only [Circuit.terminator, circuit_consDrop, circuit_consNip, Circuit.eval_zero,
    terminatorWord]

/-- These equalities bind the numerical words to the actual compiler Circuit,
with every input and child word internal and arbitrary. -/
lemma circuit_genBlock (i p : Circuit) (a b c u : V) :
    (Circuit.genBlock i p).eval a b c u = genBlockWord (i.eval a b c u) (p.eval a b c u) := by
  simp only [Circuit.genBlock, circuit_append, circuit_consDrop, circuit_consNip,
    circuit_consAx, circuit_nips, circuit_terminator, Circuit.eval_zero,
    genBlockWord, genTail]

lemma circuit_mpBlock (b pa pab : Circuit) (a d c u : V) :
    (Circuit.mpBlock b pa pab).eval a d c u =
      mpBlockWord (b.eval a d c u) (pa.eval a d c u) (pab.eval a d c u) := by
  simp only [Circuit.mpBlock, circuit_append, circuit_consDrop, circuit_consNip,
    circuit_consMp, circuit_consAx, circuit_nips, circuit_terminator, Circuit.eval_zero,
    mpBlockWord, mpTail]

noncomputable def genPrefix (i h : V) : List V :=
  [rho1 i h, rho2 i h i, rho3 i h i, rho4 i h i, rho5 i h i,
    rho6 i h, rho7 i h i, rho8 i h i 0]

lemma genPrefix_ne_one (i h : V) : ∀ x, x ∈ genPrefix i h → x ≠ 1 := by
  intro x hx
  apply axList_ne_one i h h i 0 x
  change x ∈ genPrefix i h ++ [wal i h]
  exact List.mem_append_left _ hx

lemma gen_cleanup (i h s : V) :
    evalValue (appendValue (nipsWord 9) terminatorWord)
      (stateValue 0 (axStackValue i h h i 0 0 s) 0 0) = someState (wal i h) s 0 0 := by
  have he := select_entry (genPrefix i h) (wal i h) [] 0 0 0 s
    (by simp) (by simp) (wal_ne_one i h) (genPrefix_ne_one i h) (by simp)
  have hstack : axStackValue i h h i 0 0 s =
      pushL (genPrefix i h ++ wal i h :: ([] ++ [0])) s := rfl
  rw [hstack]
  simpa only [genPrefix, List.length_cons, List.length_nil, Nat.reduceAdd,
    nipsWord, terminatorWord] using he

/-- The GEN suffix succeeds even if the child conclusion is code1: the first
NIP sees cache0, and the later caches are wal-tagged or the explicit zeros. -/
theorem eval_genTail (i h s : V) :
    evalValue (genTail i) (stateValue h s 0 0) = someState (wal i h) s 0 0 := by
  rw [genTail, eval_drop, eval_nip]
  simp only [add_zero, zero_add, zero_ne_one, if_false, first_cantor, second_cantor]
  rw [eval_ax]
  simp only [add_zero, zero_add, gate_self]
  exact gen_cleanup i h s

lemma mp_cleanup (b s : V) :
    evalValue (appendValue (nipsWord 10) terminatorWord)
      (stateValue 0 (axStackValue b 0 0 b 0 b (cantor 0 s)) 0 0) =
        if b = 1 then 0 else someState b s 0 0 := by
  rw [axStack_eq]
  have hn := eval_nips_cont 0 (cantor 0 s) 0 (axList b 0 0 b 0) 0 b terminatorWord
    (by simp) (axList_ne_one b 0 0 b 0)
  have hlen : (axList b 0 0 b 0).length + 1 = 10 := rfl
  rw [hlen] at hn
  rw [hn, terminatorWord, eval_drop]
  simp only [add_zero, first_cantor, second_cantor]
  rw [eval_nip]
  by_cases hb : b = 1
  · simp [hb]
  · simp only [hb, if_false, first_cantor, second_cantor, add_zero]
    rw [eval_nip]
    simp [someState]

/-- Exact MP suffix: either cached falsity causes the literal NIP halt, or
the original stack is restored and the desired conclusion is the top. -/
theorem eval_mpTail (a b s : V) :
    evalValue (mpTail b) (stateValue (wim a b) (cantor a s) 0 0) =
      if a = 1 ∨ b = 1 then 0 else someState b s 0 0 := by
  rw [mpTail, eval_nip]
  simp only [zero_ne_one, if_false, first_cantor, second_cantor, add_zero]
  rw [eval_drop, eval_nip]
  by_cases ha : a = 1
  · simp [ha]
  · simp only [ha, if_false, first_cantor, second_cantor, add_zero]
    rw [eval_mp]
    simp only [zero_add, if_pos rfl]
    rw [eval_ax]
    simp only [add_zero, zero_add, gate_self, mp_cleanup]
    simp [ha]

/-- Actual arbitrary-stack all-internal generalization contract. -/
theorem gen_contract (i : V) {p h : V} (hp : Contract p h) :
    Contract (genBlockWord i p) (wal i h) := by
  intro t s
  rcases hp t s with hn | hs
  · left
    exact eval_append_halt p (genTail i) (stateValue t s 0 0) hn
  · right
    rw [genBlockWord, eval_append_success _ _ _ _ hs]
    exact eval_genTail i h s

/-- The major contract is instantiated at top0 and the exact saved minor
stack. Its universal saved-stack quantifier is part of the Pi1 contract. -/
theorem mp_contract {a b pa pab : V} (ha : Contract pa a) (hab : Contract pab (wim a b)) :
    Contract (mpBlockWord b pa pab) b := by
  intro t s
  rcases ha t s with hn | hs
  · left
    exact eval_append_halt pa _ (stateValue t s 0 0) hn
  · rw [mpBlockWord, eval_append_success _ _ _ _ hs, eval_drop]
    simp only [add_zero]
    rcases hab 0 (cantor a s) with hn2 | hs2
    · left
      exact eval_append_halt pab (mpTail b) (stateValue 0 (cantor a s) 0 0) hn2
    · rw [eval_append_success _ _ _ _ hs2, eval_mpTail]
      by_cases hbad : a = 1 ∨ b = 1
      · left; exact if_pos hbad
      · right; exact if_neg hbad

/-- Literal Circuit instances, ready for the separate accepted-row proof. -/
theorem circuit_gen_contract (i p : Circuit) (a b c u h : V)
    (hp : Contract (p.eval a b c u) h) :
    Contract ((Circuit.genBlock i p).eval a b c u) (wal (i.eval a b c u) h) := by
  rw [circuit_genBlock]
  exact gen_contract _ hp

theorem circuit_mp_contract (b pa pab : Circuit) (a d c u x : V)
    (hp : Contract (pa.eval a d c u) x)
    (hq : Contract (pab.eval a d c u) (wim x (b.eval a d c u))) :
    Contract ((Circuit.mpBlock b pa pab).eval a d c u) (b.eval a d c u) := by
  rw [circuit_mpBlock]
  exact mp_contract hp hq

end SetTheory.BusyBeaver.ZFC.ArithmeticCommandRuleExecution254
