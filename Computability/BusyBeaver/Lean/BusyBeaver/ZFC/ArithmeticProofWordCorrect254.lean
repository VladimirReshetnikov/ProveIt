import BusyBeaver.ZFC.ArithmeticCommandRuleExecution254

/-!
All-internal correctness of the unchanged twelve-rule proof-word compiler.
Accepted proof codes execute from every top and saved stack to their exact
conclusion, or halt earlier. The induction is on a Pi1 prefix contract in an
arbitrary IΣ1 model, with no standard-code or register-growth restriction.
This is compiler execution correctness, not a consistency translation.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticProofWordCorrect254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticRow254
open ArithmeticHistory254 ArithmeticHistoryRecurrence254
open ArithmeticCommandBlocks254 (Circuit)
open ArithmeticProofWordRow254 ArithmeticProofWord254 ArithmeticProofWordContract254
open ArithmeticCommandBlockExecution254 ArithmeticCommandLeafExecution254
open ArithmeticCommandRuleExecution254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The numeric row consumes contracts only for nonzero child results.
GEN's first child has already been selected from the whole payload tail. -/
lemma row_contract (tag payload u v p q : V)
    (hp : u ≠ 0 → Contract p (u - 1))
    (hq : v ≠ 0 → Contract q (v - 1))
    (hr : rowKernel tag payload u v ≠ 0) :
    Contract (rowValue tag payload p q) (rowKernel tag payload u v - 1) := by
  classical
  by_cases h0 : tag = 0
  · subst tag
    by_cases he : payload = 0
    · simpa [rowValue, rowKernel, he] using (discard_contract (0 : V) 0 0 0)
    · exact False.elim (hr (by simp [rowKernel, he]))
  by_cases h1 : tag = 1
  · subst tag
    have hg : MPGate (first payload) u v := by
      by_contra hn
      exact hr (by simp [rowKernel, mpValue, hn])
    rcases hg with ⟨x, _, m, _, hu, hv, hm⟩
    have hun : u ≠ 0 := by rw [hu]; simp
    have hvn : v ≠ 0 := by rw [hv]; simp
    have hux : u - 1 = x := by rw [hu]; simp
    have hvm : v - 1 = wim x (first payload) := by rw [hv]; simpa using hm
    have hpc : Contract p x := hux ▸ hp hun
    have hqc : Contract q (wim x (first payload)) := hvm ▸ hq hvn
    have hc := circuit_mp_contract .input0 .input1 .input2 (first payload) p q 0 x
      (by simpa only [Circuit.eval_input1] using hpc)
      (by simpa only [Circuit.eval_input2, Circuit.eval_input0] using hqc)
    have hg' : MPGate (first payload) u v := ⟨x, by rw [hu]; simp,
      m, by rw [hv]; simp, hu, hv, hm⟩
    simpa [rowValue, rowKernel, mpCircuit, mpValue, hg'] using hc
  by_cases h2 : tag = 2
  · subst tag
    have hun : u ≠ 0 := by
      intro hz
      exact hr (by simp [rowKernel, genValue, hz])
    have hc := circuit_gen_contract .input0 .input1 (first payload) p 0 0 (u - 1)
      (by simpa only [Circuit.eval_input1] using hp hun)
    simpa [rowValue, rowKernel, genCircuit, genValue, hun] using hc
  by_cases h3 : tag = 3
  · subst tag
    simpa [rowValue, rowKernel] using (leaf1 (first payload) (second payload) 0 0)
  by_cases h4 : tag = 4
  · subst tag
    simpa [rowValue, rowKernel] using (leaf2 (first payload) (first (second payload)) (second (second payload)) 0)
  by_cases h5 : tag = 5
  · subst tag
    simpa [rowValue, rowKernel] using (leaf3 (first payload) (first (second payload)) (second (second payload)) 0)
  by_cases h6 : tag = 6
  · subst tag
    simpa [rowValue, rowKernel] using (leaf4 (first payload) (first (second payload)) (second (second payload)) 0)
  by_cases h7 : tag = 7
  · subst tag
    simpa [rowValue, rowKernel] using (leaf5 (first payload) (first (second payload)) (second (second payload)) 0)
  by_cases h8 : tag = 8
  · subst tag
    simpa [rowValue, rowKernel] using (leaf6 (first payload) (second payload) 0 0)
  by_cases h9 : tag = 9
  · subst tag
    simpa [rowValue, rowKernel] using (leaf7 (first payload) (first (second payload)) (second (second payload)) 0)
  by_cases h10 : tag = 10
  · subst tag
    simpa [rowValue, rowKernel] using (leaf8 (first payload) (first (second payload)) (first (second (second payload))) (second (second (second payload))))
  by_cases h11 : tag = 11
  · subst tag
    have hg : second (second payload) ≠ first payload ∧
        second (second payload) ≠ first (second payload) := by
      by_contra hn
      exact hr (by simp [rowKernel, hn])
    simpa [rowValue, rowKernel, bundleCircuit, hg] using
      (bundle_contract (first payload) (first (second payload))
        (second (second payload)) 0 hg.1 hg.2)
  exact False.elim (hr (by simp [rowKernel, h0, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11]))

/-- Literal successor step, with exact earlier child indices from the
validator and raw compiler recurrences. No arbitrary semantic rule is used. -/
theorem good_succ (raw : V) (hp : PrefixGood raw) : Good (raw + 1) := by
  classical
  by_cases hv : value (raw + 1) = 0
  · exact Or.inl hv
  · apply Or.inr
    rw [rawWord_succ, value_succ]
    apply row_contract
    · intro hu
      by_cases ht : raw % 12 = 2
      · simpa only [if_pos ht] using
          contract_of_good (hp _ (tail_le raw)) (by simpa only [if_pos ht] using hu)
      · simpa only [if_neg ht] using
          contract_of_good (hp _ (minor_le raw)) (by simpa only [if_neg ht] using hu)
    · exact fun hu => contract_of_good (hp _ (major_le raw)) hu
    · simpa only [value_succ] using hv

/-- Every internal accepted proof code has the all-input execution contract. -/
theorem good_all (code : V) : Good code := good_of_step good_succ code

theorem accepted_contract (code : V) (hv : value code ≠ 0) :
    Contract (rawWord code) (value code - 1) :=
  contract_of_good (good_all code) hv

/-- The public validity-gated compiler agrees on every accepted code. -/
theorem compiled_contract (code : V) (hv : value code ≠ 0) :
    Contract (compiledWord code) (value code - 1) := by
  rw [compiledWord_valid code hv]
  exact accepted_contract code hv

end SetTheory.BusyBeaver.ZFC.ArithmeticProofWordCorrect254
