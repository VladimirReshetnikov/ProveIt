import BusyBeaver.ZFC.ArithmeticHistory222

set_option autoImplicit false
set_option Elab.async false

/-! Exact proof-constructor equations for the represented C222 checker.
All labels, child codes and conclusions range over an arbitrary IΣ1 model.
Tag9 uses growG and tag11 uses the helper-free seed with only its two gates.
These are evaluation equations, not seed soundness or a calculus translation. -/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticHistory222
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho8)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The unchanged base-12 proof-node convention; code0 is not a node. -/
noncomputable def node (tag payload : V) : V := 12 * payload + tag + 1

def nodeDef : 𝚺₀.Semisentence 3 := .mkSigma
  “out tag payload. out = 12 * payload + tag + 1”

instance node_defined : 𝚺₀-Function₂[V] node via nodeDef :=
  .mk fun e => by simp [nodeDef, node, numeral_eq_natCast]

theorem node_ne_zero (tag payload : V) : node tag payload ≠ 0 := by simp [node]

/-- Normalize the actual quotient/remainder and use only the new recurrence.
The GEN child is the whole payload tail, while MP uses its two projections. -/
theorem value_node (tag payload : V) (ht : tag < 12) :
    value (node tag payload) = ArithmeticRow222.rowKernel tag payload
      (if tag = 2 then value (second payload)
       else value (first (second payload)))
      (value (second (second payload))) := by
  have hd : (12 * payload + tag) / 12 = payload := div_mul_add' payload 12 ht
  have hm : (12 * payload + tag) % 12 = tag := by
    simpa only [mul_comm] using (mod_mul_add_of_lt payload 12 ht)
  rw [node, value_succ, hd, hm]

@[simp] theorem node_nat (tag payload : Nat) :
    node tag payload = Code254Proof.node tag payload := by
  simp [node, Code254Proof.node]

private lemma small_tag (n : Nat) (hn : n < 12) :
    (ORingStructure.numeral n : V) < 12 := by
  have hh := numeral_lt_of_lt (M := V) hn
  simpa [numeral_eq_natCast] using hh

theorem value_truth : value (1 : V) = 1 := by
  have hh := value_node (0 : V) 0 (by simp)
  simpa [node, ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel] using hh

/-- Major/minor values include the predecessor gate exactly as in the row. -/
theorem value_mp (conclusion minor major p q : V)
    (hp : value p = minor + 1) (hq : value q = major + 1)
    (he : major = wim minor conclusion) :
    value (node 1 (cantor conclusion (cantor p q))) = conclusion + 1 := by
  have hg : ArithmeticRow254.MPGate conclusion (value p) (value q) :=
    ⟨minor, by rw [hp]; simp, major, by rw [hq]; simp, hp, hq, he⟩
  rw [value_node _ _ (by simp)]
  simp [ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel,
    ArithmeticRow254.mpValue, hg]

theorem value_gen (a conclusion p : V) (hp : value p = conclusion + 1) :
    value (node 2 (cantor a p)) = wal a conclusion + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 2 (by decide))]
  simp [ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel,
    ArithmeticRow254.genValue, hp]

theorem value_r1 (a b : V) :
    value (node 3 (cantor a b)) = rho1 a b + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 3 (by decide))]
  simp [ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel]

theorem value_r2 (a b c : V) :
    value (node 4 (cantor a (cantor b c))) = rho2 a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 4 (by decide))]
  simp [ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel]

theorem value_r3 (a b c : V) :
    value (node 5 (cantor a (cantor b c))) = rho3 a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 5 (by decide))]
  simp [ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel]

theorem value_r4 (a b c : V) :
    value (node 6 (cantor a (cantor b c))) = rho4 a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 6 (by decide))]
  simp [ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel]

theorem value_r5 (a b c : V) :
    value (node 7 (cantor a (cantor b c))) = rho5 a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 7 (by decide))]
  simp [ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel]

theorem value_r6 (a b : V) :
    value (node 8 (cantor a b)) = rho6 a b + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 8 (by decide))]
  simp [ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel]

/-- The changed tag9 is the exact merged equality row, with no gates. -/
theorem value_growG (a b c : V) :
    value (node 9 (cantor a (cantor b c))) = ArithmeticTemplates222.growG a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 9 (by decide))]
  simp [ArithmeticRow222.rowKernel]

theorem value_r8 (a b c u : V) :
    value (node 10 (cantor a (cantor b (cantor c u)))) = rho8 a b c u + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 10 (by decide))]
  simp [ArithmeticRow222.rowKernel, ArithmeticRow254.rowKernel]

/-- The changed tag11 retains only c≠a,b. No a≠b or positive-c premise. -/
theorem value_bundle (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    value (node 11 (cantor a (cantor b c))) =
      ArithmeticSeedTemplates222.bundle222 a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 11 (by decide))]
  simp [ArithmeticRow222.rowKernel, ha, hb]

/-- The forbidden self-binding cases are rejected, not accepted at another formula. -/
theorem value_bundle_rejected (a b c : V) (h : c = a ∨ c = b) :
    value (node 11 (cantor a (cantor b c))) = 0 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 11 (by decide))]
  rcases h with rfl | rfl <;> simp [ArithmeticRow222.rowKernel]

end SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors222
