import BusyBeaver.ZFC.ArithmeticHistoryRecurrence254

/-!
Exact constructor equations for the actual arithmetic C254 validator.
Every label, payload and child proof code may be internal to an IΣ1 model.
No inductive proof object, standard-code restriction, scheduler invariant,
or consistency translation is assumed by these scalar equations.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticRow254 ArithmeticHistory254
open ArithmeticHistoryRecurrence254
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho7 rho8 bundle)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def node (tag payload : V) : V := 12 * payload + tag + 1

def nodeDef : 𝚺₀.Semisentence 3 := .mkSigma
  “out tag payload. out = 12 * payload + tag + 1”

instance node_defined : 𝚺₀-Function₂[V] node via nodeDef :=
  .mk fun e => by simp [nodeDef, node, numeral_eq_natCast]

lemma node_ne_zero (tag payload : V) : node tag payload ≠ 0 := by simp [node]

/-- Normalize the actual quotient and remainder before invoking the already
checked value recurrence. Child VALUES are the actual complete history values. -/
theorem value_node (tag payload : V) (ht : tag < 12) :
    value (node tag payload) = rowKernel tag payload
      (if tag = 2 then value (second payload)
       else value (first (second payload)))
      (value (second (second payload))) := by
  have hd : (12 * payload + tag) / 12 = payload := div_mul_add' payload 12 ht
  have hm : (12 * payload + tag) % 12 = tag := by
    simpa only [mul_comm] using (mod_mul_add_of_lt payload 12 ht)
  rw [node, value_succ, hd, hm]

/-- Fixed literal tags retain the original proof-code convention. -/
@[simp] theorem node_nat (tag payload : Nat) :
    node tag payload = Code254Proof.node tag payload := by
  simp [node, Code254Proof.node, ← numeral_twelve_eq_twelve (V := Nat), Nat.numeral_eq]

lemma small_tag (n : Nat) (hn : n < 12) : (ORingStructure.numeral n : V) < 12 := by
  have hh := numeral_lt_of_lt (M := V) hn
  simpa only [numeral_twelve_eq_twelve] using hh

/-- Numeric constructor for literal truth0; proof code0 remains invalid. -/
theorem value_truth : value (1 : V) = 1 := by
  have hh := value_node (0 : V) 0 (by simp)
  simpa [node, rowKernel] using hh

/-- Exact MP proof code: first payload field is the conclusion, followed by
both positive child proof codes. The validator's predecessor gate is retained. -/
theorem value_mp (conclusion minor major p q : V)
    (hp : value p = minor + 1) (hq : value q = major + 1)
    (he : major = wim minor conclusion) :
    value (node 1 (cantor conclusion (cantor p q))) = conclusion + 1 := by
  have hg : MPGate conclusion (value p) (value q) :=
    ⟨minor, by rw [hp]; simp, major, by rw [hq]; simp, hp, hq, he⟩
  rw [value_node _ _ (by simp)]
  simp [rowKernel, mpValue, hg]

/-- GEN uses the entire tail child p, even when p is a composite code. -/
theorem value_gen (a conclusion p : V) (hp : value p = conclusion + 1) :
    value (node 2 (cantor a p)) = wal a conclusion + 1 := by
  rw [value_node _ _ (by simpa only [numeral_two_eq_two] using small_tag (V := V) 2 (by decide))]
  simp [rowKernel, genValue, hp]

theorem value_r1 (a b : V) :
    value (node 3 (cantor a b)) = rho1 a b + 1 := by
  rw [value_node _ _ (by simpa only [numeral_three_eq_three] using small_tag (V := V) 3 (by decide))]
  simp [rowKernel]

theorem value_r2 (a b c : V) :
    value (node 4 (cantor a (cantor b c))) = rho2 a b c + 1 := by
  rw [value_node _ _ (by simpa only [numeral_four_eq_four] using small_tag (V := V) 4 (by decide))]
  simp [rowKernel]

theorem value_r3 (a b c : V) :
    value (node 5 (cantor a (cantor b c))) = rho3 a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 5 (by decide))]
  simp [rowKernel]

theorem value_r4 (a b c : V) :
    value (node 6 (cantor a (cantor b c))) = rho4 a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 6 (by decide))]
  simp [rowKernel]

theorem value_r5 (a b c : V) :
    value (node 7 (cantor a (cantor b c))) = rho5 a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 7 (by decide))]
  simp [rowKernel]

theorem value_r6 (a b : V) :
    value (node 8 (cantor a b)) = rho6 a b + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 8 (by decide))]
  simp [rowKernel]

theorem value_r7 (a b c : V) :
    value (node 9 (cantor a (cantor b c))) = rho7 a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 9 (by decide))]
  simp [rowKernel]

theorem value_r8 (a b c u : V) :
    value (node 10 (cantor a (cantor b (cantor c u)))) = rho8 a b c u + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 10 (by decide))]
  simp [rowKernel]

theorem value_bundle (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    value (node 11 (cantor a (cantor b c))) = bundle a b c + 1 := by
  rw [value_node _ _ (by simpa [numeral_eq_natCast] using small_tag (V := V) 11 (by decide))]
  simp [rowKernel, ha, hb]

end SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254
