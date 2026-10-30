import BusyBeaver.ZFC.ArithmeticProofConstructors222
import BusyBeaver.ZFC.ArithmeticStackTail254

set_option autoImplicit false
set_option Elab.async false

/-!
Bounded actual C222 proof witnesses for arithmetic theorem stacks.
ProvB and StackB are Delta1; existential certification of the actual four-field
working-state code is Sigma1. The stream is internally bounded by its numeric
code, with the checked Cantor-tail drain supplying every later truth entry.
The reused StackTail254 is solely numeric Cantor-tail iteration; no old
checker or runtime semantics is imported. Push/pop and witness-bound
weakening are local algebraic facts. No runtime
preservation, scheduler soundness or PA consistency theorem is asserted here.
-/
namespace DiophantineConsistency.ArithmeticStackCertificate222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticHistory222 ArithmeticProofConstructors222
open ArithmeticStackTail254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance value_delta : 𝚫₁-Function₁[V] value := value_defined_delta.to_definable
local instance first_zero_definable : 𝚺₀-Function₁[V] first := first_defined.to_definable
local instance second_zero_definable : 𝚺₀-Function₁[V] second := second_defined.to_definable

/-- B bounds actual accepted proof codes, not formula values or stack size. -/
def ProvB (B x : V) : Prop := ∃ p ≤ B, value p = x+1

instance provB_definable : 𝚫₁-Relation[V] ProvB := by
  unfold ProvB
  definability

/-- The bound1 condition keeps the literal truth witness available beyond the
numeric stack-code range. All quantified indices and witnesses are internal. -/
def StackB (B z : V) : Prop :=
  1 ≤ B ∧ ∀ k ≤ z, ProvB B (first (tailIter k z))

instance stackB_definable : 𝚫₁-Relation[V] StackB := by
  unfold StackB
  definability

lemma prov_of_value {B p x : V} (hp : p ≤ B) (hv : value p = x+1) : ProvB B x :=
  ⟨p, hp, hv⟩

lemma prov_weaken {B C x : V} (hBC : B ≤ C) (hx : ProvB B x) : ProvB C x := by
  obtain ⟨p, hp, hv⟩ := hx
  exact ⟨p, le_trans hp hBC, hv⟩

lemma prov_truth {B : V} (hB : 1 ≤ B) : ProvB B 0 :=
  ⟨1, hB, by simpa only [zero_add] using (value_truth (V := V))⟩

/-- A concrete bound adjoining one new witness. It need not bound any
constructor function uniformly, and contains no choice of stack witnesses. -/
def extendBound (B p : V) : V := B+p+1

lemma old_le_extendBound (B p : V) : B ≤ extendBound B p := by
  have hb : B ≤ B+p := by
    simpa only [add_zero] using (_root_.add_le_add le_rfl (Arithmetic.zero_le p))
  exact le_trans hb (by simp [extendBound])

lemma witness_le_extendBound (B p : V) : p ≤ extendBound B p := by
  have hp : p ≤ B+p := by
    simpa only [zero_add] using (_root_.add_le_add (Arithmetic.zero_le B) le_rfl)
  exact le_trans hp (by simp [extendBound])

lemma one_le_extendBound (B p : V) : 1 ≤ extendBound B p := by
  simpa only [extendBound, zero_add] using
    (_root_.add_le_add (Arithmetic.zero_le (B+p)) (le_rfl : (1 : V) ≤ 1))

lemma prov_extend {B p x : V} (hv : value p = x+1) : ProvB (extendBound B p) x :=
  prov_of_value (witness_le_extendBound B p) hv

lemma stack_weaken {B C z : V} (hBC : B ≤ C) (hs : StackB B z) : StackB C z := by
  refine ⟨le_trans hs.1 hBC, ?_⟩
  intro k hk
  exact prov_weaken hBC (hs.2 k hk)

/-- The unbounded stream consequence is derived from the bounded certificate.
It is not the induction predicate used for scheduler time. -/
lemma stack_full {B z : V} (hs : StackB B z) (k : V) :
    ProvB B (first (tailIter k z)) := by
  by_cases hk : k ≤ z
  · exact hs.2 k hk
  · have hz : z ≤ k := le_of_lt (lt_of_not_ge hk)
    rw [tail_eq_zero_of_le k z hz, first_zero]
    exact prov_truth hs.1

lemma stack_of_full {B z : V} (hB : 1 ≤ B)
    (hs : ∀ k, ProvB B (first (tailIter k z))) : StackB B z :=
  ⟨hB, fun k _ => hs k⟩

lemma stack_zero {B : V} (hB : 1 ≤ B) : StackB B 0 := by
  apply stack_of_full hB
  intro k
  simpa only [tail_zero_stream, first_zero] using (prov_truth hB)

lemma stack_head {B z : V} (hs : StackB B z) : ProvB B (first z) := by
  simpa only [tail_zero] using (stack_full hs (0 : V))

lemma stack_cons {B x z : V} (hx : ProvB B x) (hs : StackB B z) :
    StackB B (cantor x z) := by
  apply stack_of_full hs.1
  intro k
  rcases zero_or_succ k with rfl | ⟨k, rfl⟩
  · simpa only [tail_zero, first_cantor] using hx
  · simpa only [tail_cantor] using stack_full hs k

lemma stack_tail {B z : V} (hs : StackB B z) : StackB B (second z) := by
  apply stack_of_full hs.1
  intro k
  simpa only [tail_shift] using stack_full hs (k+1)

/-- Only a fixed external finite push list is traversed here. The arithmetic
invariant itself has no external list or standard-code component. -/
noncomputable def pushList : List V → V → V
  | [], z => z
  | x::xs, z => cantor x (pushList xs z)

lemma stack_pushList (B z : V) (xs : List V)
    (hx : ∀ x ∈ xs, ProvB B x) (hs : StackB B z) : StackB B (pushList xs z) := by
  revert hx
  induction xs with
  | nil => intro _; exact hs
  | cons x xs ih =>
    intro hx
    exact stack_cons (hx x (List.mem_cons_self ..))
      (ih (fun y hy => hx y (List.mem_cons_of_mem x hy)))

/-- The actual unshifted four-register coding P(top,P(stack,P(d,cache))).
The additive register has no logical proof obligation. -/
def WorkingB (B w : V) : Prop :=
  ProvB B (first w) ∧ ProvB B (second (second (second w))) ∧
    StackB B (first (second w))

instance workingB_definable : 𝚫₁-Relation[V] WorkingB := by
  unfold WorkingB
  definability

def CertifiedWorking (w : V) : Prop := ∃ B, WorkingB B w

instance certifiedWorking_definable : 𝚺₁-Predicate (CertifiedWorking (V := V)) := by
  unfold CertifiedWorking
  definability

lemma working_fields (B top stack d cache : V) :
    WorkingB B (cantor top (cantor stack (cantor d cache))) ↔
      ProvB B top ∧ ProvB B cache ∧ StackB B stack := by simp [WorkingB]

lemma working_weaken {B C w : V} (hBC : B ≤ C) (hw : WorkingB B w) : WorkingB C w :=
  ⟨prov_weaken hBC hw.1, prov_weaken hBC hw.2.1, stack_weaken hBC hw.2.2⟩

lemma working_bound {B w : V} (hw : WorkingB B w) : 1 ≤ B := hw.2.2.1

lemma working_zero {B : V} (hB : 1 ≤ B) : WorkingB B 0 := by
  simpa only [WorkingB, first_zero, second_zero] using
    (show ProvB B (0 : V) ∧ ProvB B 0 ∧ StackB B 0 from
      ⟨prov_truth hB, prov_truth hB, stack_zero hB⟩)

lemma certified_zero : CertifiedWorking (0 : V) := ⟨1, working_zero le_rfl⟩

/-- The actual cached falsity witness, ready for the halting NIP branch. -/
lemma accepted_falsity_of_cache {B w : V} (hw : WorkingB B w)
    (hc : second (second (second w)) = 1) :
    ∃ p ≤ B, value p = 2 := by
  obtain ⟨p, hp, hv⟩ := hw.2.1
  refine ⟨p, hp, ?_⟩
  simpa only [hc, one_add_one_eq_two] using hv

end DiophantineConsistency.ArithmeticStackCertificate222
