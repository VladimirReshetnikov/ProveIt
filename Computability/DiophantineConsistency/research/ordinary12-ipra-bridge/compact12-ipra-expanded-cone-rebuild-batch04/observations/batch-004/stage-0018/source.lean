import BusyBeaver.ZFC.ArithmeticRow254
import BusyBeaver.ZFC.ArithmeticSeedTemplates222
import BusyBeaver.ZFC.Code222Proof

set_option autoImplicit false
set_option Elab.async false

/-! The actual C222 row, changing only the two calibrated rule tags. The
bounded graph includes rejected inputs; child results remain explicit inputs.
No history lookup, internal seed validity or machine runtime is assumed. -/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRow222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticRow254

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def rowKernel (k p u v : V) : V := by
  classical
  let a := first p
  let b := first (second p)
  let c := second (second p)
  exact if k = 9 then ArithmeticTemplates222.growG a b c + 1
    else if k = 11 then
      (if c ≠ a ∧ c ≠ b then ArithmeticSeedTemplates222.bundle222 a b c + 1 else 0)
    else ArithmeticRow254.rowKernel k p u v

theorem rowKernel_unchanged (k p u v : V) (h9 : k ≠ 9) (h11 : k ≠ 11) :
    rowKernel k p u v = ArithmeticRow254.rowKernel k p u v := by
  simp only [rowKernel, h9, h11, if_false]

theorem rowKernel_growG (p u v : V) : rowKernel 9 p u v =
    ArithmeticTemplates222.growG (first p) (first (second p)) (second (second p)) + 1 := by
  simp only [rowKernel, if_true]

theorem rowKernel_bundle (p u v : V) : rowKernel 11 p u v =
    if second (second p) ≠ first p ∧ second (second p) ≠ first (second p)
    then ArithmeticSeedTemplates222.bundle222 (first p) (first (second p))
      (second (second p)) + 1 else 0 := by
  simp [rowKernel]

def rowDef : 𝚺₀.Semisentence 5 := .mkSigma
  “r k p u v. ∃ a <⁺ p, ∃ t <⁺ p, !ArithmeticCantor.pairDef p a t ∧
    ∃ b <⁺ p, ∃ c <⁺ p, !ArithmeticCantor.pairDef t b c ∧
    ((k = 9 ∧ ∃ f <⁺ r, !ArithmeticTemplates222.growGDef f a b c ∧ r = f + 1) ∨
     (k = 11 ∧ (((c ≠ a ∧ c ≠ b) ∧ ∃ f <⁺ r,
       !ArithmeticSeedTemplates222.bundleDef f a b c ∧ r = f + 1) ∨
       ((c = a ∨ c = b) ∧ r = 0))) ∨
     (k ≠ 9 ∧ k ≠ 11 ∧ !ArithmeticRow254.rowDef r k p u v))”

instance row_defined : 𝚺₀-Function₄[V] rowKernel via rowDef := .mk fun e => by
  classical
  simp [rowDef, numeral_eq_natCast]
  rw [payload_fields_flat]
  by_cases h9 : e 1 = 9
  · simp_all [rowKernel]
  by_cases h11 : e 1 = 11
  · by_cases hca : second (second (e 2)) = first (e 2) <;>
      by_cases hcb : second (second (e 2)) = first (second (e 2)) <;>
      simp_all [rowKernel]
  simp_all [rowKernel]

end Internal

/-- All other tags, including invalid tags, retain the old numeric row.
Only its numeric child-result interface is reused, not its proof semantics. -/
def row (rec : Nat → Nat) (tag payload : Nat) : Nat :=
  let a := (Cantor.ofNat payload).1
  let b := (Cantor.ofNat (Cantor.ofNat payload).2).1
  let c := (Cantor.ofNat (Cantor.ofNat payload).2).2
  if tag = 9 then KCode222.growG a b c + 1
  else if tag = 11 then
    (if c ≠ a ∧ c ≠ b then KCode222.bundle222 a b c + 1 else 0)
  else Code254History.row rec tag payload

theorem row_unchanged (rec : Nat → Nat) (tag payload : Nat) (h9 : tag ≠ 9) (h11 : tag ≠ 11) :
    row rec tag payload = Code254History.row rec tag payload := by
  simp only [row, h9, h11, if_false]

theorem row_invalid (rec : Nat → Nat) (tag payload : Nat) (h : 12 ≤ tag) :
    row rec tag payload = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  have h9 : 12 + n ≠ 9 := by omega
  have h11 : 12 + n ≠ 11 := by omega
  rw [row_unchanged rec _ _ h9 h11, Nat.add_comm]
  rfl

/-- Exact binding for every tag and arbitrary supplied numeric child results. -/
theorem rowKernel_nat (rec : Nat → Nat) (tag payload : Nat) :
    rowKernel tag payload
      (if tag = 2 then rec (Cantor.ofNat payload).2
       else rec (Cantor.ofNat (Cantor.ofNat payload).2).1)
      (rec (Cantor.ofNat (Cantor.ofNat payload).2).2) = row rec tag payload := by
  by_cases h9 : tag = 9
  · subst tag
    simp [rowKernel, row]
  by_cases h11 : tag = 11
  · subst tag
    simp [rowKernel, row]
  rw [rowKernel_unchanged _ _ _ _ h9 h11, row_unchanged _ _ _ h9 h11]
  exact ArithmeticRow254.rowKernel_nat rec tag payload

theorem rowGraph_nat (rec : Nat → Nat) (tag payload output : Nat) :
    rowDef.val.Evalb (ArithmeticRow254.rowEnv rec tag payload output) ↔
      output = row rec tag payload := by
  have h := (row_defined (V := Nat)).df (ArithmeticRow254.rowEnv rec tag payload output)
  change rowDef.val.Evalb (ArithmeticRow254.rowEnv rec tag payload output) ↔
    output = rowKernel tag payload
      (if tag = 2 then rec (Cantor.ofNat payload).2
        else rec (Cantor.ofNat (Cantor.ofNat payload).2).1)
      (rec (Cantor.ofNat (Cantor.ofNat payload).2).2) at h
  exact h.trans (Iff.of_eq (congrArg (fun z => output = z) (rowKernel_nat rec tag payload)))

/-- Zero denotes invalid data, and successor denotes a valid C222 conclusion. -/
def parsedValue : Option Code254Proof.RawProof → Nat
  | none => 0
  | some p => if Code222Proof.valid222 p then Code222Proof.conclusion222 p + 1 else 0

/-- Complete one-rule agreement with the unchanged parser and the NEW C222
conclusions/validity, for every oracle, tag and payload. -/
theorem row_parsedValue (rec : Nat → Option Code254Proof.RawProof) (tag payload : Nat) :
    row (fun c => parsedValue (rec c)) tag payload =
      parsedValue (Code254Proof.decodeStep rec tag payload) := by
  match tag with
  | 0 =>
      by_cases hp : payload = 0 <;>
        simp [row, Code254History.row, Code254Proof.decodeStep, parsedValue,
          Code222Proof.valid222, Code222Proof.conclusion222, hp]
  | 1 =>
      cases hp : rec (Cantor.ofNat (Cantor.ofNat payload).2).1 with
      | none => simp [row, Code254History.row, Code254Proof.decodeStep, hp, parsedValue]
      | some p =>
          cases hq : rec (Cantor.ofNat (Cantor.ofNat payload).2).2 with
          | none => simp [row, Code254History.row, Code254Proof.decodeStep, hp, hq, parsedValue]
          | some q =>
              cases hv : Code222Proof.valid222 p <;> cases hw : Code222Proof.valid222 q <;>
                simp [row, Code254History.row, Code254Proof.decodeStep, hp, hq, parsedValue,
                  Code222Proof.valid222, Code222Proof.conclusion222, hv, hw]
  | 2 =>
      cases hp : rec (Cantor.ofNat payload).2 with
      | none => simp [row, Code254History.row, Code254Proof.decodeStep, hp, parsedValue]
      | some p =>
          cases hv : Code222Proof.valid222 p <;>
            simp [row, Code254History.row, Code254Proof.decodeStep, hp, parsedValue,
              Code222Proof.valid222, Code222Proof.conclusion222, hv]
  | 3 => simp [row, Code254History.row, Code254Proof.decodeStep, parsedValue,
      Code222Proof.valid222, Code222Proof.conclusion222]
  | 4 => simp [row, Code254History.row, Code254Proof.decodeStep, parsedValue,
      Code222Proof.valid222, Code222Proof.conclusion222]
  | 5 => simp [row, Code254History.row, Code254Proof.decodeStep, parsedValue,
      Code222Proof.valid222, Code222Proof.conclusion222]
  | 6 => simp [row, Code254History.row, Code254Proof.decodeStep, parsedValue,
      Code222Proof.valid222, Code222Proof.conclusion222]
  | 7 => simp [row, Code254History.row, Code254Proof.decodeStep, parsedValue,
      Code222Proof.valid222, Code222Proof.conclusion222]
  | 8 => simp [row, Code254History.row, Code254Proof.decodeStep, parsedValue,
      Code222Proof.valid222, Code222Proof.conclusion222]
  | 9 => simp [row, Code254Proof.decodeStep, parsedValue,
      Code222Proof.valid222, Code222Proof.conclusion222]
  | 10 => simp [row, Code254History.row, Code254Proof.decodeStep, parsedValue,
      Code222Proof.valid222, Code222Proof.conclusion222]
  | 11 => simp [row, Code254Proof.decodeStep, parsedValue,
      Code222Proof.valid222, Code222Proof.conclusion222, Bool.and_eq_true]
  | n + 12 =>
      rw [row_invalid _ _ _ (by omega)]
      rfl

/-- As in the old numeric interface, only child indices at most payload
can affect a row. The two new leaves do not read the child oracle at all. -/
theorem row_congr {f g : Nat → Nat} (tag payload : Nat)
    (h : ∀ i, i ≤ payload → f i = g i) : row f tag payload = row g tag payload := by
  by_cases h9 : tag = 9
  · simp [row, h9]
  by_cases h11 : tag = 11
  · simp [row, h11]
  rw [row_unchanged _ _ _ h9 h11, row_unchanged _ _ _ h9 h11]
  exact Code254History.row_congr tag payload h

end SetTheory.BusyBeaver.ZFC.ArithmeticRow222
