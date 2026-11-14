import ConfigurationStep
import PA195Bounded

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace ConfigurationStandard
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory BinaryTapeCodes TableDispatch TableModelSemantics ConfigurationStep
open List.Vector

local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

theorem numeralNat (n : Nat) : modelNumeral Nat n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change modelNumeral Nat n + 1 = n + 1
    rw [ih]

theorem lookupNat (d : Nat) (xs : List Nat) (n : Nat) : lookupSem d xs n = xs.getD n d := by
  have h := (modelLookupAll d xs n).symm
  change lookupSem d xs n = eval (lookupCode d xs) (n ::ᵥ nil) at h
  rw [h, evalLookup]

theorem ofFn_three (q l r : Nat) : List.Vector.ofFn (![q,l,r] : Fin 3 → Nat) =
    q ::ᵥ l ::ᵥ r ::ᵥ nil := by
  ext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun z => Fin.elim0 z) k

theorem fnAdd (a b : Nat) : Structure.func (L := language) addCode ![a,b] = a+b := by
  change eval addCode (ofFn ![a,b]) = _
  rw [ofFn_two, eval_addCode]
  rfl

theorem fnLt (a b : Nat) : Structure.func (L := language) ltBitCode ![a,b] = if a < b then 1 else 0 := by
  change eval ltBitCode (ofFn ![a,b]) = _
  rw [ofFn_two, eval_ltBitCode]
  rfl

theorem fnParity (a : Nat) : Structure.func (L := language) parityCode (fun _ => a) = a%2 := by
  change eval parityCode (a ::ᵥ nil) = _
  exact parityEval a

theorem fnHalf (a : Nat) : Structure.func (L := language) halfCode (fun _ => a) = a/2 := by
  change eval halfCode (a ::ᵥ nil) = _
  exact halfEval a

theorem fnZero : Structure.func (L := language) (Code.zero 0) (Fin.elim0 : Fin 0 → Nat) = 0 := rfl

theorem directionBit (i : Nat) : let d := (PA195Rows.rows.getD i (0,0,195)).2.1; d = 0 ∨ d = 1 := by
  have hall : PA195Rows.rows.all (fun row => decide (row.2.1 = 0 ∨ row.2.1 = 1)) = true := by decide +kernel
  by_cases hi : i < PA195Rows.rows.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact of_decide_eq_true ((List.all_eq_true.mp hall) _ (List.getElem_mem hi))
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    exact Or.inl rfl

def numericNext (q l r : Nat) : Nat × Nat × Nat :=
  if q < 195 then
    let row := PA195Rows.rows.getD (2*q + r%2) (0,0,195)
    if row.2.1 = 1 then (row.2.2,2*l+row.1,r/2)
    else (row.2.2,l/2,l%2+2*(row.1+2*(r/2)))
  else (q,l,r)

theorem modelStepNat (q l r : Nat) :
    stepSem q l r = numericNext q l r := by
  classical
  simp only [stepSem, numeralNat, fnAdd, fnLt, fnParity, fnHalf, fnZero, lookupNat, numericNext]
  rw [show q+q = 2*q by omega]
  have h1 := getDMap (fun x : Nat × Nat × Nat => x.1) PA195Rows.rows (2*q+r%2) (0,0,195)
  have h2 := getDMap (fun x : Nat × Nat × Nat => x.2.1) PA195Rows.rows (2*q+r%2) (0,0,195)
  have h3 := getDMap (fun x : Nat × Nat × Nat => x.2.2) PA195Rows.rows (2*q+r%2) (0,0,195)
  change writes.getD (2*q+r%2) 0 = _ at h1
  change directions.getD (2*q+r%2) 0 = _ at h2
  change targets.getD (2*q+r%2) 195 = _ at h3
  rw [h1,h2,h3]
  by_cases hq : q < 195
  · rcases directionBit (2*q+r%2) with hd | hd <;> simp only [hq, hd, ite_true, ite_false, Nat.reduceEqDiff] <;> simp only [Prod.mk.injEq, true_and, and_true] <;> omega
  · simp [hq]

theorem evalStepNat (q l r : Nat) :
    (eval nextQ (q ::ᵥ l ::ᵥ r ::ᵥ nil),
     eval nextL (q ::ᵥ l ::ᵥ r ::ᵥ nil),
     eval nextR (q ::ᵥ l ::ᵥ r ::ᵥ nil)) = numericNext q l r := by
  have h := modelNext (![q,l,r] : Fin 3 → Nat)
  change (eval nextQ (ofFn ![q,l,r]), eval nextL (ofFn ![q,l,r]),
    eval nextR (ofFn ![q,l,r])) = stepSem q l r at h
  rw [ofFn_three] at h
  exact h.trans (modelStepNat q l r)

theorem evalStepBounded (q l r : Nat) :
    (eval nextQ (q ::ᵥ l ::ᵥ r ::ᵥ nil),
     eval nextL (q ::ᵥ l ::ᵥ r ::ᵥ nil),
     eval nextR (q ::ᵥ l ::ᵥ r ::ᵥ nil)) = PA195Bounded.next (q,l,r) := by
  rw [evalStepNat]
  rfl

theorem evalStepZip (c : M6.Zip.Conf) :
    (eval nextQ (c.q ::ᵥ PA195Bounded.bits c.l ::ᵥ PA195Bounded.bits c.r ::ᵥ nil),
     eval nextL (c.q ::ᵥ PA195Bounded.bits c.l ::ᵥ PA195Bounded.bits c.r ::ᵥ nil),
     eval nextR (c.q ::ᵥ PA195Bounded.bits c.l ::ᵥ PA195Bounded.bits c.r ::ᵥ nil)) =
    PA195Bounded.encodeZip (PA195Bounded.zipTotalStep c) := by
  rw [evalStepBounded]
  exact PA195Bounded.zip_step_binding c

#print axioms evalStepBounded
#print axioms evalStepZip
#print axioms directionBit
#print axioms modelStepNat
#print axioms evalStepNat
end ConfigurationStandard
