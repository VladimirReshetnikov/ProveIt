import ConPAMachineScans
import M6.Runtime

/-! The compressed symbolic tape interpreted in an arbitrary model of IΣ₁. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ConPA.Machine.Compressed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open M6.Runtime

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def push (b : Bool) (x : V) : V := 2*x+(b.toNat : V)

theorem pushDiv (b : Bool) (x : V) : push b x / 2 = x := by
  have h : (b.toNat : V) < 2 := by cases b <;> simp
  exact div_mul_add' x 2 h

theorem pushMod (b : Bool) (x : V) : push b x % 2 = (b.toNat : V) := by
  have h : (b.toNat : V) < 2 := by cases b <;> simp
  rw [push,mul_comm]
  exact mod_mul_add_of_lt x 2 h

def runLength (gap : V) (a c : Nat) : V := (a : V)*gap+(c : V)

/-- A box occupies the final suffix of a compressed tape side. -/
noncomputable def packSegments (gap : V) (box : BoxSt → V) : List Seg → V
  | [] => 0
  | .bit b :: rest => push b (packSegments gap box rest)
  | .run b a c :: rest => bitPrefix b (runLength gap a c) (packSegments gap box rest)
  | .box x :: _ => box x

/-- Convert the compressed zipper to the ordinary packed configuration with
the head bit in the right tape half. -/
noncomputable def encode (label : Nat → Nat) (gap : V) (box : BoxSt → V) : SConf → V
  | (q, false, l, r) => scanFrame true (label q) (packSegments gap box l) (packSegments gap box r)
  | (q, true, l, r) => scanFrame false (label q) (packSegments gap box r) (packSegments gap box l)

def Reach (T : Table) (x y : V) : Prop := ∃ n : V, runFrom T n x = y
def Reach1 (T : Table) (x y : V) : Prop := ∃ n : V, (0 : V) < n ∧ runFrom T n x = y

theorem ofEq {T : Table} {x y : V} (h : x = y) : Reach T x y := by
  exact ⟨0, (runFrom_zero T x).trans h⟩

theorem one {T : Table} {x y : V} (h : step T x = y) : Reach1 T x y := by
  refine ⟨1,Arithmetic.zero_lt_one,?_⟩
  simpa only [zero_add,runFrom_zero,h] using runFrom_succ T (0 : V) x

theorem trans {T : Table} {x y z : V} (h : Reach T x y) (g : Reach T y z) : Reach T x z := by
  obtain ⟨s,hs⟩ := h
  obtain ⟨t,ht⟩ := g
  exact ⟨s+t, by rw [runFrom_add,hs,ht]⟩

theorem transPositive {T : Table} {x y z : V} (h : Reach T x y) (g : Reach1 T y z) :
    Reach1 T x z := by
  obtain ⟨s,hs⟩ := h
  obtain ⟨t,ht,hz⟩ := g
  refine ⟨s+t,lt_of_lt_of_le ht (le_add_of_nonneg_left zero_le),?_⟩
  rw [runFrom_add,hs,hz]

theorem positiveTrans {T : Table} {x y z : V} (h : Reach1 T x y) (g : Reach T y z) :
    Reach1 T x z := by
  obtain ⟨s,hs,hy⟩ := h
  obtain ⟨t,ht⟩ := g
  refine ⟨s+t,lt_of_lt_of_le hs le_self_add,?_⟩
  rw [runFrom_add,hy,ht]

theorem reachable {T : Table} {x y : V} (h : Reach1 T x y) : Reach T x y := by
  obtain ⟨n,_,h⟩ := h
  exact ⟨n,h⟩

theorem lengthSucc (gap : V) (a c : Nat) :
    runLength gap a (c+1) = runLength gap a c + 1 := by
  rw [runLength,runLength,Nat.cast_succ,add_assoc]

theorem lengthZero (gap : V) : runLength gap 0 0 = 0 := by simp [runLength]

theorem peelRun (gap : V) (box : BoxSt → V) (b : Bool) (a c : Nat) (rest : List Seg) :
    packSegments gap box (.run b a (c+1) :: rest) =
      packSegments gap box (.bit b :: .run b a c :: rest) := by
  simp only [packSegments,lengthSucc,bitPrefix_succ,push]

theorem removeEmptyRun (gap : V) (box : BoxSt → V) (b : Bool) (rest : List Seg) :
    packSegments gap box (.run b 0 0 :: rest) = packSegments gap box rest := by
  simp only [packSegments,lengthZero,bitPrefix_zero]

theorem turnRight (q : Nat) (b : Bool) (l r : V) :
    scanFrame false q r (push b l) = scanFrame true q l (push b r) := by
  change ⟪(q : V),push b l/2,2*r+push b l%2⟫ = ⟪(q : V),l,push b r⟫
  rw [pushDiv,pushMod,push]

theorem turnBlank (q : Nat) (r : V) :
    scanFrame false q r 0 = scanFrame true q 0 (push false r) := by
  have h : push false (0 : V) = 0 := by simp [push]
  simpa only [h] using turnRight q false (0 : V) r

theorem rightRow (T : Table) (q q' : Nat) (b w : Bool) (l r : V)
    (hr : findRow T q b.toNat = some ⟨q,b.toNat,w.toNat,true,q'⟩) :
    Reach1 T (scanFrame true q l (push b r)) (scanFrame true q' (push w l) r) :=
  one (scanStep T true b w q q' l r hr)

theorem leftRow (T : Table) (q q' : Nat) (b w : Bool) (l r : V)
    (hr : findRow T q b.toNat = some ⟨q,b.toNat,w.toNat,false,q'⟩) :
    Reach1 T (scanFrame true q l (push b r)) (scanFrame false q' (push w r) l) := by
  rw [←turnRight]
  exact one (scanStep T false b w q q' r l hr)

#print axioms peelRun
#print axioms turnRight
#print axioms leftRow
#print axioms rightRow
end models
end ConPA.Machine.Compressed
