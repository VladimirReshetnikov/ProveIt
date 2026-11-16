import ConPAMachineNumerals
import PA194BModelSteps

/-! Direct indexing and scanning agree for a dense 194-state binary table. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace PA194IndexedNumerals
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine
open PA194BRows (Action)
open PA194BModelSteps (table indexedRow find)

def indexedNext (values : List Action) (c : PackedConf) : PackedConf :=
  if c.1 < 194 then
    let a := values.getD (2*c.1+c.2.2%2) (0,0,194)
    if a.2.1 = 1 then (a.2.2,2*c.2.1+a.1,c.2.2/2)
    else (a.2.2,c.2.1/2,c.2.1%2+2*(a.1+2*(c.2.2/2)))
  else c

def indexedRunFrom (values : List Action) (initial : PackedConf) (n : Nat) : PackedConf :=
  Nat.rec initial (fun _ c => indexedNext values c) n

def indexedRun (values : List Action) (n : Nat) : PackedConf := indexedRunFrom values (0,0,0) n

theorem indexedRunFrom_add (values : List Action) (initial : PackedConf) (a b : Nat) :
    indexedRunFrom values initial (a + b) = indexedRunFrom values (indexedRunFrom values initial a) b := by
  induction b with
  | zero => simp [indexedRunFrom]
  | succ b ih =>
    change indexedNext values (indexedRunFrom values initial (a + b)) =
      indexedNext values (indexedRunFrom values (indexedRunFrom values initial a) b)
    rw [ih]

def BinaryDirections (values : List Action) : Prop :=
  ∀ (q : Fin 194) (b : Fin 2), (values.getD (2*q.val+b.val) (0,0,194)).2.1 ≤ 1

private theorem packedStepFind (T : Table) (c : PackedConf) :
    packedStep T c = ((T.find? (fun row => row.q == c.1 && row.b == c.2.2%2)).map
      (fun row => packedOut row c.2.1 c.2.2)).getD c := by
  induction T with
  | nil => rfl
  | cons row T ih =>
    by_cases hq : c.1 = row.q <;> by_cases hb : c.2.2%2 = row.b <;>
      simp [packedStep,hq,hb,Ne.symm,ih]

theorem indexedNext_eq (values : List Action) (length : values.length = 388)
    (direction : BinaryDirections values) (c : PackedConf) :
    packedStep (table values) c = indexedNext values c := by
  rcases c with ⟨q,l,r⟩
  by_cases hq : q < 194
  · have hb : r%2 < 2 := Nat.mod_lt _ (by decide)
    have hi : 2*q+r%2 < values.length := by rw [length]; omega
    have hfind := find values q (r%2) hb hi
    let a := values.getD (2*q+r%2) (0,0,194)
    have ha : a.2.1 ≤ 1 := direction ⟨q,hq⟩ ⟨r%2,hb⟩
    have ha' : a.2.1 = 0 ∨ a.2.1 = 1 := by omega
    simp only [packedStepFind,hfind,Option.map_some,Option.getD_some,indexedNext,hq,if_pos]
    change (if a.2.1 != 0 then (a.2.2,2*l+a.1,r/2)
      else (a.2.2,l/2,4*(r/2)+2*a.1+l%2)) =
        (if a.2.1 = 1 then (a.2.2,2*l+a.1,r/2)
          else (a.2.2,l/2,l%2+2*(a.1+2*(r/2))))
    rcases ha' with hd | hd <;> simp [hd] <;> omega
  · have hn : (table values).find? (fun row => row.q == q && row.b == r%2) = none := by
      apply List.find?_eq_none.mpr
      intro row hr
      simp only [table,List.mem_map,List.mem_range] at hr
      obtain ⟨i,hi,rfl⟩ := hr
      have h : i/2 ≠ q := by omega
      simp [indexedRow,h]
    simp [packedStepFind,indexedNext,hq,hn]

theorem packedRun_eq (values : List Action) (length : values.length = 388)
    (direction : BinaryDirections values) (n : Nat) :
    packedRun (table values) n = indexedRun values n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change packedStep (table values) (packedRun (table values) n) =
      indexedNext values (indexedRun values n)
    rw [ih,indexedNext_eq values length direction]

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem indexedRun_correct (values : List Action) (length : values.length = 388)
    (direction : BinaryDirections values) (n : Nat) :
    run (V := V) (table values) (n : V) = (packedCode (indexedRun values n) : V) := by
  rw [packedRun_correct,packedRun_eq values length direction]

#print axioms indexedNext_eq
#print axioms indexedRun_correct
end models
end PA194IndexedNumerals
