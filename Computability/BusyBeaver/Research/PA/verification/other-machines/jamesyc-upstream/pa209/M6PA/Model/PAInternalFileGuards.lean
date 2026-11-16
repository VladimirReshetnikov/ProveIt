module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalFileBoxes
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.FileBoxes
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open FileLayout M6.Runtime
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

def Guard (xs : V) : Branch → Prop
  | none => True
  | some (r,true) => value r xs=0
  | some (r,false) => value r xs≠0

lemma index_room (xs : V) (hsize : (10 : V)≤len xs) (r : Nat) (hr : r<9) :
    (r : V)+1<len xs := by
  have hn : r+1≤9 := by omega
  have hv : (r : V)+1≤9 := by exact_mod_cast hn
  have h9 : (9 : V)<10 := by
    have h : (9 : V)<9+1 := by simp
    simpa only [show (9 : V)+1=10 by ring1] using h
  exact lt_of_le_of_lt hv (lt_of_lt_of_le h9 hsize)

lemma index_valid (xs : V) (hsize : (10 : V)≤len xs) (r : Nat) (hr : r<9) :
    (r : V)<len xs := lt_trans (by simp) (index_room xs hsize r hr)

lemma suffix_nonempty (xs : V) (hsize : (10 : V)≤len xs) (r : Nat) (hr : r<9) :
    suffix r xs≠0 := by
  have hl := index_valid xs hsize r hr
  have hd := drop_length r xs (le_of_lt hl)
  rw [selected r xs hl,len_adjoin] at hd
  intro hz
  rw [hz,len_nil,zero_add] at hd
  exact (ne_of_lt (index_room xs hsize r hr)) hd
end Models
#print axioms index_valid
#print axioms suffix_nonempty
end M6.Arithmetic.PA.InternalTrace.FileBoxes

