import DirectBFSRowTransfer
import DiophantineConsistency.ArithmeticWangTable
import DiophantineConsistency.ArithmeticPackingBlocks
import DiophantineConsistency.CleanGeometry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSModelIndexMap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWangTable ArithmeticPackingBlocks CleanGeometry
open DirectBFSConjugacyBase DirectBFSConjugacyLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def back (x : V) : V := tabValue rowInverse.toList 0 x
instance back_definable : 𝚺₁-Function₁[V] back := (tab_defined rowInverse.toList 0).to_definable.of_zero

theorem back_cast (i : ℕ) : back (i:V)=(rowInverse.getD i 0:V) := by
  unfold back
  rw [tab_cast]
  simp only [List.getD_eq_getElem?_getD,Array.getElem?_toList,Array.getD_eq_getD_getElem?]

theorem back_bound (x : V) (hx : x<943) : back x<943 := by
  obtain ⟨i,hi,he⟩ := bounded_standard 943 x hx
  rw [he,back_cast]
  exact_mod_cast (row_bounds hi).2

theorem back_zero : back (0:V)=0 := by
  rw [show (0:V)=((0:ℕ):V) by norm_num,back_cast]
  have h : rowInverse.getD 0 0=0 := by decide
  rw [h]

theorem back_one : back (1:V)=1 := by
  rw [show (1:V)=((1:ℕ):V) by norm_num,back_cast]
  have h : rowInverse.getD 1 0=1 := by decide
  rw [h]

theorem represented (b : V → V) [𝚺₁-Function₁[V] b] (N : V) (hb : ∀ j<N,b j<943) :
    ∃ W : V, Blocks 10 (fun j => back (b j)) N W := by
  let f : V → V := fun j => back (b j)
  have hf : 𝚺₁-Function₁[V] f := by dsimp [f]; definability
  letI := hf
  change ∃ W : V, Blocks 10 f N W
  apply blocks_exists 10 f N
  intro j hj
  have he : Exp.exp (10:V)=1024 := by
    rw [show (10:V)=9+1 by norm_num,exp_succ]
    have h9 : Exp.exp (9:V)=512 := by
      have h := ArithmeticStandardCasts.cast_exp (V:=V) 9
      norm_num at h
      exact h
    rw [h9]
    norm_num
  rw [he]
  exact lt_trans (back_bound (b j) (hb j hj)) (by norm_num)
#print axioms DirectBFSModelIndexMap.back_definable
#print axioms DirectBFSModelIndexMap.back_cast
#print axioms DirectBFSModelIndexMap.back_bound
#print axioms DirectBFSModelIndexMap.back_zero
#print axioms DirectBFSModelIndexMap.back_one
#print axioms DirectBFSModelIndexMap.represented
end DirectBFSModelIndexMap
