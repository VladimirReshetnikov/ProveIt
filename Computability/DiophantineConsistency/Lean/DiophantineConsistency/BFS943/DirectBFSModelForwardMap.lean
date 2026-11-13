import DiophantineConsistency.BFS943.DirectBFSRowTransfer
import DiophantineConsistency.ArithmeticWangTable
import DiophantineConsistency.ArithmeticPackingBlocks
import DiophantineConsistency.Compact44.CleanGeometry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSModelForwardMap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWangTable ArithmeticPackingBlocks CleanGeometry
open DirectBFSConjugacyBase DirectBFSConjugacyLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def forward (x : V) : V := tabValue rowMap.toList 0 x
instance forward_definable : 𝚺₁-Function₁[V] forward := (tab_defined rowMap.toList 0).to_definable.of_zero

theorem forward_cast (i : ℕ) : forward (i:V)=(rowMap.getD i 0:V) := by
  unfold forward
  rw [tab_cast]
  simp only [List.getD_eq_getElem?_getD,Array.getElem?_toList,Array.getD_eq_getD_getElem?]

theorem forward_bound (x : V) (hx : x<943) : forward x<943 := by
  obtain ⟨i,hi,he⟩ := bounded_standard 943 x hx
  rw [he,forward_cast]
  exact_mod_cast (row_bounds hi).1

theorem forward_zero : forward (0:V)=0 := by
  rw [show (0:V)=((0:ℕ):V) by norm_num,forward_cast]
  have h : rowMap.getD 0 0=0 := by decide
  rw [h]

theorem forward_one : forward (1:V)=1 := by
  rw [show (1:V)=((1:ℕ):V) by norm_num,forward_cast]
  have h : rowMap.getD 1 0=1 := by decide
  rw [h]

theorem represented (b : V → V) [𝚺₁-Function₁[V] b] (N : V) (hb : ∀ j<N,b j<943) :
    ∃ W : V, Blocks 10 (fun j => forward (b j)) N W := by
  let f : V → V := fun j => forward (b j)
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
  exact lt_trans (forward_bound (b j) (hb j hj)) (by norm_num)
#print axioms DirectBFSModelForwardMap.forward_definable
#print axioms DirectBFSModelForwardMap.forward_cast
#print axioms DirectBFSModelForwardMap.forward_bound
#print axioms DirectBFSModelForwardMap.forward_zero
#print axioms DirectBFSModelForwardMap.forward_one
#print axioms DirectBFSModelForwardMap.represented
end DirectBFSModelForwardMap
