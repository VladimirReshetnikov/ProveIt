import FirstRootGap
import DiophantineConsistency.Compact44.P72Root

/-! Source-only natural fresh-parent-root fact. No graph zero, port bound,
Lean elaboration or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FreshParentRootDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive b,t and the first-root gap admit a positive fresh root with
the exact subtraction-free balance required by the parent ring cut. -/
theorem fresh_root (m k s tau b t : V) (hb : 0<b) (ht : 0<t)
    (hgap : m*k+s<tau) :
    ∃ r : V, 0<r ∧ r+(m*k+k+s)=k*(b*t)+t+tau := by
  let A := m*k+k+s
  let B := k*(b*t)+t+tau
  have hbt : 0<b*t := mul_pos hb ht
  have hbt1 : 1≤b*t := pos_iff_one_le.mp hbt
  have hk : k≤k*(b*t) := le_mul_of_one_le_right (Arithmetic.zero_le k) hbt1
  have hAB : A<B := by dsimp [A,B]; nlinarith
  refine ⟨B-A,tsub_pos_of_lt hAB,?_⟩
  have he : B-A+A=B := tsub_add_cancel_of_le (le_of_lt hAB)
  simpa only [A,B] using he

end DiophantineConsistency.FreshParentRootDraft

#print axioms DiophantineConsistency.FreshParentRootDraft.fresh_root
