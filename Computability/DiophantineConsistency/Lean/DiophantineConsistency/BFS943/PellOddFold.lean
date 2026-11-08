import DiophantineConsistency.BFS943.PellFold

/-! Fold an arbitrary odd internal Pell index into the strong-index window. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositivePellOddFold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellPeriodicity ArithmeticPellResidueClasses ArithmeticPellHalfIndex
open TenPositivePellFold
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fold_odd_index (n s b : V) (hn : 0<n) (hs : s%2=1) :
    ∃ p : V, p≤n ∧ p%2=1 ∧
      SignMod (xcoord n b) (ycoord s b) (ycoord p b) := by
  have h2 : 0<(2:V) := by simp
  have h2n : 0<2*n := mul_pos h2 hn
  have hF : 0<xcoord n b := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x n b)
  let r : V := s%(2*n)
  have hr : r<2*n := mod_lt s h2n
  have hr2 : r%2=1 := by
    have hd : (2:V)∣2*n := dvd_mul_right 2 n
    have he : (s%(2*n))%2=s%2 := mod_reduce s 2 (2*n) h2 hd
    exact he.trans hs
  have hsign : SignMod (xcoord n b) (ycoord s b) (ycoord r b) := by
    have h := y_antiperiod_blocks (s/(2*n)) n r b
    rw [show 2*n*(s/(2*n))+r=s from div_add_mod s (2*n)] at h
    exact h
  rcases le_total r n with h|h
  · exact ⟨r,h,hr2,hsign⟩
  · let p : V := 2*n-r
    have hp : p≤n := by
      apply (tsub_le_iff_right).mpr
      simpa only [two_mul] using (_root_.add_le_add le_rfl h : n+n≤n+r)
    have hsum : r+p=2*n := add_tsub_cancel_of_le (le_of_lt hr)
    have hp2 : p%2=1 := by
      rcases mod_two p with h0|h1
      · have hmod : (r+p)%2=1 := by rw [mod_add h2,hr2,h0]; simp
        rw [hsum,mod_mul_self_right] at hmod
        exact False.elim (_root_.zero_ne_one hmod)
      · exact h1
    have he : ycoord r b%xcoord n b=ycoord p b%xcoord n b := by
      exact (y_reflected_mod n r b (le_of_lt hr)).symm
    exact ⟨p,hp,hp2,sign_trans hF hsign (Or.inl he)⟩

#print axioms TenPositivePellOddFold.fold_odd_index
end TenPositivePellOddFold
