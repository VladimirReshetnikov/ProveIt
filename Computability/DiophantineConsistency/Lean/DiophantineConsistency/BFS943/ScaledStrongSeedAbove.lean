import DiophantineConsistency.BFS943.PellOrdinateAbove
import DiophantineConsistency.ArithmeticPellPeriodicity

/-! Internal scaled strong Pell seed with the first root in its ordinate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositiveScaledStrongSeedAbove
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence TenPositivePellOrdinateAbove ArithmeticPellPeriodicity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem strong_seed_above (a c tau L : V) (hc : 0<c) (htau : 0<tau) :
    ∃ m i f : V, L<m ∧ 0<i ∧ 0<f ∧
      ycoord m a=(i*c*c)*tau ∧ f=xcoord m a ∧
      f*f=1+ArithmeticPellRecurrence.delta a*(i*c*c)*(i*c*c)*tau*tau ∧
      xcoord (2*m) a=1+2*ArithmeticPellRecurrence.delta a*(i*c*c)*(i*c*c)*tau*tau ∧
      ycoord (2*m) a=(i*c*c)*(2*tau*f) := by
  let N:=c*c*tau
  have hN : 0<N := mul_pos (mul_pos hc hc) htau
  obtain ⟨m,hmL,hdiv⟩ := ordinate_dvd_above a N L hN
  have hm : 0<m := lt_of_le_of_lt (by simp) hmL
  obtain ⟨i,hi⟩ := hdiv
  have hy : 0<ycoord m a := lt_of_lt_of_le hm (time_le_y m a)
  have hi0 : 0<i := by
    apply pos_of_mul_pos_right (a:=N) _ (by simp)
    rw [←hi]
    exact hy
  have hyi : ycoord m a=(i*c*c)*tau := by
    rw [hi]
    dsimp [N]
    ring
  let f:=xcoord m a
  have hf : 0<f := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x m a)
  have hnorm : f*f=1+ArithmeticPellRecurrence.delta a*(i*c*c)*(i*c*c)*tau*tau := by
    have hh := norm m a
    rw [hyi] at hh
    dsimp [f]
    calc
      xcoord m a*xcoord m a=1+ArithmeticPellRecurrence.delta a*((i*c*c)*tau)*((i*c*c)*tau) := hh
      _=1+ArithmeticPellRecurrence.delta a*(i*c*c)*(i*c*c)*tau*tau := by ring
  have hx : xcoord (2*m) a=1+2*ArithmeticPellRecurrence.delta a*(i*c*c)*(i*c*c)*tau*tau := by
    rw [double_x,hyi]
    ring
  have hy2 : ycoord (2*m) a=(i*c*c)*(2*tau*f) := by
    rw [double_y,hyi]
    dsimp [f]
    ring
  exact ⟨m,i,f,hmL,hi0,hf,hyi,rfl,hnorm,hx,hy2⟩

#print axioms TenPositiveScaledStrongSeedAbove.strong_seed_above
end TenPositiveScaledStrongSeedAbove
