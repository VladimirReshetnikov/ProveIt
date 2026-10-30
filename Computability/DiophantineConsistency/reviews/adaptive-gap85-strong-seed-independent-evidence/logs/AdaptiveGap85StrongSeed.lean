import DiophantineConsistency.ArithmeticPellSquaredSeed
import DiophantineConsistency.ArithmeticPellCongruences

/-! A positive strong-factor seed at the special ordinate c=a+1. This is
arithmetic only; it does not claim that the full 85 literal has a zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85StrongSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellSquaredSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every a has positive f and i satisfying the strong norm with c=a+1. -/
theorem strong_seed_at_successor (a : V) :
    let c := a+1
    ∃ f i : V, 0<f ∧ 0<i ∧
      (c*c*i)*(c*c*i)+delta a=delta a*(f*f) := by
  let c : V := a+1
  have hc : 0<c := by dsimp [c]; simp
  have hdiv : c∣a+1 := by dsimp [c]; exact dvd_refl _
  obtain ⟨r,s,_,hy⟩ := residue_quotients c a c hdiv
  obtain ⟨f,j,hf,hj,_,_,hn⟩ := strong_seed c a hc
  let i : V := delta a*j*(1+s)*(1+s)
  have hd : 0<delta a := by
    rw [delta]
    exact mul_pos (by simp) (by simp)
  have hi : 0<i := by
    dsimp [i]
    exact mul_pos (mul_pos (mul_pos hd hj) (by simp)) (by simp)
  refine ⟨f,i,hf,hi,?_⟩
  rw [hn,hy]
  dsimp [i]
  ring
end DiophantineConsistency.AdaptiveGap85StrongSeed
