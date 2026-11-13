import Trace74CoupledPellPositiveShift
import DiophantineConsistency.ArithmeticPellPigeonhole
import DiophantineConsistency.ArithmeticPellStrongDivisibility

/-! Construct a divisible strong Pell seed at one internal index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoupledPellStrongSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellPeriodicity
open ArithmeticPellPigeonhole ArithmeticPellStrongDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The same positive Pell index is divisible by c and its ordinate by
`c²*tau`; its doubled abscissa and scaled ordinate satisfy the strong norm. -/
theorem exists_strong_seed (a c tau : V) (hc : 0<c) (htau : 0<tau) :
    ∃ t i : V, 0<t ∧ 0<i ∧ c∣t ∧
      ycoord t a=(c*c*tau)*i ∧
      let f := xcoord (2*t) a
      let I := delta a*ycoord (2*t) a
      2≤I ∧ c∣I ∧ f%c=(1:V)%c ∧ I*I+delta a=delta a*f*f := by
  have hm : 0<c*c*tau := mul_pos (mul_pos hc hc) htau
  obtain ⟨t0,ht0,hdiv⟩ := ordinate_dvd a (c*c*tau) hm
  let t := c*t0
  have ht : 0<t := mul_pos hc ht0
  have htt : t0∣t := by refine ⟨c,?_⟩; dsimp [t]; ring
  have hyt : ycoord t0 a∣ycoord t a := (y_dvd_iff a t0 t).mpr htt
  obtain ⟨i,hi⟩ := dvd_trans hdiv hyt
  have hiy : ycoord t a=(c*c*tau)*i := hi
  have hypos : 0<ycoord t a := lt_of_lt_of_le ht (time_le_y t a)
  have hip : 0<i := by
    by_contra hn
    have hz : i=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [hz,mul_zero] at hiy
    exact (ne_of_gt hypos) hiy
  have hct : c∣t := ⟨t0,rfl⟩
  have hcY : c∣ycoord t a := by
    refine ⟨c*tau*i,?_⟩
    rw [hiy]; ring
  let f := xcoord (2*t) a
  let I := delta a*ycoord (2*t) a
  have hd1 : 1≤delta a := by
    apply pos_iff_one_le.mp
    unfold delta
    positivity
  have ht1 : 1≤t := pos_iff_one_le.mp ht
  have hy2 : 2≤ycoord (2*t) a := by
    have ht2 : (2:V)≤2*t := by
      simpa using mul_le_mul_of_nonneg_left ht1 (show (0:V)≤2 by simp)
    exact le_trans ht2 (time_le_y (2*t) a)
  have hI : 2≤I := by
    dsimp [I]
    exact le_trans hy2 (le_mul_of_one_le_left (by simp) hd1)
  have hcI : c∣I := by
    obtain ⟨u,hu⟩ := hcY
    refine ⟨delta a*(2*xcoord t a*u),?_⟩
    dsimp [I]
    rw [double_y,hu]
    ring
  have hfmod : f%c=(1:V)%c := by
    obtain ⟨u,hu⟩ := hcY
    have hfshape : f=1+c*(2*delta a*u*ycoord t a) := by
      dsimp [f]
      rw [double_x,hu]
      ring
    rw [hfshape,mod_add_mul' _ _ hc]
  have hnorm : I*I+delta a=delta a*f*f := by
    dsimp [I,f]
    have he := norm (2*t) a
    calc
      (delta a*ycoord (2*t) a)*(delta a*ycoord (2*t) a)+delta a =
          delta a*(1+delta a*ycoord (2*t) a*ycoord (2*t) a) := by ring
      _=delta a*(xcoord (2*t) a*xcoord (2*t) a) := by rw [he]
      _=delta a*xcoord (2*t) a*xcoord (2*t) a := by ring
  exact ⟨t,i,ht,hip,hct,hiy,hI,hcI,hfmod,hnorm⟩

#print axioms Trace74CoupledPellStrongSeed.exists_strong_seed
end Trace74CoupledPellStrongSeed
