import DiophantineConsistency.ArithmeticPellResidueClasses

/-! Exact odd-block Pell anti-period at arbitrary internal indices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74PellOddAntiperiod
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellPeriodicity ArithmeticPellResidueClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For every internal number of odd blocks, the shifted ordinate has
the opposite residue modulo the even-time Pell abscissa. -/
theorem odd_blocks_antiperiod (a t r s : V) :
    (ycoord (r+4*t*(2*s+1)) a+ycoord r a)%xcoord (2*t) a=0 := by
  let f := xcoord (2*t) a
  have hf : 0<f := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x (2*t) a)
  have hx : xcoord (4*t) a+1=2*f*f := by
    simpa only [show (4:V)*t=2*(2*t) by ring,f] using double_x_add_one (2*t) a
  have hy : ycoord (4*t) a=2*f*ycoord (2*t) a := by
    simpa only [show (4:V)*t=2*(2*t) by ring,f] using double_y (2*t) a
  have he : ycoord (r+4*t) a+ycoord r a=
      f*(2*(f*ycoord r a+ycoord (2*t) a*xcoord r a)) := by
    calc
      ycoord (r+4*t) a+ycoord r a=
          ycoord r a*(xcoord (4*t) a+1)+xcoord r a*ycoord (4*t) a := by
            rw [(addition r (4*t) a).2]; ring
      _=f*(2*(f*ycoord r a+ycoord (2*t) a*xcoord r a)) := by rw [hx,hy]; ring
  have hbase : (ycoord (r+4*t) a+ycoord r a)%f=0 := by
    rw [he,mod_mul_self_right]
  have hp := (period_mod s (2*t) (r+4*t) a).2
  change ycoord (4*(2*t)*s+(r+4*t)) a%f=ycoord (r+4*t) a%f at hp
  have hsum := mod_add_congr _ _ (ycoord r a) f hf hp
  rw [hbase] at hsum
  have hidx : 4*(2*t)*s+(r+4*t)=r+4*t*(2*s+1) := by ring
  simpa only [hidx] using hsum

#print axioms Trace74PellOddAntiperiod.odd_blocks_antiperiod
end Trace74PellOddAntiperiod
