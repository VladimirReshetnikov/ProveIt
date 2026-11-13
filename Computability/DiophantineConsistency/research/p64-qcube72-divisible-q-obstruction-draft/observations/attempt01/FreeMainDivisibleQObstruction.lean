import DiophantineConsistency.ArithmeticPellRecurrence

/-! Unchecked generic draft: a q divisible by 3 obstructs U|h. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainDivisibleQObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem not_dvd (q w s U g c h : V) (hq3 : (3:V)∣q) (hU : 0<U)
    (hnorm : let X := w*q
      let Y := q*q*q*s
      let a := X*Y+Y
      g*g=1+delta a*c*c)
    (hcar : let X := w*q
      let Y := q*q*q*s
      let a := X*Y+Y
      let H := 4*a+3
      U*g=U*(X+a*c)+H*h) : ¬U∣h := by
  let X : V := w*q
  let Y : V := q*q*q*s
  let a : V := X*Y+Y
  let H : V := 4*a+3
  change g*g=1+delta a*c*c at hnorm
  change U*g=U*(X+a*c)+H*h at hcar
  obtain ⟨r,hr⟩ := hq3
  have hx3 : (3:V)∣X := by
    refine ⟨w*r,?_⟩
    dsimp [X]
    rw [hr]
    ring
  have hy3 : (3:V)∣Y := by
    refine ⟨r*q*q*s,?_⟩
    dsimp [Y]
    rw [hr]
    ring
  obtain ⟨y,hy⟩ := hy3
  have ha3 : a=3*((X+1)*y) := by dsimp [a]; rw [hy]; ring
  have hH3 : H=3*(4*((X+1)*y)+1) := by dsimp [H]; rw [ha3]; ring
  have hD3 : delta a=3*((a+1)*((X+1)*y+1)) := by
    unfold delta
    rw [ha3]
    ring
  intro hdiv
  obtain ⟨t,ht⟩ := hdiv
  have hg : g=X+a*c+H*t := by
    apply mul_left_cancel₀ (ne_of_gt hU)
    calc
      U*g=U*(X+a*c)+H*h := hcar
      _=U*(X+a*c+H*t) := by rw [ht]; ring
  obtain ⟨x,hx⟩ := hx3
  have hg3 : (3:V)∣g := by
    refine ⟨x+((X+1)*y)*c+(4*((X+1)*y)+1)*t,?_⟩
    rw [hg,hx,ha3,hH3]
    ring
  have hsquare : (3:V)∣g*g := dvd_mul_of_dvd_left hg3 g
  have hterm : (3:V)∣delta a*c*c := by
    refine ⟨((a+1)*((X+1)*y+1))*c*c,?_⟩
    rw [hD3]
    ring
  have hone : (3:V)∣1 := by
    have hh : (3:V)∣1+delta a*c*c := by rw [←hnorm]; exact hsquare
    exact (dvd_add_left hterm).mp hh
  have hbad : (3:V)≤1 := Arithmetic.le_of_dvd (by norm_num) hone
  exact (not_le_of_gt (by norm_num : (1:V)<3)) hbad

#print axioms not_dvd
end FreeMainDivisibleQObstruction
