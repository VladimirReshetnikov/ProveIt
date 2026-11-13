import DiophantineConsistency.Compact44.Absorb89Signs

/-! Divisibility of the first-factor transport term in either sign branch. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb89Divisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89 Absorb89First
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveFirstDivisibility2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem divisor_of_branches (b Bt L first k : V) (hb : 0<b)
    (h : b*L=(1+k*b)*Bt+b*first ∨ b*L+b*first=(1+k*b)*Bt) : b∣Bt := by
  have hmod (z : V) : (b*z)%b=0 := by rw [mul_comm]; exact mod_mul_self_left _ _
  have hright : (1+k*b)*Bt=Bt+b*(k*Bt) := by ring
  have hzero : Bt%b=0 := by
    rcases h with hp | hn
    · have hr : (1+k*b)*Bt+b*first=Bt+b*(k*Bt+first) := by ring
      have hm := congrArg (fun z : V => z%b) hp
      rw [hr,mod_add_mul' _ _ hb,hmod] at hm
      exact hm.symm
    · have hl : b*L+b*first=b*(L+first) := by ring
      have hm := congrArg (fun z : V => z%b) hn
      rw [hl,hright,mod_add_mul' _ _ hb,hmod] at hm
      exact hm.symm
  exact mod_eq_zero_iff_dvd.mp hzero

theorem graph_divisibility (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    b∣q*(Bp-Bn) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let ell : V := (X*Y)*(Y*k)
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let Bt : V := q*(Bp-Bn)
  have hb0 : 0<b := mul_pos (hv 0) hb
  obtain ⟨first,_,_,_,h⟩ := Absorb89Signs.first_branches p v hb hv hz
  exact divisor_of_branches b Bt (ell+k+v 7) first k hb0 h

#print axioms Absorb89Divisibility.divisor_of_branches
#print axioms Absorb89Divisibility.graph_divisibility
end Absorb89Divisibility
