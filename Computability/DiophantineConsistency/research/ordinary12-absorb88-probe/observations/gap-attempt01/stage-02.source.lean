import Absorb88Divisibility

/-! The positive signed branch has enough room for inverse transport, conditionally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb88Gap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_gap (p : Fin 4 → ℕ) (v : Fin 12 → V) (first : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v)
    (hbound : (v 1+v 2)*((p 1:V)+v 5)+v 1 < (1+v 0*(p 0:V))*((p 1:V)+v 5))
    (hnorm : let b : V := v 0*(p 0:V); let q : V := 1+b
      let X : V := q*v 5; let Y : V := (q*(q*q))*v 6
      let k : V := v 8+v 9; let ell : V := (X*Y)*(Y*k)
      first*first=1+ell*(ell+k))
    (hBtpos : let b : V := v 0*(p 0:V); let q : V := 1+b
      let A : V := (p 1:V)+v 5; let Bp : V := q*A
      let Bn : V := (v 1+v 2)*A+v 1
      0<q*(Bp-Bn))
    (hsign : let b : V := v 0*(p 0:V); let q : V := 1+b
      let k : V := v 8+v 9
      let A : V := (p 1:V)+v 5; let Bp : V := q*A
      let Bn : V := (v 1+v 2)*A+v 1; let Bt : V := q*(Bp-Bn)
      b*v 7=(1+k*b)*Bt+b*first) :
    let q : V := 1+v 0*(p 0:V)
    let X : V := q*v 5; let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9; let ell : V := (X*Y)*(Y*k)
    ell+k<v 7 := by
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
  have hsquare : ell*ell<first*first := by
    calc
      ell*ell≤ell*(ell+k) := mul_le_mul_of_nonneg_left (by simp) (by simp)
      _<1+ell*(ell+k) := by simp
      _=first*first := hnorm.symm
  have hfirst : ell<first := lt_of_mul_self_lt_mul_self₀ (by simp) hsquare
  obtain ⟨t,ht⟩ := Absorb88Divisibility.graph_divisibility p v hb hv hz hbound
  change Bt=b*t at ht
  have hbt : 1≤b*t := by apply pos_iff_one_le.mp; rw [←ht]; exact hBtpos
  have hkt : k≤(1+k*b)*t := by
    calc
      k=k*1 := by ring
      _≤k*(b*t) := mul_le_mul_of_nonneg_left hbt (by simp)
      _≤k*(b*t)+t := by simp
      _=(1+k*b)*t := by ring
  have heq : v 7=(1+k*b)*t+first := by
    apply mul_left_cancel₀ (ne_of_gt hb0)
    calc
      b*v 7=(1+k*b)*Bt+b*first := hsign
      _=(1+k*b)*(b*t)+b*first := by rw [ht]
      _=b*((1+k*b)*t+first) := by ring
  calc
    ell+k<first+(1+k*b)*t := add_lt_add_of_lt_of_le hfirst hkt
    _=v 7 := by rw [heq]; ring

#print axioms Absorb88Gap.positive_gap
end Absorb88Gap
