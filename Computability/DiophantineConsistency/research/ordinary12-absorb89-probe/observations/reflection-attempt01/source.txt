import Absorb89Signs
import DirectMainReflect

/-! Bind the negative-sign witness reflection to the speculative graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb89Reflection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89 Absorb89First
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reflected_branch (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
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
    ∃ first : V, 0<first ∧ 0<Bt ∧ first*first=1+ell*(ell+k) ∧
      (b*(ell+k+v 7)=(1+k*b)*Bt+b*first ∨
       ∃ rnew : V, v 6<rnew ∧ rnew=v 7+2*first ∧
         b*(ell+k+rnew)=(1+k*b)*Bt+b*first) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let Q : V := (X*Y)*Y
  let ell : V := (X*Y)*(Y*k)
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let Bt : V := q*(Bp-Bn)
  have hq : 0<q := by dsimp [q,b]; simp
  have hq1 : 1≤q := pos_iff_one_le.mp hq
  have hX : 0<X := mul_pos hq (hv 5)
  have hX1 : 1≤X := pos_iff_one_le.mp hX
  have hY : 0<Y := mul_pos (mul_pos hq (mul_pos hq hq)) (hv 6)
  have hY1 : 1≤Y := pos_iff_one_le.mp hY
  have hk : 0<k := add_pos (hv 8) (hv 9)
  have hk1 : 1≤k := pos_iff_one_le.mp hk
  have hQ : 0<Q := mul_pos (mul_pos hX hY) hY
  have hQ1 : 1≤Q := pos_iff_one_le.mp hQ
  have hklell : k≤ell := by
    calc
      k≤Q*k := le_mul_of_one_le_left (by simp) hQ1
      _=ell := by dsimp [Q,ell]; ring
  have hqcube : 1≤q*(q*q) := by
    have h := mul_le_mul hq1 (mul_le_mul hq1 hq1 (by simp) (by simp)) (by simp) (by simp)
    simpa only [one_mul] using h
  have hsY : v 6≤Y := by
    dsimp [Y]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hqcube (show (0:V)≤v 6 by simp)
  have hYell : Y≤ell := by
    calc
      Y≤Y*Y := le_mul_of_one_le_right (by simp) hY1
      _≤X*(Y*Y) := le_mul_of_one_le_left (by simp) hX1
      _≤(X*(Y*Y))*k := le_mul_of_one_le_right (by simp) hk1
      _=ell := by dsimp [ell]; ring
  have hs : v 6≤ell := le_trans hsY hYell
  obtain ⟨first,hfirst,hBtpos,hnorm,hbranch⟩ := Absorb89Signs.first_branches p v hb hv hz
  have hn : first*first=1+ell*(ell+k) := by
    calc
      first*first=1+Q*(Q+1)*k*k := hnorm
      _=1+ell*(ell+k) := by dsimp [Q,ell]; ring
  refine ⟨first,hfirst,hBtpos,hn,?_⟩
  rcases hbranch with hp | hn'
  · exact Or.inl hp
  · right
    have hthird := DirectMainPlusBranch.root_thirds ell k first hklell hn
    have hscale : 3*ell<3*first := lt_of_le_of_lt (by simp) hthird
    have hfirstgt : ell<first := lt_of_mul_lt_mul_left hscale (by simp)
    have hsfirst : v 6<first := lt_of_le_of_lt hs hfirstgt
    have hr2 : v 6<v 7+2*first := by
      apply lt_of_lt_of_le hsfirst
      calc
        first≤first+first := by simp
        _≤v 7+(first+first) := by simp
        _=v 7+2*first := by ring
    have heq2 : b*(ell+k+(v 7+2*first))=(1+k*b)*Bt+b*first := by
      calc
        _=(b*(ell+k+v 7)+b*first)+b*first := by ring
        _=(1+k*b)*Bt+b*first := by rw [hn']
    exact ⟨v 7+2*first,hr2,rfl,heq2⟩

#print axioms Absorb89Reflection.reflected_branch
end Absorb89Reflection
