import Absorb89Window
import Absorb89Growth
import Absorb89Divisibility
import DirectMainPlusBranch

/-! The positive first-root branch forces the absorbed witness above s. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb89PositiveBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89 Absorb89First
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_growth (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    3*v 6≤v 8+v 9 := by
  obtain ⟨_,_,n,_,_,_,hn,_,_,_,_,hcoord,_⟩ := Absorb89Window.graph_early p v hb hl hh hv hz
  have hn3 : 3≤n := le_trans (by norm_num) hn
  exact Absorb89Growth.growth_of_index p v n hb hv hn3 hcoord

theorem positive_branch (p : Fin 4 → ℕ) (v : Fin 12 → V) (first : V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hnorm : let b : V := v 0*(p 0:V); let q : V := 1+b
      let X : V := q*v 5; let Y : V := (q*(q*q))*v 6
      let k : V := v 8+v 9; let ell : V := (X*Y)*(Y*k)
      first*first=1+ell*(ell+k))
    (hBtpos : let b : V := v 0*(p 0:V); let q : V := 1+b
      let A : V := (p 1:V)+v 5; let Bp : V := q*A
      let Bn : V := (v 1+v 2)*A+v 1
      0<q*(Bp-Bn))
    (hsign : let b : V := v 0*(p 0:V); let q : V := 1+b
      let X : V := q*v 5; let Y : V := (q*(q*q))*v 6
      let k : V := v 8+v 9; let ell : V := (X*Y)*(Y*k)
      let A : V := (p 1:V)+v 5; let Bp : V := q*A
      let Bn : V := (v 1+v 2)*A+v 1; let Bt : V := q*(Bp-Bn)
      b*(ell+k+v 7)=(1+k*b)*Bt+b*first) : v 6<v 7 := by
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
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := by dsimp [q,b]; simp
  have hX : 0<X := mul_pos hq (hv 5)
  have hY : 0<Y := mul_pos (mul_pos hq (mul_pos hq hq)) (hv 6)
  have hQ1 : 1≤Q := pos_iff_one_le.mp (mul_pos (mul_pos hX hY) hY)
  have hkell : k≤ell := by
    calc
      k≤Q*k := le_mul_of_one_le_left (by simp) hQ1
      _=ell := by dsimp [Q,ell]; ring
  have hthird := DirectMainPlusBranch.root_thirds ell k first hkell hnorm
  have hgrowth := graph_growth p v hb hl hh hv hz
  obtain ⟨t,ht⟩ := Absorb89Divisibility.graph_divisibility p v hb hv hz
  change Bt=b*t at ht
  have hbt : 1≤b*t := by
    apply pos_iff_one_le.mp
    rw [←ht]
    exact hBtpos
  have heq : ell+k+v 7=(1+k*b)*t+first := by
    apply mul_left_cancel₀ (ne_of_gt hb0)
    calc
      b*(ell+k+v 7)=(1+k*b)*Bt+b*first := hsign
      _=(1+k*b)*(b*t)+b*first := by rw [ht]
      _=b*((1+k*b)*t+first) := by ring
  exact DirectMainPlusBranch.positive_branch b t ell k first (v 6) (v 7) hbt hgrowth hthird heq

#print axioms Absorb89PositiveBranch.graph_growth
#print axioms Absorb89PositiveBranch.positive_branch
end Absorb89PositiveBranch
