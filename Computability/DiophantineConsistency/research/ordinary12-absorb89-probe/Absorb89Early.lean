import Absorb89Rank
import DiophantineConsistency.ArithmeticPellCongruences

/-! Early-index congruence from a draft zero, conditional on the radix window. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb89Early
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticPellRecurrence
open ArithmeticPellCongruences ArithmeticAdaptiveFirstDivisibility2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem early_of_window (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (Absorb89First.integerPorts p)).output v)
    (hw : let b : V := v 0*(p 0:V); let q : V := 1+b;
      let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q);
      24≤R ∧ R+q^3+q+1≤q^4) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let c : V := v 8+Y*k
    let a : V := X*Y+Y
    let Q : V := (X*Y)*Y
    let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
    ∃ first main n m : V, 0<first ∧ 0<main ∧ 13≤n ∧ 0<m ∧ n≤k ∧ m≤c ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c ∧ (2*n)%(q^4)=R+1 ∧ R+1≤2*n ∧ R+1≤k := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let c : V := v 8+Y*k
  let a : V := X*Y+Y
  let Q : V := (X*Y)*Y
  let B : V := 2*(Q-1)+1
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hq : 0<q := by dsimp [q,b]; simp
  have hX : 0<X := mul_pos hq (hv 5)
  have hY : 0<Y := mul_pos (mul_pos hq (mul_pos hq hq)) (hv 6)
  have hQ : 0<Q := mul_pos (mul_pos hX hY) hY
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : B+1=2*Q := by
    dsimp [B]
    calc
      2*(Q-1)+1+1=2*(Q-1+1) := by ring
      _=2*Q := by rw [hQ1]
  have hy : Y=q^3*v 6 := by dsimp [Y]; ring
  have hdiv : q^4∣B+1 := by
    rw [hB]
    refine ⟨2*X*(q*q)*(v 6)*(v 6),?_⟩
    dsimp [Q]; rw [hy]; ring
  obtain ⟨first,main,n,m,hfirst,hmain,_,_,hm,hnk,hmc,hnx,hny,hmx,hmy⟩ :=
    Absorb89Indices.graph_indices p v hb hv hz
  have hc : q^4∣magnitude (R+1,k) := Absorb89Rank.graph_rank p v hb hv hz
  obtain ⟨hR24,hupper⟩ := hw
  have hmod : 0<q^4 := pow_pos hq _
  have hRlt : R+1<q^4 := by
    have hp : 0<q^3+q := add_pos (pow_pos hq _) hq
    calc
      R+1<(R+1)+(q^3+q) := lt_add_of_pos_right _ hp
      _=R+q^3+q+1 := by ring
      _≤q^4 := hupper
  have hres : (R+1)%(q^4)=k%(q^4) := magnitude_mod (R+1,k) (q^4) hmod hc
  rw [mod_eq_self_of_lt hRlt] at hres
  obtain ⟨r,t,_,hy'⟩ := residue_quotients n B (q^4) hdiv
  change 2*ycoord n B=k at hny
  have hk : k=2*n+q^4*(2*t) := by rw [←hny,hy']; ring
  have hnmod : (2*n)%(q^4)=R+1 := by
    rw [hk,mod_add_mul' _ _ hmod] at hres
    exact hres.symm
  have hnlow : R+1≤2*n := by rw [←hnmod]; exact mod_le _ _
  have hklow : R+1≤k := by rw [hres]; exact mod_le _ _
  have hn13 : 13≤n := by
    have htwelve : (2:V)*12<2*n := by
      rw [show (2:V)*12=24 by ring]
      exact lt_of_le_of_lt hR24 (lt_of_lt_of_le (lt_add_one R) hnlow)
    have h12 : (12:V)<n := lt_of_mul_lt_mul_left htwelve (by simp)
    simpa only [show (12:V)+1=13 by ring] using lt_iff_succ_le.mp h12
  exact ⟨first,main,n,m,hfirst,hmain,hn13,hm,hnk,hmc,hnx,hny,hmx,hmy,hnmod,hnlow,hklow⟩

#print axioms Absorb89Early.early_of_window
end Absorb89Early
