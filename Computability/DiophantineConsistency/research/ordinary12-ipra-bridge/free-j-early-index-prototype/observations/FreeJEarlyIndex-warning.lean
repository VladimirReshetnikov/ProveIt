import DiophantineConsistency.FreeJPellIndices
import DiophantineConsistency.FreeJEarlyWindow
import DiophantineConsistency.ArithmeticAdaptiveEarlyIndex2011
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeJEarlyIndex
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellCongruences
open DiophantineConsistency.Ordinary12FreeJ
open FreeJRootBinding FreeJPellIndices FreeJEarlyWindow FreeJMainOrientation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def FreeJEarlyIndex (p : Fin 4 → ℕ) (v : Fin 12 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let M : V := (q*(q*q))*(v 0*(p 0:V))
  let Q : V := (v 5*v 6)*v 6
  let k : V := v 8+v 9
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  ∃ first n : V, 0<first ∧ 13≤n ∧ n≤k ∧
    magnitude (pairEval (core (fun j => (p j:ℤ))).z v)=M*first ∧
    xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
    (2*n)%(q^4)=R+1 ∧ R+1≤2*n ∧ R+1≤k

theorem early_index_of_facts (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hq : 0<1+v 0*(p 0:V)) (hv : ∀j,0<v j)
    (hY : ∃s:V, v 6=((1+v 0*(p 0:V))^3)*s)
    (hi : FreeJIndices p v)
    (hw : let q : V := 1+v 0*(p 0:V); let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0; 24≤R ∧ R+q^3+q+1≤q^4)
    (hc : FreeJRankCongruence p v) : FreeJEarlyIndex p v := by
  let q : V := 1+v 0*(p 0:V)
  let Q : V := (v 5*v 6)*v 6
  let B : V := 2*(Q-1)+1
  let k : V := v 8+v 9
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have hQ : 0<Q := mul_pos (mul_pos (hv 5) (hv 6)) (hv 6)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : B+1=2*Q := by
    dsimp [B]
    calc
      2*(Q-1)+1+1=2*(Q-1+1) := by ring
      _=2*Q := by rw [hQ1]
  obtain ⟨s,hs⟩ := hY
  have hdiv : q^4∣B+1 := by
    rw [hB]
    refine ⟨2*v 5*(q*q)*s*s,?_⟩
    dsimp [Q]; rw [hs]; ring
  obtain ⟨first,main,n,m,hfirst,_,_,_,hnk,_,hroot,_,hnx,hny,_,_⟩ := hi
  obtain ⟨hR24,hupper⟩ := hw
  have hm : 0<q^4 := pow_pos hq _
  have hRlt : R+1<q^4 := by
    have hp : 0<q^3+q := add_pos (pow_pos hq _) hq
    calc
      R+1<(R+1)+(q^3+q) := lt_add_of_pos_right _ hp
      _=R+q^3+q+1 := by ring
      _≤q^4 := hupper
  have hres : (R+1)%(q^4)=k%(q^4) := magnitude_mod (R+1,k) (q^4) hm hc
  rw [mod_eq_self_of_lt hRlt] at hres
  obtain ⟨r,t,_,hy⟩ := residue_quotients n B (q^4) hdiv
  change 2*ycoord n B=k at hny
  have hk : k=2*n+q^4*(2*t) := by rw [←hny,hy]; ring
  have hnmod : (2*n)%(q^4)=R+1 := by
    rw [hk,mod_add_mul' _ _ hm] at hres
    exact hres.symm
  have hnlow : R+1≤2*n := by rw [←hnmod]; exact mod_le _ _
  have hklow : R+1≤k := by rw [hres]; exact mod_le _ _
  have hn13 : 13≤n := by
    have htwelve : (2:V)*12<2*n := by
      rw [show (2:V)*12=24 by ring]
      exact lt_of_le_of_lt hR24 (lt_of_lt_of_le (lt_add_one R) hnlow)
    have h12 : (12:V)<n := lt_of_mul_lt_mul_left htwelve (by simp)
    simpa only [show (12:V)+1=13 by ring] using lt_iff_succ_le.mp h12
  exact ⟨first,n,hfirst,hn13,hnk,hroot,hnx,hny,hnmod,hnlow,hklow⟩


theorem early_index (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) : FreeJEarlyIndex p v := by
  have hq : 0<1+v 0*(p 0:V) := by simp
  exact early_index_of_facts p v hq hv (first_factor_forces_Y_divisible p v hz (hv 0) hb)
    (indices p v hb hv hz) (early_window p v hb hl hh hv hz) (rank_congruence p v hb hv hz)

end FreeJEarlyIndex
#print axioms FreeJEarlyIndex.early_index_of_facts
#print axioms FreeJEarlyIndex.early_index
