import DiophantineConsistency.FreeJEarlyIndex
import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeJIndexComparison
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011
open DiophantineConsistency.Ordinary12FreeJ
open FreeJRootBinding FreeJPellIndices FreeJEarlyIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def Bound (p : Fin 4 → ℕ) (v : Fin 12 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let M : V := (q*(q*q))*(v 0*(p 0:V))
  let U : V := v 6*(q*q)
  let Q : V := (v 5*v 6)*v 6
  let k : V := v 8+v 9
  let c : V := v 8+v 6*k
  let a : V := v 5*v 6+v 6
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  ∃ first main n m : V, 0<first ∧ 0<main ∧ 13≤n ∧ n<m ∧ 14≤m ∧ 2*R<c ∧
    magnitude (pairEval (core (fun j => (p j:ℤ))).z v)=M*first ∧
    Equivalent (pairEval (core (fun j => (p j:ℤ))).d v) (natural (U*main)) ∧
    xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
    xcoord m a=main ∧ ycoord m a=c ∧ (2*n)%(q^4)=R+1

theorem comparison_of_facts (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hv : ∀j,0<v j) (hY : 2≤v 6) (hi : FreeJIndices p v) (he : FreeJEarlyIndex.Bound p v) : Bound p v := by
  let E : V := v 5*v 6
  let Y : V := v 6
  let Q : V := E*Y
  let B : V := 2*(Q-1)+1
  let k : V := v 8+v 9
  let c : V := v 8+Y*k
  let a : V := E+Y
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have hE : 0<E := mul_pos (hv 5) (hv 6)
  have hk : 0<k := add_pos (hv 8) (hv 9)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp (mul_pos hE (hv 6)))
  have hB : B+2=2*Q+1 := by
    dsimp [B]
    calc
      2*(Q-1)+1+2=2*(Q-1+1)+1 := by ring
      _=2*Q+1 := by rw [hQ1]
  have hab : a≤B := by
    have hEsub : E-1+1=E := tsub_add_cancel_of_le (pos_iff_one_le.mp hE)
    have hYsub : Y-2+2=Y := tsub_add_cancel_of_le hY
    have heq : a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=B+2 := by
      rw [hB]
      calc
        a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=
          (E-1+1)+(Y-2+2)+2+(E-1)*(2*(Y-2)+3)+(Y-2) := by rw [hEsub,hYsub]
        _=2*((E-1+1)*(Y-2+2))+1 := by ring
        _=2*Q+1 := by rw [hEsub,hYsub]
    have heq' : a+2≤B+2 := by rw [←heq]; simp
    exact (add_le_add_iff_right (2:V)).mp heq'
  obtain ⟨first,n,hfirst,hn13,_,hroot,hnx,hny,hnmod,_,hRk⟩ := he
  obtain ⟨_,main,_,m,_,hmain,_,_,_,_,_,horient,_,_,hmx,hmy⟩ := hi
  change 2*ycoord n B=k at hny
  change ycoord m a=c at hmy
  have hkc : k<c := calc
    k≤k*Y := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1:V)≤2) hY)
    _<k*Y+v 8 := lt_add_of_pos_right _ (hv 8)
    _=c := by dsimp [c]; ring
  have hnm : n<m := by
    by_contra hn
    have hm : m≤n := le_of_not_gt hn
    have hc : c≤k := calc
      c=ycoord m a := hmy.symm
      _≤ycoord n a := (y_strictMono a).monotone hm
      _≤ycoord n B := (base_mono a B hab n).2
      _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
      _=k := hny
    exact (not_le_of_gt hkc) hc
  have hm14 : 14≤m := by
    have h := le_trans (_root_.add_le_add hn13 (le_refl (1:V))) (lt_iff_succ_le.mp hnm)
    simpa only [show (13:V)+1=14 by ring] using h
  have hhalf : 2*R<c := calc
    2*R<2*(R+1) := mul_lt_mul_of_pos_left (lt_add_one R) (by simp)
    _≤2*k := mul_le_mul_of_nonneg_left hRk (by simp)
    _≤k*Y := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hY (Arithmetic.zero_le k)
    _<k*Y+v 8 := lt_add_of_pos_right _ (hv 8)
    _=c := by dsimp [c]; ring
  exact ⟨first,main,n,m,hfirst,hmain,hn13,hnm,hm14,hhalf,hroot,horient,hnx,hny,hmx,hmy,hnmod⟩


/-- The two Pell indices are ordered before the strong norm is recovered. -/
theorem comparison (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) : Bound p v := by
  have hq : 1<1+v 0*(p 0:V) := lt_add_of_pos_right _ (mul_pos (hv 0) hb)
  obtain ⟨s,hs⟩ := first_factor_forces_Y_divisible p v hz (hv 0) hb
  have hspos : 0<s := pos_of_mul_pos_right (by rw [←hs]; exact hv 6) (by simp)
  have hYquotient : ∃ s : V, 0<s ∧ v 6=(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*s := by
    refine ⟨s,hspos,?_⟩
    rw [hs]
    congr 1 <;> ring
  have hY := two_le_of_positive_cube_quotient hq hYquotient
  exact comparison_of_facts p v hv hY (indices p v hb hv hz) (early_index p v hb hl hh hv hz)

end FreeJIndexComparison
#print axioms FreeJIndexComparison.comparison_of_facts
#print axioms FreeJIndexComparison.comparison
