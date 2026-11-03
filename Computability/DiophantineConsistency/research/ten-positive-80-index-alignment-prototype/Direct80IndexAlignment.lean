import Direct80FirstIndexResidue
import Direct80RankExact
import DiophantineConsistency.ArithmeticPellFirstIndex

/-! Noncircular comparison and exact first/main index alignment. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80IndexAlignment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellFirstIndex
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80Pell
open TenPositive80RankExact TenPositive80FirstIndexResidue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_main_alignment (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbeta : ∃u : V, (p 0:V)=2*u+1) :
    ∃ n : V, 0<n ∧ n<rankNat p v ∧ 2*n=rankNat p v+1 ∧
      2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      c p v=ycoord (rankNat p v) (A p v-1) := by
  let P : V := firstParam p v
  let S : V := mu p v*Y p v
  let A0 : V := A p v
  let B : V := 2*(P-1)+1
  let R : V := rankNat p v
  let M : V := mu p v*mu p v
  obtain ⟨n,hn,hny,hres⟩ := graph_first_index_residue p v hb hl hh hv hz hbeta
  obtain ⟨_hRlo,hwindow,_hRodd,hc⟩ := graph_rank_exact p v hb hl hh hv hz
  change 2*ycoord n B=k v at hny
  change (2*n)%M=(R+1)%M at hres
  change c p v=ycoord R (A0-1) at hc
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hS : 0<S := mul_pos hmu hY
  have hS1 : 1≤S := pos_iff_one_le.mp hS
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hP : 0<P := mul_pos hX (mul_pos hS hS)
  have hA : 0<A0 := mul_pos hS (add_pos hX (by simp))
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hA1 : A0-1+1=A0 := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hXP : X p v+1≤2*X p v := by
    calc
      X p v+1≤X p v+X p v := by simpa only [add_comm] using _root_.add_le_add_left hX1 (X p v)
      _=2*X p v := by ring
  have hSsq : S≤S*S := le_mul_of_one_le_right (by simp) hS1
  have hA2P : A0≤2*P := calc
    A0=S*(X p v+1) := rfl
    _≤S*(2*X p v) := mul_le_mul_of_nonneg_left hXP (by simp)
    _≤(S*S)*(2*X p v) := mul_le_mul_of_nonneg_right hSsq (by simp)
    _=2*P := by dsimp [P,firstParam,S]; ring
  have hbase : A0-1≤B := by
    apply (add_le_add_iff_right (2:V)).mp
    calc
      A0-1+2=A0+1 := by rw [show A0-1+2=(A0-1+1)+1 by ring,hA1]
      _≤2*P+1 := by simpa only [add_comm] using _root_.add_le_add_right hA2P (1:V)
      _=B+2 := by dsimp [B]; rw [show 2*(P-1)+1+2=2*(P-1+1)+1 by ring,hP1]
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hkC : k v<c p v := lt_of_le_of_lt (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hY) (by simp : (0:V)≤k v))
    (show k v*Y p v<k v*Y p v+v 8 from lt_add_of_pos_right _ (hv 8))
  have hnR : n<R := by
    by_contra hnR
    have hRn : R≤n := le_of_not_gt hnR
    have he : c p v≤k v := calc
      c p v=ycoord R (A0-1) := hc
      _≤ycoord n (A0-1) := (y_strictMono (A0-1)).monotone hRn
      _≤ycoord n B := (base_mono (A0-1) B hbase n).2
      _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
      _=k v := hny
    exact (not_le_of_gt hkC) he
  have hRplus : R+1≤(q p v)^4 := by
    calc
      R+1≤R+(q p v)^3+q p v+1 := by simpa only [add_comm] using _root_.add_le_add_right (show R≤R+(q p v)^3+q p v by simp) (1:V)
      _≤(q p v)^4 := hwindow
  have hpow : (q p v)^4<M := by
    calc
      (q p v)^4<(q p v)^4+(2*q p v*q p v+1) := lt_add_of_pos_right _ (by simp)
      _=(q p v*q p v+1)*(q p v*q p v+1) := by ring
      _=M := rfl
  have hRplusM : R+1<M := lt_of_le_of_lt hRplus hpow
  have hRlt : R<M := lt_trans (lt_add_one R) hRplusM
  have hM : 0<M := mul_pos hmu hmu
  have hrem : (2*n)%M=R+1 := by rwa [mod_eq_self_of_lt hRplusM] at hres
  have hsmall : 2*n<M+(R+1) := calc
    2*n<2*R := mul_lt_mul_of_pos_left hnR (by simp)
    _<M+(R+1) := by
      have hh' := _root_.add_lt_add_of_lt_of_le hRlt (show R≤R+1 by simp)
      simpa only [two_mul] using hh'
  have hquot : (2*n)/M=0 := by
    by_contra hne
    have hq1 : 1≤(2*n)/M := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hne)
    have hcontra : M+(R+1)≤2*n := calc
      M+(R+1)≤M*((2*n)/M)+(R+1) := by simpa only [add_comm] using _root_.add_le_add_right (le_mul_of_one_le_right (by simp : (0:V)≤M) hq1) (R+1)
      _=2*n := by rw [←hrem]; exact div_add_mod _ _
    exact (not_le_of_gt hsmall) hcontra
  have heq : 2*n=R+1 := by
    simpa only [hquot,mul_zero,zero_add,hrem] using (div_add_mod (2*n) M).symm
  exact ⟨n,hn,hnR,heq,hny,hc⟩

#print axioms TenPositive80IndexAlignment.graph_first_main_alignment
end TenPositive80IndexAlignment
