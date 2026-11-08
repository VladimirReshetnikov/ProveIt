import DiophantineConsistency.BFS943.Trace104NormRank
import DiophantineConsistency.BFS943.Trace75OffsetExact

/-! # First-index alignment at an arbitrary carrier (104/174)

`Trace82NormOffset.graph_first_main_alignment` for the constant-dilation core registers.
In the 82 chain the residue `2 n ≡ R + 1 (mod q⁴)` of the first index came from
`q⁴ ∣ e` and `k ≡ 2 n (mod 4 v)` with `q⁴ ∣ 4 v`. Here `v = q³ w s²`, so the
residue is an explicit hypothesis `hres` at the given first index `n`; the
104 transport supplies it through the third-order inverse
(`Trace104Transport.graph_zero_data`). Output: `n < R`, `2 n = R + 1` and
`c = ψ_A(R)`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace104NormOffset
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace104 TenPositiveTrace76
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellFirstIndex
open Trace104Factors
open Trace104NormRank (rankNat)
open Trace75OffsetCongruence (mod_eq_of_signed_dvd)
open Trace104NormRank (graph_rank_window graph_rank_exact)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_main_alignment (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V) (n : V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hm : v 1+v 2<q p v)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hres : (ι (q p v):DiffRing V)^4 ∣ ι (2*n)-ι (rankNat p v+1)) :
    n<rankNat p v ∧ 2*n=rankNat p v+1 ∧
      c p v=ycoord (rankNat p v) (A p v-1) := by
  let P : V := firstParam p v
  let S : V := Y p v
  let A0 : V := A p v
  let B : V := 2*(P-1)+1
  let R : V := rankNat p v
  let M : V := (q p v)^4
  obtain ⟨_heval,_hRlo,_hRodd,hc,hwindow⟩ := graph_rank_exact p v Z hb31 hl hh hv hz hm
  change 2*ycoord n B=k v at hny
  change c p v=ycoord R (A0-1) at hc
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hM : 0<M := pow_pos hq 4
  have hres' : (2*n)%M=(R+1)%M := by
    apply mod_eq_of_signed_dvd M (2*n) (R+1) hM
    simpa only [M,map_pow] using hres
  have hY : 0<Y p v := mul_pos (by norm_num) (hv 6)
  have hX : 0<X p v := mul_pos hq (hv 5)
  have hS : 0<S := hY
  have hS1 : 1≤S := pos_iff_one_le.mp hS
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hP : 0<P := mul_pos hX (mul_pos hS hS)
  have hA : 0<A0 := add_pos (mul_pos hX hY) hY
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hA1 : A0-1+1=A0 := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hXP : X p v+1≤2*X p v := by
    calc
      X p v+1≤X p v+X p v := by simpa only [add_comm] using _root_.add_le_add_left hX1 (X p v)
      _=2*X p v := by ring
  have hSsq : S≤S*S := le_mul_of_one_le_right (by simp) hS1
  have hA2P : A0≤2*P := calc
    A0=S*(X p v+1) := by dsimp [A0,A,S]; ring
    _≤S*(2*X p v) := mul_le_mul_of_nonneg_left hXP (by simp)
    _≤(S*S)*(2*X p v) := mul_le_mul_of_nonneg_right hSsq (by simp)
    _=2*P := by dsimp [P,firstParam,S]; ring
  have hbase : A0-1≤B := by
    apply (add_le_add_iff_right (2:V)).mp
    calc
      A0-1+2=A0+1 := by rw [show A0-1+2=(A0-1+1)+1 by ring,hA1]
      _≤2*P+1 := by simpa only [add_comm] using _root_.add_le_add_right hA2P (1:V)
      _=B+2 := by dsimp [B]; rw [show 2*(P-1)+1+2=2*(P-1+1)+1 by ring,hP1]
  have hkC : k v<c p v := lt_of_le_of_lt (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6)) (by simp : (0:V)≤k v))
    (show k v*v 6<k v*v 6+v 8 from lt_add_of_pos_right _ (hv 8))
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
  have hRplusM : R+1<M := calc
    R+1 < R+((q p v)^3+q p v)+1 := by
      simpa only [add_comm,add_left_comm,add_assoc] using
        _root_.add_lt_add_right (lt_add_of_pos_right R (add_pos (pow_pos hq 3) hq)) 1
    _ ≤ M := by simpa only [M,add_assoc] using hwindow
  have hRlt : R<M := lt_trans (lt_add_one R) hRplusM
  have hrem : (2*n)%M=R+1 := by rwa [mod_eq_self_of_lt hRplusM] at hres'
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
  exact ⟨hnR,heq,hc⟩

#print axioms Trace104NormOffset.graph_first_main_alignment
end Trace104NormOffset
