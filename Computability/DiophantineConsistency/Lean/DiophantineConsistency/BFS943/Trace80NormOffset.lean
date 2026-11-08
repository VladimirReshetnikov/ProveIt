import DiophantineConsistency.BFS943.Trace80NormRank
import DiophantineConsistency.BFS943.Trace75OffsetExact

/-! # First-index alignment and the exact offset at an arbitrary carrier

`Trace75OffsetCongruence`, `Trace75FirstResidue`, `Trace75IndexAlignment` and
`Trace75OffsetExact` restated for a positive zero of `normValue (regs …) Z`
at an arbitrary carrier `Z`. Their two carrier-dependent inputs are explicit
hypotheses: the mask `F + α < q` (`hm`) and the divisibility `q⁴ ∣ e` of the
offset (`hq4`; the 75 chain takes it from `Trace75OffsetDiv`). Output:
`2 n0 = R + 1`, `k = R + 1 + 4 X Y² s` and `e = 4 X Y² s` with `s ≥ 0`.

Chart q1 copy of `TraceNormOffset` for the 80/258 registers
`TenPositiveTrace80.regs` (`X = q² w`, `Y = q s`); names `Trace75*`/`TraceNorm*` below
refer to the q3 originals, whose proofs are reused with the q1 register lemmas. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace80NormOffset
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace80 TenPositiveTrace76
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellFirstIndex
open Trace80Factors Trace80Factors
open Trace80NormRank (rankNat)
open Trace75OffsetCongruence (mod_eq_of_signed_dvd)
open Trace80NormRank (graph_rank_window graph_rank_exact)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_offset_congruence (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hm : v 1+v 2<q p v)
    (hq4 : (ι (q p v):DiffRing V)^4 ∣ (regs (ports p) (fun j => ι (v j))).e) :
    k v%(q p v)^4=(rankNat p v+1)%(q p v)^4 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hrank := (graph_rank_window p v Z hb31 hl hh hv hz hm).1
  have he : (regs (ports p) (fun j => ι (v j))).e =
      (ι (k v):DiffRing V)-ι (rankNat p v+1) := by
    rw [e_def,k_def,hrank]
    simp only [k,map_add,map_one]
    ring
  have hd := hq4
  rw [he,←map_pow] at hd
  exact mod_eq_of_signed_dvd _ _ _ (pow_pos hq 4) hd


theorem graph_first_index_residue (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hm : v 1+v 2<q p v)
    (hq4 : (ι (q p v):DiffRing V)^4 ∣ (regs (ports p) (fun j => ι (v j))).e) :
    ∃ n : V, 0<n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      (2*n)%(q p v)^4=(rankNat p v+1)%(q p v)^4 := by
  let P : V := firstParam p v
  let M : V := (q p v)^4
  let B : V := 2*(P-1)+1
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos hq (hv 6)
  have hX : 0<X p v := mul_pos hq (mul_pos hq (hv 5))
  have hM : 0<M := pow_pos hq 4
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hdiv : M∣B+1 := by
    refine ⟨2*v 5*v 6*v 6,?_⟩
    calc
      B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
      _=M*(2*v 5*v 6*v 6) := by dsimp [M,P,firstParam,X,Y]; ring
  obtain ⟨_tau,_f,n,_I,_ht,_hf,hn,_hnK,_hE,_hf2,_hnx,hny,_hIeq,_hIpos,_hstrong,_hQ,_hC⟩ :=
    Trace80NormFold.first_and_doubled p v Z hb hv hz
  change 2*ycoord n B=k v at hny
  obtain ⟨_r,s,_hx,hys⟩ := residue_quotients n B M hdiv
  have hk : k v=2*n+M*(2*s) := by rw [←hny,hys]; ring
  have hmod : k v%M=(2*n)%M := by rw [hk,mod_add_mul' _ _ hM]
  have hcong := graph_offset_congruence p v Z hb31 hl hh hv hz hm hq4
  exact ⟨n,hn,hny,hmod.symm.trans hcong⟩


theorem graph_first_main_alignment (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hm : v 1+v 2<q p v)
    (hq4 : (ι (q p v):DiffRing V)^4 ∣ (regs (ports p) (fun j => ι (v j))).e) :
    ∃ n : V, 0<n ∧ n<rankNat p v ∧ 2*n=rankNat p v+1 ∧
      2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      c p v=ycoord (rankNat p v) (A p v-1) := by
  let P : V := firstParam p v
  let S : V := Y p v
  let A0 : V := A p v
  let B : V := 2*(P-1)+1
  let R : V := rankNat p v
  let M : V := (q p v)^4
  obtain ⟨n,hn,hny,hres⟩ := graph_first_index_residue p v Z hb31 hl hh hv hz hm hq4
  obtain ⟨_heval,_hRlo,_hRodd,hc,hwindow⟩ := graph_rank_exact p v Z hb31 hl hh hv hz hm
  change 2*ycoord n B=k v at hny
  change (2*n)%M=(R+1)%M at hres
  change c p v=ycoord R (A0-1) at hc
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos hq (hv 6)
  have hX : 0<X p v := mul_pos hq (mul_pos hq (hv 5))
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
  have hRplusM : R+1<M := calc
    R+1 < R+((q p v)^3+q p v)+1 := by
      simpa only [add_comm,add_left_comm,add_assoc] using
        _root_.add_lt_add_right (lt_add_of_pos_right R (add_pos (pow_pos hq 3) hq)) 1
    _ ≤ M := by simpa only [M,add_assoc] using hwindow
  have hRlt : R<M := lt_trans (lt_add_one R) hRplusM
  have hM : 0<M := pow_pos hq 4
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


theorem graph_offset_exact (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hm : v 1+v 2<q p v)
    (hq4 : (ι (q p v):DiffRing V)^4 ∣ (regs (ports p) (fun j => ι (v j))).e) :
    ∃ n s : V, 0<n ∧ 2*n=rankNat p v+1 ∧
      k v=rankNat p v+1+(4*firstParam p v)*s ∧
      (regs (ports p) (fun j => ι (v j))).e=ι ((4*firstParam p v)*s) := by
  obtain ⟨n,hn,_hnR,halign,hny,_hc⟩ := graph_first_main_alignment p v Z hb31 hl hh hv hz hm hq4
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos hq (hv 6)
  have hX : 0<X p v := mul_pos hq (mul_pos hq (hv 5))
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB : B+1=2*P := calc
    B+1=2*(P-1+1) := by dsimp [B]; ring
    _=2*P := by rw [hP1]
  have hdiv : 2*P∣B+1 := ⟨1,by rw [hB,mul_one]⟩
  obtain ⟨_r,s,_hx,hys⟩ := residue_quotients n B (2*P) hdiv
  change 2*ycoord n B=k v at hny
  have hk : k v=rankNat p v+1+(4*P)*s := by
    calc
      k v=2*ycoord n B := hny.symm
      _=2*n+(4*P)*s := by rw [hys]; ring
      _=rankNat p v+1+(4*P)*s := by rw [halign]
  have hnat := (graph_rank_window p v Z hb31 hl hh hv hz hm).1
  have heval : (regs (ports p) (fun j => ι (v j))).e=ι (k v)-ι (rankNat p v+1) := by
    rw [e_def,k_def,hnat]
    simp only [k,map_add,map_one]
    ring
  refine ⟨n,s,hn,halign,hk,?_⟩
  rw [heval,hk,map_add]
  ring

theorem graph_offset_full_divisibility (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hm : v 1+v 2<q p v)
    (hq4 : (ι (q p v):DiffRing V)^4 ∣ (regs (ports p) (fun j => ι (v j))).e) :
    (ι (X p v*Y p v):DiffRing V) ∣
      (regs (ports p) (fun j => ι (v j))).e := by
  obtain ⟨_n,s,_hn,_halign,_hk,he⟩ := graph_offset_exact p v Z hb31 hl hh hv hz hm hq4
  refine ⟨ι (4*Y p v*s),?_⟩
  rw [he,←map_mul]
  congr 1
  dsimp [firstParam]
  ring

#print axioms Trace80NormOffset.graph_offset_full_divisibility
end Trace80NormOffset
