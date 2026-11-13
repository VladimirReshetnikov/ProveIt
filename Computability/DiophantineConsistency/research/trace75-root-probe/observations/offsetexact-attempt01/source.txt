import Trace75IndexAlignment

/-! Exact nonnegative graph offset after noncircular index alignment. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75OffsetExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellCongruences
open Trace75Factors Trace75Rank Trace75Pell Trace75IndexAlignment
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_offset_exact (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ n s : V, 0<n ∧ 2*n=rankNat p v+1 ∧
      k v=rankNat p v+1+(4*firstParam p v)*s ∧
      (regs (ports p) (fun j => ι (v j))).e=ι ((4*firstParam p v)*s) := by
  obtain ⟨n,hn,_hnR,halign,hny,_hc⟩ := graph_first_main_alignment p v hb31 hl hh hv hz
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
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
  have hnat := (graph_rank_window p v hb31 hl hh hv hz).1
  have heval : (regs (ports p) (fun j => ι (v j))).e=ι (k v)-ι (rankNat p v+1) := by
    rw [e_def,k_def,hnat]
    simp only [k,map_add,map_one]
    ring
  refine ⟨n,s,hn,halign,hk,?_⟩
  rw [heval,hk,map_add]
  ring

theorem graph_offset_full_divisibility (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    (ι (X p v*Y p v):DiffRing V) ∣
      (regs (ports p) (fun j => ι (v j))).e := by
  obtain ⟨_n,s,_hn,_halign,_hk,he⟩ := graph_offset_exact p v hb31 hl hh hv hz
  refine ⟨ι (4*Y p v*s),?_⟩
  rw [he,←map_mul]
  congr 1
  dsimp [firstParam]
  ring

#print axioms Trace75OffsetExact.graph_offset_exact
#print axioms Trace75OffsetExact.graph_offset_full_divisibility
end Trace75OffsetExact
