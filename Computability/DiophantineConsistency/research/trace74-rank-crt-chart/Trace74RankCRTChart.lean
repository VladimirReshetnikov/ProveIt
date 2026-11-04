import Trace74RankCRTModel

/-! Specialize the three-modulus CRT to the negative trace74 rank chart. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace Trace74RankCRTChart
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing Trace74RankCRTModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Construct the negative signed-rank chart with simultaneous carrier,
offset and main-index divisibilities. Coprimality remains explicit. -/
theorem negative_rank_chart (q h D c U W RJ k r bound : V)
    (hh : 0<h) (hD : 0<D) (hc : 0<c)
    (hq : h+1=q) (hU : 1≤U) (hW : 1≤W)
    (hDc : IsCoprime (ι D : DiffRing V) (ι c))
    (hDh : IsCoprime (ι D : DiffRing V) (ι h))
    (hch : IsCoprime (ι c : DiffRing V) (ι h))
    (hUD : IsCoprime (ι U : DiffRing V) (ι D))
    (hUc : IsCoprime (ι U : DiffRing V) (ι c))
    (hWh : IsCoprime (ι W : DiffRing V) (ι h)) :
    ∃ N B : V, bound<N ∧ 1≤B ∧
      let C := q*h+N
      let R : DiffRing V := ι RJ-ι U*ι N
      R<0 ∧ q≤1+C ∧
      (ι D : DiffRing V) ∣ ι k-R-1 ∧
      (ι c : DiffRing V) ∣ R+ι r ∧
      (ι h : DiffRing V) ∣ ι B ∧
      (ι B : DiffRing V)=ι W*ι C-1 := by
  obtain ⟨N,hN,hN_D,hN_c,hN_h⟩ :=
    positive_three_linear D c h U W (max bound RJ)
      ((ι k : DiffRing V)-ι RJ-1) (-(ι RJ+ι r))
      hD hc hh hDc hDh hch hUD hUc hWh
  have hbound : bound<N := lt_of_le_of_lt (le_max_left _ _) hN
  have hRJ : RJ<N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN1 : 1≤N := pos_iff_one_le.mp (lt_of_le_of_lt (by simp : (0:V)≤RJ) hRJ)
  have hq1 : 1≤q := by rw [←hq]; simp
  have hh1 : 1≤h := pos_iff_one_le.mp hh
  let C := q*h+N
  have hC2 : 2≤C := by
    have hp : 1≤q*h := one_le_mul hq1 hh1
    dsimp [C]
    calc
      (2:V) = 1+1 := by norm_num
      _ ≤ q*h+N := add_le_add hp hN1
  have hWC : 2≤W*C := calc
    (2:V)≤C := hC2
    _≤W*C := by simpa using mul_le_mul_of_nonneg_right hW (show (0:V)≤C by simp)
  have hWC' : (2:DiffRing V)≤ι W*ι C := by
    simpa only [map_mul,map_ofNat] using ι_le_ι.mpr hWC
  obtain ⟨B,hB⟩ := nonneg_iff.mp (show (0:DiffRing V)≤ι W*ι C-1 by linarith)
  have hB1 : 1≤B := ι_le_ι.mp (by rw [←hB]; simpa only [map_one] using (show (1:DiffRing V)≤ι W*ι C-1 by linarith))
  let R : DiffRing V := ι RJ-ι U*ι N
  have hUN : N≤U*N := by simpa using mul_le_mul_of_nonneg_right hU (show (0:V)≤N by simp)
  have hR : R<0 := by
    have hm : (ι RJ:DiffRing V)<ι (U*N) := ι_lt_ι.mpr (lt_of_lt_of_le hRJ hUN)
    simp only [map_mul] at hm
    dsimp [R]
    linarith
  have hguard : q≤1+C := by
    have hp : q≤q*h := by simpa using mul_le_mul_of_nonneg_left hh1 (show (0:V)≤q by simp)
    dsimp [C]
    calc
      q ≤ q*h := hp
      _ ≤ q*h+N := le_add_of_nonneg_right (by simp)
      _ ≤ 1+(q*h+N) := le_add_of_nonneg_left (by simp)
  have hd : (ι D:DiffRing V)∣ι k-R-1 := by
    convert hN_D using 1 <;> dsimp [R] <;> ring
  have hc' : (ι c:DiffRing V)∣R+ι r := by
    have hd := dvd_neg.mpr hN_c
    convert hd using 1 <;> dsimp [R] <;> ring
  have hh' : (ι h:DiffRing V)∣ι B := by
    rw [←hB]
    have hd : (ι h:DiffRing V)∣ι W*ι q*ι h := dvd_mul_left _ _
    have hs := dvd_add hd hN_h
    convert hs using 1 <;> dsimp [C] <;> simp only [map_add,map_mul] <;> ring
  exact ⟨N,B,hbound,hB1,hR,hguard,hd,hc',hh',hB.symm⟩

#print axioms Trace74RankCRTChart.negative_rank_chart
end Trace74RankCRTChart
