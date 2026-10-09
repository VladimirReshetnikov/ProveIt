import GowersSzemeredi.Proofs16RefinementKernel
import Mathlib.Combinatorics.Pigeonhole

/-! A bounded image on an auxiliary Bohr restriction controls the image
on the endpoint half-radius Bohr set. A popular level avoids shrinking
by the image cap and gives linear dependence on that cap. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Removing `e` auxiliary frequencies costs a fixed rank/radius factor,
keeps radius `rho/2`, and is linear in the original image cap `K`. -/
theorem freiman_image_remove_frequencies {N d e K : Nat} [NeZero N]
    (T U : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho : Real} (hrho : 0 < rho)
    (hT : T.card ≤ d) (hU : U.card ≤ e) (hK : 0 < K)
    (hf : IsFreimanLinearOn (bohr T rho) f)
    (himage : ((bohr (T ∪ U) rho).image f).card ≤ K) :
    (((bohr T (rho/2)).image f).card : Real) ≤ K*(refinementKernelCap d e rho rho : Real) := by
  let P := denseLevelCells rho
  let Q := refinementCells rho
  let B := bohr (T ∪ U) rho
  have hP : 0 < P := Nat.ceil_pos.mpr (by positivity)
  have hQ : 0 < Q := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero P := ⟨ne_of_gt hP⟩
  letI : NeZero Q := ⟨ne_of_gt hQ⟩
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  have hQR : (0 : Real) < Q := by exact_mod_cast hQ
  have hKR : (0 : Real) < K := by exact_mod_cast hK
  have hBne : B.Nonempty := ⟨0, zero_mem_bohr (T ∪ U) hrho.le⟩
  have hPcell : 1 ≤ (rho/4)*P := by
    have h : 4/rho ≤ (P : Real) := Nat.le_ceil _
    rw [div_le_iff₀ hrho] at h
    nlinarith
  have hQcell : 1 ≤ rho*Q := by
    have h : 1/rho ≤ (Q : Real) := Nat.le_ceil _
    rw [div_le_iff₀ hrho] at h
    nlinarith
  have hBmass : (1/(Q : Real)^(d+e))*N ≤ (B.card : Real) := by
    have h := bohr_card_lower (T ∪ U) Q hQcell
    have hc := (Finset.card_union_le T U).trans (Nat.add_le_add hT hU)
    have hn := h.trans (Nat.mul_le_mul_right B.card (Nat.pow_le_pow_right hQ hc))
    have hnR : (N : Real) ≤ (Q : Real)^(d+e)*B.card := by exact_mod_cast hn
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hnR)
  have himageR : ((B.image f).card : Real) ≤ K := by exact_mod_cast himage
  obtain ⟨v, hv, hlevel⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := B) (t := B.image f) (f := f) (b := (B.card : Real)/K)
    (fun z hz => Finset.mem_image_of_mem f hz) (hBne.image f) (by
      rw [nsmul_eq_mul]
      calc
        ((B.image f).card : Real)*((B.card : Real)/K) ≤ K*((B.card : Real)/K) :=
          mul_le_mul_of_nonneg_right himageR (by positivity)
        _ = B.card := mul_div_cancel₀ _ hKR.ne')
  let Z := B.filter fun z => f z = v
  let alpha : Real := 1/((Q : Real)^(d+e)*K)
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hZ : Z ⊆ bohr T rho := by
    intro z hz
    have hzB := (Finset.mem_filter.mp hz).1
    dsimp only [B] at hzB
    rw [bohr_union] at hzB
    exact (Finset.mem_inter.mp hzB).1
  have hZmass : alpha*N ≤ (Z.card : Real) := by
    have h := div_le_div_of_nonneg_right hBmass hKR.le
    have heq : ((1/(Q : Real)^(d+e))*N)/K = alpha*N := by dsimp [alpha]; field_simp
    rw [heq] at h
    exact h.trans hlevel
  have hbound := freiman_image_card_le_of_dense_level T hrho.le ha f hf Z hZ
    (fun _ hz => (Finset.mem_filter.mp hz).2) hZmass hPcell
  calc
    _ ≤ (P : Real)^T.card/alpha := hbound
    _ ≤ (P : Real)^d/alpha := div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by exact_mod_cast hP) hT) ha.le
    _ = _ := by
      dsimp [alpha, refinementKernelCap, P, Q]
      push_cast
      field_simp

/-- A natural-number form of the same linear-cap estimate. -/
theorem freiman_image_remove_frequencies_nat {N d e K : Nat} [NeZero N]
    (T U : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho : Real} (hrho : 0 < rho)
    (hT : T.card ≤ d) (hU : U.card ≤ e) (hK : 0 < K)
    (hf : IsFreimanLinearOn (bohr T rho) f)
    (himage : ((bohr (T ∪ U) rho).image f).card ≤ K) :
    ((bohr T (rho/2)).image f).card ≤ K*refinementKernelCap d e rho rho := by
  exact_mod_cast freiman_image_remove_frequencies T U f hrho hT hU hK hf himage

end LeanProofs.GowersSzemeredi
