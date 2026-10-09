import GowersSzemeredi.Proofs16DenseLevelKernelRadius
import GowersSzemeredi.Proofs16VarietyRegularStep

/-! Remove extra Bohr constraints from a zero identity, at an explicit
radius cost and with no new frequencies in a sufficiently large prime target. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def refinementCells (r : Real) : Nat := ⌈1 / r⌉₊
def refinementKernelCap (d e : Nat) (rho r : Real) : Nat :=
  (denseLevelCells rho)^d * (refinementCells r)^(d + e)
def refinementKernelRadius (d e : Nat) (rho r : Real) : Real :=
  (rho / 2) / refinementKernelCap d e rho r

theorem refinementKernelCap_pos (d e : Nat) {rho r : Real} (hrho : 0 < rho) (hr : 0 < r) :
    0 < refinementKernelCap d e rho r := by
  have hP : 0 < denseLevelCells rho := Nat.ceil_pos.mpr (by positivity)
  have hQ : 0 < refinementCells r := Nat.ceil_pos.mpr (by positivity)
  exact Nat.mul_pos (pow_pos hP _) (pow_pos hQ _)

theorem refinementKernelRadius_pos (d e : Nat) {rho r : Real} (hrho : 0 < rho) (hr : 0 < r) :
    0 < refinementKernelRadius d e rho r := by
  have hK : (0 : Real) < refinementKernelCap d e rho r := by
    exact_mod_cast refinementKernelCap_pos d e hrho hr
  exact div_pos (by positivity) hK

/-- A Freiman-linear map which vanishes after adding `e` frequencies
already vanishes on a smaller Bohr set using only its original `d`
frequencies. All numerical bounds are independent of the modulus. -/
theorem freiman_zero_remove_frequencies {N d e : Nat} [NeZero N] [Fact N.Prime]
    (T U : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hT : T.card ≤ d) (hU : U.card ≤ e)
    (hf : IsFreimanLinearOn (bohr T rho) f) (hf0 : f 0 = 0)
    (hzero : ∀ y ∈ bohr (T ∪ U) r, f y = 0)
    (hN : refinementKernelCap d e rho r < N) :
    ∀ y ∈ bohr T (refinementKernelRadius d e rho r), f y = 0 := by
  let P := denseLevelCells rho
  let Q := refinementCells r
  let K := refinementKernelCap d e rho r
  let Z := bohr (T ∪ U) r
  let alpha : Real := 1 / (Q : Real)^(d + e)
  have hP : 0 < P := Nat.ceil_pos.mpr (by positivity)
  have hQ : 0 < Q := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero P := ⟨ne_of_gt hP⟩
  letI : NeZero Q := ⟨ne_of_gt hQ⟩
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  have hQR : (0 : Real) < Q := by exact_mod_cast hQ
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hPcell : 1 ≤ (rho / 4) * P := by
    have hc : 4 / rho ≤ (P : Real) := Nat.le_ceil _
    have := (div_le_iff₀ hrho).mp hc
    nlinarith only [this]
  have hQcell : 1 ≤ r * Q := by
    have hc : 1 / r ≤ (Q : Real) := Nat.le_ceil _
    have := (div_le_iff₀ hr).mp hc
    nlinarith only [this]
  have hZ : Z ⊆ bohr T rho := by
    intro y hy
    dsimp only [Z] at hy
    rw [bohr_union] at hy
    exact bohr_mono_radius T hrle (Finset.mem_inter.mp hy).1
  have hcard : alpha * N ≤ (Z.card : Real) := by
    have h := bohr_card_lower (T ∪ U) Q hQcell
    have hc : (T ∪ U).card ≤ d + e := (Finset.card_union_le _ _).trans (Nat.add_le_add hT hU)
    have hn : N ≤ Q^(d + e) * Z.card := h.trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hQ hc))
    have hnR : (N : Real) ≤ (Q : Real)^(d + e) * Z.card := by exact_mod_cast hn
    dsimp only [alpha]
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hnR)
  have hbound := freiman_image_card_le_of_dense_level T hrho.le ha f hf Z hZ hzero hcard hPcell
  have hcap : ((bohr T (rho / 2)).image f).card ≤ K := by
    have hp : (P : Real)^T.card ≤ (P : Real)^d := pow_le_pow_right₀ (by exact_mod_cast hP) hT
    have hB : (((bohr T (rho / 2)).image f).card : Real) ≤ (K : Real) := by
      calc _ ≤ (P : Real)^T.card / alpha := hbound
        _ ≤ (P : Real)^d / alpha := div_le_div_of_nonneg_right hp ha.le
        _ = (K : Real) := by simp [K, refinementKernelCap, alpha, P, Q]
    exact_mod_cast hB
  have hhalf : IsFreimanLinearOn (bohr T (rho / 2)) f := by
    intro a b c d ha hb hc hd heq
    exact hf a b c d (bohr_mono_radius T (by linarith) ha) (bohr_mono_radius T (by linarith) hb)
      (bohr_mono_radius T (by linarith) hc) (bohr_mono_radius T (by linarith) hd) heq
  exact freiman_small_image_zero T (by positivity) f hhalf hf0 hcap hN

end LeanProofs.GowersSzemeredi
