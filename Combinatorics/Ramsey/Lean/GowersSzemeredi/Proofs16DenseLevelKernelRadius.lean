import GowersSzemeredi.Proofs16PrimeSmallRange
import GowersSzemeredi.Proofs16FreimanFewValues
import GowersSzemeredi.Proofs16BohrLowerBound

/-! Dense level sets give an exact kernel Bohr set without adding
frequencies in sufficiently large prime cyclic targets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A dense level set bounds the image on the half-radius domain by a
quantity independent of the modulus. -/
theorem freiman_image_card_le_of_dense_level {N M : Nat} [NeZero N] [NeZero M]
    (T : Finset (ZMod N)) {rho alpha : Real} (hrho : 0 ≤ rho) (ha : 0 < alpha)
    (f : ZMod N → ZMod N) (hf : IsFreimanLinearOn (bohr T rho) f)
    (Z : Finset (ZMod N)) (hZ : Z ⊆ bohr T rho) {v : ZMod N}
    (hv : ∀ z ∈ Z, f z = v) (hcard : alpha * N ≤ Z.card)
    (hM : 1 ≤ (rho / 4) * M) :
    (((bohr T (rho / 2)).image f).card : Real) ≤ (M : Real)^T.card / alpha := by
  let I : Real := ((bohr T (rho / 2)).image f).card
  let B : Real := (bohr T (rho / 4)).card
  let D : Real := (M : Real)^T.card
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hI : 0 ≤ I := Nat.cast_nonneg _
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hD : 0 ≤ D := by positivity
  have hpack : I * ((Z.card : Real) * B) ≤ (N : Real)^2 := by
    have h := freiman_image_card_mul_le T hrho f hf Z hZ hv
    have hfull : (bohr T rho).card ≤ N := by
      simpa only [ZMod.card] using Finset.card_le_univ (bohr T rho)
    have h' := h.trans (Nat.mul_le_mul_left N hfull)
    dsimp only [I, B]
    rw [pow_two]
    exact_mod_cast h'
  have hlower : (N : Real) ≤ D * B := by
    dsimp only [D, B]
    exact_mod_cast bohr_card_lower T M hM
  have hbound : I * alpha * (N : Real)^2 ≤ D * (N : Real)^2 := by
    calc I * alpha * (N : Real)^2 = (I * alpha * N) * N := by ring
      _ ≤ (I * alpha * N) * (D * B) := mul_le_mul_of_nonneg_left hlower (by positivity)
      _ = D * (I * (alpha * N * B)) := by ring
      _ ≤ D * (I * ((Z.card : Real) * B)) := by gcongr
      _ ≤ D * (N : Real)^2 := mul_le_mul_of_nonneg_left hpack hD
  exact (le_div_iff₀ ha).mpr ((mul_le_mul_iff_left₀ (sq_pos_of_pos hN)).mp hbound)

/-- The explicit number of values forced by the dense level set. -/
def denseLevelImageCap (d M : Nat) (alpha : Real) : Nat := ⌈(M : Real)^d / alpha⌉₊

/-- In a prime target larger than the image cap, a dense level set forces
constancy on a smaller Bohr set with exactly the original frequencies. -/
theorem freiman_dense_level_constant_same_frequencies {N M : Nat} [NeZero N] [NeZero M]
    [Fact N.Prime] (T : Finset (ZMod N)) {rho alpha : Real}
    (hrho : 0 ≤ rho) (ha : 0 < alpha)
    (f : ZMod N → ZMod N) (hf : IsFreimanLinearOn (bohr T rho) f)
    (Z : Finset (ZMod N)) (hZ : Z ⊆ bohr T rho) {v : ZMod N}
    (hv : ∀ z ∈ Z, f z = v) (hcard : alpha * N ≤ Z.card)
    (hM : 1 ≤ (rho / 4) * M) (hN : denseLevelImageCap T.card M alpha < N) :
    ∀ y ∈ bohr T ((rho / 2) / denseLevelImageCap T.card M alpha), f y = f 0 := by
  have hhalf : IsFreimanLinearOn (bohr T (rho / 2)) f := by
    intro a b c d ha hb hc hd heq
    exact hf a b c d (bohr_mono_radius T (by linarith) ha)
      (bohr_mono_radius T (by linarith) hb) (bohr_mono_radius T (by linarith) hc)
      (bohr_mono_radius T (by linarith) hd) heq
  have hcap : ((bohr T (rho / 2)).image f).card ≤ denseLevelImageCap T.card M alpha := by
    have hb : (((bohr T (rho / 2)).image f).card : Real) ≤
        (denseLevelImageCap T.card M alpha : Real) :=
      (freiman_image_card_le_of_dense_level T hrho ha f hf Z hZ hv hcard hM).trans (Nat.le_ceil _)
    exact_mod_cast hb
  exact freiman_small_image_constant T (by linarith) f hhalf hcap hN

/-- Choose the quarter-domain cell count explicitly. -/
def denseLevelCells (rho : Real) : Nat := ⌈4 / rho⌉₊

/-- An explicit positive radius for the same-frequency kernel conclusion. -/
def denseLevelKernelRadius (d : Nat) (rho alpha : Real) : Real :=
  (rho / 2) / denseLevelImageCap d (denseLevelCells rho) alpha

/-- Dense level-set rigidity with every auxiliary numerical choice discharged. -/
theorem freiman_dense_level_explicit_kernel {N : Nat} [NeZero N] [Fact N.Prime]
    (T : Finset (ZMod N)) {rho alpha : Real} (hrho : 0 < rho) (ha : 0 < alpha)
    (f : ZMod N → ZMod N) (hf : IsFreimanLinearOn (bohr T rho) f)
    (Z : Finset (ZMod N)) (hZ : Z ⊆ bohr T rho) {v : ZMod N}
    (hv : ∀ z ∈ Z, f z = v) (hcard : alpha * N ≤ Z.card)
    (hN : denseLevelImageCap T.card (denseLevelCells rho) alpha < N) :
    0 < denseLevelKernelRadius T.card rho alpha ∧
      ∀ y ∈ bohr T (denseLevelKernelRadius T.card rho alpha),
        y ∈ bohr T rho ∧ f y = f 0 := by
  have hM : 0 < denseLevelCells rho := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero (denseLevelCells rho) := ⟨ne_of_gt hM⟩
  have hMR : (0 : Real) < denseLevelCells rho := by exact_mod_cast hM
  have hK : 0 < denseLevelImageCap T.card (denseLevelCells rho) alpha :=
    Nat.ceil_pos.mpr (by positivity)
  have hKR : (0 : Real) < denseLevelImageCap T.card (denseLevelCells rho) alpha := by exact_mod_cast hK
  have hcell : 1 ≤ (rho / 4) * denseLevelCells rho := by
    have hceil : 4 / rho ≤ (denseLevelCells rho : Real) := Nat.le_ceil _
    have h := (div_le_iff₀ hrho).mp hceil
    nlinarith only [h]
  have hrad : denseLevelKernelRadius T.card rho alpha ≤ rho := by
    apply (div_le_self (by positivity : 0 ≤ rho / 2) (by exact_mod_cast hK)).trans
    linarith
  refine ⟨div_pos (by positivity) hKR, fun y hy => ⟨bohr_mono_radius T hrad hy, ?_⟩⟩
  exact freiman_dense_level_constant_same_frequencies T hrho.le ha f hf Z hZ hv hcard hcell hN y hy

end LeanProofs.GowersSzemeredi
