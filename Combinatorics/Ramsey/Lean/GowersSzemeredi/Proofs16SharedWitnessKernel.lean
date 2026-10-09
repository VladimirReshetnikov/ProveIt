import GowersSzemeredi.Proofs16SharedWitnessZeros
import GowersSzemeredi.Proofs16DenseLevelKernelRadius

/-! Shared witness density yields exact column identities at a uniform
radius in sufficiently large prime cyclic groups. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def sharedWitnessImageCap (d : Nat) (rho theta : Real) : Nat :=
  denseLevelImageCap (4 * d) (denseLevelCells rho) theta

def sharedWitnessKernelRadius (d : Nat) (rho theta : Real) : Real :=
  (rho / 2) / sharedWitnessImageCap d rho theta

theorem sharedWitnessImageCap_pos (d : Nat) {rho theta : Real}
    (hrho : 0 < rho) (htheta : 0 < theta) : 0 < sharedWitnessImageCap d rho theta := by
  have hM : 0 < denseLevelCells rho := Nat.ceil_pos.mpr (by positivity)
  have hMR : (0 : Real) < denseLevelCells rho := by exact_mod_cast hM
  exact Nat.ceil_pos.mpr (by positivity)

theorem sharedWitnessKernelRadius_pos (d : Nat) {rho theta : Real}
    (hrho : 0 < rho) (htheta : 0 < theta) : 0 < sharedWitnessKernelRadius d rho theta := by
  have hK : (0 : Real) < sharedWitnessImageCap d rho theta := by
    exact_mod_cast sharedWitnessImageCap_pos d hrho htheta
  exact div_pos (by positivity) hK

/-- The spectrum union of a column quadruple has rank at most four times
the uniform column rank. -/
theorem columnQuadrupleSpectrum_card_le {N d : Nat}
    (T : ZMod N → Finset (ZMod N)) (q : Fin 4 → ZMod N)
    (hT : ∀ i, (T (q i)).card ≤ d) : (columnQuadrupleSpectrum T q).card ≤ 4 * d := by
  apply Finset.card_biUnion_le.trans
  calc (∑ i : Fin 4, (T (q i)).card) ≤ ∑ _i : Fin 4, d := Finset.sum_le_sum fun i _ => hT i
    _ = 4 * d := by simp

/-- A dense set of shared witnesses forces the exact column identity on
a common radius which depends only on rank, initial radius, and density. -/
theorem shared_witness_uniform_identity {N d : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
    {rho theta : Real} (hrho : 0 < rho) (htheta : 0 < theta)
    (hphi : IsEBihomomorphism A phi {0}) (hsys : IsColumnWitnessSystem A phi X T L W rho)
    (q : Fin 4 → ZMod N) (hqX : ∀ i, q i ∈ X) (hq : IsAdditiveQuadruple q)
    (hT : ∀ i, (T (q i)).card ≤ d)
    (hL : ∀ i, IsFreimanLinearOn (bohr (T (q i)) rho) (L (q i)))
    (hzero : ∀ i, L (q i) 0 = 0)
    (hcount : theta * (N : Real)^4 ≤ (commonWitnesses W q).card)
    (hN : sharedWitnessImageCap d rho theta < N) :
    ∀ y, (∀ i, y ∈ bohr (T (q i)) (sharedWitnessKernelRadius d rho theta)) →
      L (q 0) y + L (q 1) y = L (q 2) y + L (q 3) y := by
  obtain ⟨Z, hZ, hZcard, hZzero⟩ := common_witness_dense_zero_set A phi X T L W
    hphi hsys q hqX hq hcount
  let S := columnQuadrupleSpectrum T q
  have hS : S.card ≤ 4 * d := columnQuadrupleSpectrum_card_le T q hT
  have hM : 0 < denseLevelCells rho := Nat.ceil_pos.mpr (by positivity)
  have hMR : (1 : Real) ≤ denseLevelCells rho := by exact_mod_cast hM
  have hcap : denseLevelImageCap S.card (denseLevelCells rho) theta ≤
      sharedWitnessImageCap d rho theta := by
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hMR hS) htheta.le
  have hsmall : 0 < denseLevelImageCap S.card (denseLevelCells rho) theta :=
    Nat.ceil_pos.mpr (by positivity)
  have hsmallR : (0 : Real) < denseLevelImageCap S.card (denseLevelCells rho) theta := by
    exact_mod_cast hsmall
  have hrad : sharedWitnessKernelRadius d rho theta ≤ denseLevelKernelRadius S.card rho theta :=
    div_le_div_of_nonneg_left (by positivity) hsmallR (by exact_mod_cast hcap)
  have hker := (freiman_dense_level_explicit_kernel S hrho htheta (columnQuadrupleDefect L q)
    (columnQuadrupleDefect_freiman T L q hL) Z hZ hZzero hZcard (hcap.trans_lt hN)).2
  intro y hy
  have hyS : y ∈ bohr S (sharedWitnessKernelRadius d rho theta) :=
    (mem_bohr_family_union (fun i => T (q i)) _ y).mpr hy
  have heq := (hker y (bohr_mono_radius S hrad hyS)).2
  simp only [columnQuadrupleDefect, hzero, add_zero, sub_zero] at heq
  linear_combination heq

end LeanProofs.GowersSzemeredi
