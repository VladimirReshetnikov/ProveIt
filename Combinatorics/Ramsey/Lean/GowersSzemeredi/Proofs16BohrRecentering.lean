import GowersSzemeredi.Proofs16Corollary20CommonBohr
import GowersSzemeredi.Proofs16BohrSpectrum
import GowersSzemeredi.Proofs16BohrLowerBound
import GowersSzemeredi.Proofs05ProgressionVariance

/-! Averaging and recentering dense pieces on translates of half-radius
Bohr neighborhoods. The retained mass is relative to that neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def localTranslateCoordinates {N : Nat} (E B : Finset (ZMod N)) (t : ZMod N) : Finset (ZMod N) :=
  B.filter fun x => t + x ∈ E

/-- The exact mean size of intersections with translates. -/
theorem localTranslateCoordinates_sum {N : Nat} [NeZero N] (E B : Finset (ZMod N)) :
    (∑ t : ZMod N, ((localTranslateCoordinates E B t).card : Real)) =
      (E.card : Real) * B.card := by
  have hcard (t : ZMod N) : ((localTranslateCoordinates E B t).card : Real) =
      ∑ x ∈ B, realSetIndicator E (t + x) := by
    simp [localTranslateCoordinates, realSetIndicator]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  have hs (x : ZMod N) : (∑ t : ZMod N, realSetIndicator E (t + x)) = E.card :=
    (sum_translate_real (realSetIndicator E) x).trans (sum_realSetIndicator E)
  simp only [hs, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Some translate retains the ambient density inside any test set. -/
theorem exists_dense_localTranslate {N : Nat} [NeZero N] (E B : Finset (ZMod N))
    {kappa : Real} (hE : kappa * N ≤ E.card) :
    ∃ t : ZMod N, kappa * B.card ≤ ((localTranslateCoordinates E B t).card : Real) := by
  have hs : (∑ _t : ZMod N, kappa * (B.card : Real)) ≤
      ∑ t : ZMod N, ((localTranslateCoordinates E B t).card : Real) := by
    rw [localTranslateCoordinates_sum]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have h := mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg B.card : (0 : Real) ≤ B.card)
    nlinarith only [h]
  obtain ⟨t, ht, hbound⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨t, hbound⟩

/-- A dense set contains a cluster of the expected relative size whose
pairwise differences all lie in the full-radius Bohr set. -/
theorem exists_dense_bohr_cluster {N : Nat} [NeZero N]
    (E Gamma : Finset (ZMod N)) {kappa rho : Real}
    (hk : 0 < kappa) (hrho : 0 ≤ rho) (hE : kappa * N ≤ E.card) :
    ∃ (a : ZMod N) (C : Finset (ZMod N)), a ∈ C ∧ C ⊆ E ∧
      kappa * (bohr Gamma (rho / 2)).card ≤ (C.card : Real) ∧
      ∀ x ∈ C, ∀ y ∈ C, x - y ∈ bohr Gamma rho := by
  let B := bohr Gamma (rho / 2)
  obtain ⟨t, ht⟩ := exists_dense_localTranslate E B hE
  have hBpos : (0 : Real) < B.card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨0, zero_mem_bohr Gamma (show 0 ≤ rho / 2 by positivity)⟩)
  have hnonempty : (localTranslateCoordinates E B t).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos hk hBpos).trans_le ht
  obtain ⟨b, hb⟩ := hnonempty
  let C := (localTranslateCoordinates E B t).image fun x => t + x
  refine ⟨t + b, C, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hu).2
  · have hc : C.card = (localTranslateCoordinates E B t).card :=
      Finset.card_image_of_injective _ (fun x y h => add_left_cancel h)
    simpa only [hc] using ht
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hdiff := bohr_add_half (Finset.mem_filter.mp hu).1
      (neg_mem_bohr (Finset.mem_filter.mp hv).1)
    rw [show (t + u) - (t + v) = u + -v by ring]
    exact hdiff

/-- The retained relative mass gives an explicit ambient density by the
Dirichlet-cell lower bound for the half-radius neighborhood. -/
theorem bohr_cluster_density_lower {N : Nat} [NeZero N]
    (C Gamma : Finset (ZMod N)) (M : Nat) [NeZero M] {kappa rho : Real}
    (hk : 0 ≤ kappa) (hM : 2 ≤ rho * M)
    (hC : kappa * (bohr Gamma (rho / 2)).card ≤ (C.card : Real)) :
    (kappa / (M : Real)^Gamma.card) * N ≤ (C.card : Real) := by
  have hMP : (0 : Real) < M := by exact_mod_cast NeZero.pos M
  have hB : (N : Real) ≤ (M : Real)^Gamma.card * (bohr Gamma (rho / 2)).card := by
    exact_mod_cast bohr_card_lower Gamma M (show 1 ≤ rho / 2 * M by linarith)
  have h1 := mul_le_mul_of_nonneg_left hB hk
  have h2 := mul_le_mul_of_nonneg_left hC (show 0 ≤ (M : Real)^Gamma.card by positivity)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [h1, h2]

/-- Recenter a Bohr-extended map on a dense cluster. The difference map
remains normalized and locally additive on the common neighborhood. -/
theorem IsBHomomorphism.dense_recenter {N : Nat} [NeZero N]
    (E Gamma : Finset (ZMod N)) (f : ZMod N → ZMod N) {kappa rho : Real}
    (hk : 0 < kappa) (hrho : 0 ≤ rho) (hE : kappa * N ≤ E.card)
    (hf : IsBHomomorphism E (bohr Gamma rho) f) :
    ∃ (a : ZMod N) (C : Finset (ZMod N)) (psi : ZMod N → ZMod N),
      a ∈ C ∧ C ⊆ E ∧ kappa * (bohr Gamma (rho / 2)).card ≤ (C.card : Real) ∧
      FreimanHom 2 (bohr Gamma rho) psi ∧ psi 0 = 0 ∧
      (∀ x ∈ bohr Gamma rho, ∀ y ∈ bohr Gamma rho, x + y ∈ bohr Gamma rho →
        psi (x + y) = psi x + psi y) ∧
      (∀ x ∈ C, ∀ y ∈ C, x - y ∈ bohr Gamma rho) ∧
      ∀ x ∈ C, f x = f a + psi (x - a) := by
  obtain ⟨a, C, ha, hCE, hC, hdiff⟩ := exists_dense_bohr_cluster E Gamma hk hrho hE
  obtain ⟨psi, hpsi, hz, hadd, hagree⟩ :=
    hf.normalized_extension ⟨a, hCE ha⟩ (zero_mem_bohr Gamma hrho)
  refine ⟨a, C, psi, ha, hCE, hC, hpsi, hz, hadd, hdiff, ?_⟩
  intro x hx
  have h := hagree x (hCE hx) a (hCE ha) (hdiff x hx a ha)
  linear_combination h

end LeanProofs.GowersSzemeredi
