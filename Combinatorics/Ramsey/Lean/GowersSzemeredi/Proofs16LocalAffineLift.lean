import GowersSzemeredi.Proofs16CompressedSynchronizedCover

/-! # Local affine lifting with explicit verified bounds

This assembles sampling, a common slice refinement, and compatible final
axis tiling on a proper box. The output parameters are recorded as proved;
they are not identified with the unsupported closing bounds of Lemma 16.10.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_local_affine_lift {N k q r m v : Nat} [Fact N.Prime]
    (P : Box N (k + 1)) (hP : P.IsProper) (hk : 0 < k)
    (hm : 4 ≤ m) (hmP : m ≤ P.width)
    (B D : Finset (Point N (k + 1))) (hD : D ⊆ B)
    (phi : Point N (k + 1) → ZMod N) (gamma s : ℝ)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi) (hs : 1 ≤ s)
    (ell : Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ h i, LinearOn Finset.univ (ell h i))
    (hcover : ∀ h x, appendCoordinate h x ∈ P.carrier → appendCoordinate h x ∈ D →
      ∃ i, phi (appendCoordinate h x) = ell h i x)
    (τ ε : ℝ) (hq : 0 < q) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ) (hv : 1 ≤ v)
    (hvscale : (v : ℝ) ^ 2 + 1 ≤ ((m : ℝ) / 8) ^
      ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s))) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
      G ⊆ P.carrier ∧ (1 - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition S P ∧ (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j ij, IsMultilinear (nu j ij)) ∧
      ∀ j z, z ∈ (S j).carrier → z ∈ D → z ∈ G → ∃ ij, phi z = nu j ij z := by
  classical
  let T := boxInit P
  let I := P.axis (Fin.last k)
  have hT : T.IsProper := boxInit_isProper P hP
  have hI : I.IsProper := hP (Fin.last k)
  have hmT : m ≤ T.width := hmP.trans (boxInit_width P hk)
  have hmI : m ≤ I.length := hmP.trans (P.width_le_axis_length (Fin.last k))
  have hInonempty : I.carrier.Nonempty := by
    apply Finset.card_pos.mp
    rw [show I.carrier.card = I.length from hI]
    omega
  have hprod : IsLastCoordinateBoxProduct P T I := boxInit_last_product P
  have hcarrier : P.carrier = lastProductSet T.carrier I.carrier := hprod.1
  obtain ⟨u, hu⟩ := I.step_isUnit_of_prime hI (by omega)
  have hstep : I.step = T.commonDiff := P.axis_step (Fin.last k)
  have hrpos : 0 < r := by
    by_contra hz
    have hz' : r = 0 := by omega
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    simp only [hz', Nat.cast_zero, zero_mul] at hr
    linarith
  obtain ⟨sample, F, _, hF, hFm, ha⟩ := section16_box_recovered_good_set P T I hprod
    hInonempty D phi ell (fun h _ i => hell h i) (fun h hh x hx hz =>
      hcover h x (by
        rw [appendCoordinate_eq_snoc]
        exact (hprod.mem_snoc h x).mpr ⟨hh, hx⟩) hz) τ hq hτ hτ1 hr
  obtain ⟨p, G, L, S, nu, hp, hG, hGm, hSpart, hSproper, hnu, hc⟩ :=
    ha.synchronized_compressed_cover hD hsections hrpos hs ε hε hε1 T I hT hI hstep u hu.symm
      hk hm hmT hmI hv hvscale (2 * τ) (hcarrier ▸ hF) (hcarrier ▸ hFm)
  refine ⟨p, G, L, S, nu, hp, hG.trans hF, ?_, ?_, hSproper, hnu, hc⟩
  · simpa only [← hcarrier] using hGm
  · change IsPartition (fun j => (S j).carrier) P.carrier
    rw [hcarrier]
    exact hSpart

end LeanProofs.GowersSzemeredi
