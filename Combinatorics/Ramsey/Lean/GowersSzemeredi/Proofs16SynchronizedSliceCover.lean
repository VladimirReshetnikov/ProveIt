import GowersSzemeredi.Proofs16SynchronizedCover

/-! # A synchronized multilinear cover from recovered slices

Short parent cells supply compatible final-axis tilings. The width budget
is stated explicitly before rounding: v^2+1 must fit below the refined
base width. This is a local quantitative conclusion, not the unproved
comparison with the fixed controls in Lemma 16.10.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem Section16SampledOrAnchoredOn.synchronized_cover {N k r m v : Nat} [NeZero N]
    {gamma s : ℝ} {B D F : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {sample : Fin r → ZMod N}
    (ha : Section16SampledOrAnchoredOn D phi sample F) (hD : D ⊆ B)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi)
    (hr : 0 < r) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (T : Box N k) (I : ModAP N) (hT : T.IsProper) (hI : I.IsProper)
    (hstep : I.step = T.commonDiff) (u : (ZMod N)ˣ) (hu : I.step = (↑u : ZMod N))
    (hk : 0 < k) (hm : 4 ≤ m) (hmT : m ≤ T.width) (hmI : m ≤ I.length)
    (hv : 1 ≤ v)
    (hvscale : (v : ℝ) ^ 2 + 1 ≤ ((m : ℝ) / 8) ^
      ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s)))
    (η : ℝ) (hF : F ⊆ lastProductSet T.carrier I.carrier)
    (hFm : (1 - η) * ((lastProductSet T.carrier I.carrier).card : ℝ) ≤ F.card) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → ((Fin r × Fin p) ⊕ (Fin r × Fin r × Fin p × Fin p)) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
      G ⊆ F ∧ (1 - η - ε) * ((lastProductSet T.carrier I.carrier).card : ℝ) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j ij, IsMultilinear (nu j ij)) ∧
      ∀ j z, z ∈ (S j).carrier → z ∈ D → z ∈ G → ∃ ij, phi z = nu j ij z := by
  classical
  let Gamma := fun i : Fin r => partialGraph (section16FinalCoordinateSection B (sample i))
    (section16FinalCoordinateRestriction phi (sample i))
  have hGamma : ∀ i, ProperMultiplyLinear gamma s (Gamma i) := fun i => hsections (sample i)
  have hML := BaseCase.properMultiplyLinear_finsetUnion gamma s hs Gamma hr hGamma
  obtain ⟨p, H, b, P, n, R, mu, hp, hH, hHm, hPpart, hPproper,
      hPaxes, hPstep, hRpart, hRproper, hRwidth, hmu, hc⟩ :=
    hML.short_parent_cover ε hε hε1 T I hT hI hk hm hmT hmI
  let e := section5NatFlattenEquiv n
  let R' := boxFlatten n R
  have hR'part : IsBoxPartition R' T := boxFlatten_partition T P n R hPpart hRpart
  have hfit (j : Fin (∑ a, n a)) : v ^ 2 ≤ (R' j).width - 1 := by
    have h := hvscale.trans (hRwidth (e.symm j).1 (e.symm j).2)
    have h' : v ^ 2 + 1 ≤ (R' j).width := by exact_mod_cast h
    omega
  have hne (j : Fin (∑ a, n a)) : (R' j).carrier.Nonempty := by
    apply Box.carrier_nonempty_of_axis_pos
    intro a
    have hw := (R' j).width_le_axis_length a
    have hf := hfit j
    have hv2 : 1 ≤ v ^ 2 := by nlinarith
    omega
  let axis : Fin k := ⟨0, hk⟩
  let parent := fun j : Fin (∑ a, n a) => (P (e.symm j).1).axis axis
  have hsub (j : Fin (∑ a, n a)) : ((R' j).axis axis).carrier ⊆ (parent j).carrier :=
    (R' j).axis_carrier_subset_of_carrier_subset (P (e.symm j).1) (hne j)
      (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) axis
  have hparentstep (j : Fin (∑ a, n a)) : (parent j).step = (↑u : ZMod N) := by
    dsimp only [parent]
    rw [(P _).axis_step, hPstep, ← hstep, hu]
  have hparallel (j : Fin (∑ a, n a)) : I.step = (parent j).step := by
    rw [hparentstep, hu]
  have hlift : ∀ j : Fin (∑ a, n a),
      ∃ nu : ((Fin r × Fin p) ⊕ (Fin r × Fin r × Fin p × Fin p)) → Point N (k + 1) → ZMod N,
        (∀ ij, IsMultilinear (nu ij)) ∧
        ∀ h ∈ H ∩ (R' j).carrier, ∀ x, appendCoordinate h x ∈ D →
          appendCoordinate h x ∈ F → ∃ ij, phi (appendCoordinate h x) = nu ij (appendCoordinate h x) := by
    intro j
    apply ha.multilinear_cover (H ∩ (R' j).carrier)
      (fun _ => mu (e.symm j).1 (e.symm j).2) (fun _ => hmu _ _)
    intro h hh i hi _
    obtain ⟨hhH, hhR⟩ := Finset.mem_inter.mp hh
    apply hc (e.symm j).1 (e.symm j).2 h hhR hhH (phi (appendCoordinate h (sample i)))
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD hi⟩, rfl⟩
  choose nu hnu hcov using hlift
  let G := F ∩ lastProductSet H I.carrier
  have hprod := lastProductSet_good_mass T.carrier H I.carrier ε hH hHm
  have hGmass := good_intersection_mass (lastProductSet T.carrier I.carrier) F
    (lastProductSet H I.carrier) η ε hF hprod.1 hFm hprod.2
  have hcover : ∀ j z, section16Init z ∈ (R' j).carrier → z ∈ D → z ∈ G →
      ∃ ij, phi z = nu j ij z := by
    intro j z hzR hzD hzG
    obtain ⟨hzF, hzH⟩ := Finset.mem_inter.mp hzG
    have hhH := (Finset.mem_filter.mp hzH).2.1
    have hd : appendCoordinate (section16Init z) (section16Last z) ∈ D := by
      simpa only [appendCoordinate_init_last] using hzD
    have hf : appendCoordinate (section16Init z) (section16Last z) ∈ F := by
      simpa only [appendCoordinate_init_last] using hzF
    simpa only [appendCoordinate_init_last] using hcov j (section16Init z)
      (Finset.mem_inter.mpr ⟨hhH, hzR⟩) (section16Last z) hd hf
  obtain ⟨L, S, nu', hSpart, hSproper, hnu', hc'⟩ := section16_synchronize_base_cover
    T I hI R' hR'part (fun j => hRproper _ _) parent axis (fun _ => u)
    hparentstep hparallel hsub (fun j => (hPaxes (e.symm j).1 axis).2.1)
    (fun j => (hPaxes (e.symm j).1 axis).2.2) hv hfit D G phi nu hnu hcover
  exact ⟨p, G, L, S, nu', hp, Finset.inter_subset_left, hGmass, hSpart, hSproper, hnu', hc'⟩

end LeanProofs.GowersSzemeredi
