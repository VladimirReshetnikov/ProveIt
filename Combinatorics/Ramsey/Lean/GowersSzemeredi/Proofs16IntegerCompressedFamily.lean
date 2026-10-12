import GowersSzemeredi.Proofs16IntegerRelationLift

/-! Synchronized sampled-slice compression with integer product cells.
The candidate count, loss and short-axis width are unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_synchronize_integer_base_cover_family {N k M v : Nat} [NeZero N] {C ι : Type*}
    (T : Box N k) (I : NatAP) (hI : I.IsProper) (hIN : I.carrier ⊆ Finset.range N)
    (R : Fin M → Box N k) (hRpart : IsBoxPartition R T) (hR : ∀ j, (R j).IsAscendingInteger)
    (B : Fin M → NatAP) (axis : Fin k)
    (hB : ∀ j, (B j).IsProper) (hBN : ∀ j, (B j).carrier ⊆ Finset.range N)
    (hparallel : ∀ j, (B j).step = I.step)
    (hsub : ∀ j, ((R j).axis axis).carrier ⊆ ((B j).toModAP N).carrier)
    (hL : ∀ j, (B j).length ≤ I.length)
    (hv : 1 ≤ v) (hfit : ∀ j, v ^ 2 ≤ (R j).width - 1)
    (D G : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
    (mu : Fin M → C → Point N (k + 1) → ZMod N)
    (hmu : ∀ j c, IsMultilinear (mu j c))
    (hcover : ∀ a j z, section16Init z ∈ (R j).carrier → z ∈ D a → z ∈ G a →
      ∃ c, phi a z = mu j c z) :
    ∃ (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → C → Point N (k + 1) → ZMod N),
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier (I.toModAP N).carrier) ∧
      (∀ j, (S j).IsAscendingInteger ∧ v - 1 ≤ (S j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (S j).carrier → z ∈ D a → z ∈ G a → ∃ c, phi a z = nu j c z := by
  classical
  choose L S J hSpart hSproper hSproduct hJlength using fun j =>
    ascending_box_product_tiling_of_contained_integer_axis (R j) (hR j) (B j) I axis
      (hB j) hI (hBN j) hIN (hparallel j) (hsub j) (hL j) hv (hfit j)
  let e := section5NatFlattenEquiv L
  refine ⟨∑ j, L j, boxFlatten L S, fun j => mu (e.symm j).1,
    finsetPartition_flatten L (fun j => lastProductSet (R j).carrier (I.toModAP N).carrier)
      (lastProductSet T.carrier (I.toModAP N).carrier) (fun j a => (S j a).carrier)
      (lastProductSet_partition _ _ _ hRpart) hSpart,
    fun j => hSproper _ _, fun j c => hmu _ c, ?_⟩
  intro a j z hz hD hG
  have hp := (hSproduct (e.symm j).1 (e.symm j).2).1
  change z ∈ (S (e.symm j).1 (e.symm j).2).carrier at hz
  rw [hp] at hz
  exact hcover a _ z (Finset.mem_filter.mp hz).2.1 hD hG

/-- **Synchronized compressed cover for a family.** One cover of a relation
containing all members' sampled slices; each member interpolates its own
candidates; one common good set `F′` inside every member's recovered set. -/
theorem section16_synchronized_integer_compressed_cover_family
    {N k r m v : Nat} [Fact N.Prime] {ι : Type}
    {D F : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {sample : ι → Fin r → ZMod N}
    {Pb Eb : Real → Real} {Gs : Finset (Point N k × ZMod N)}
    (ha : ∀ a, Section16SampledOrAnchoredOn (D a) (phi a) (sample a) (F a))
    (hslice : IntegerMultiplyLinearWith Pb Eb Gs)
    (hGs : ∀ a h i, appendCoordinate h (sample a i) ∈ D a →
      (h, phi a (appendCoordinate h (sample a i))) ∈ Gs)
    (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hPb : 0 ≤ Pb ε) (hEb : 0 ≤ Eb ε)
    (T : Box N k) (I : NatAP) (hT : T.IsAscendingInteger) (hI : I.IsProper) (hIN : I.carrier ⊆ Finset.range N)
    (hstep : (I.toModAP N).step = T.commonDiff)
    (hk : 0 < k) (hm : 4 ≤ m) (hmT : m ≤ T.width) (hmI : m ≤ I.length)
    (hv : 1 ≤ v)
    (hvscale : (v : ℝ) ^ 2 + 1 ≤ ((m : ℝ) / 8) ^ (Eb ε))
    (η : ℝ) (F' : Finset (Point N (k + 1))) (hF'c : ∀ a, F' ⊆ F a)
    (hF : F' ⊆ lastProductSet T.carrier (I.toModAP N).carrier)
    (hFm : (1 - η) * ((lastProductSet T.carrier (I.toModAP N).carrier).card : ℝ) ≤ F'.card) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → ι × Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ Pb ε ∧
      G ⊆ F' ∧ (1 - η - ε) * ((lastProductSet T.carrier (I.toModAP N).carrier).card : ℝ) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier (I.toModAP N).carrier) ∧
      (∀ j, (S j).IsAscendingInteger ∧ v - 1 ≤ (S j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (S j).carrier → z ∈ D a → z ∈ G → ∃ c, phi a z = nu j c z := by
  classical
  obtain ⟨p, H, b, P, n, R, mu, hp, hH, hHm, hPpart, hPproper,
      hPaxes, hPstep, hRpart, hRproper, hRwidth, hmu, hc⟩ :=
    hslice.short_parent_cover ε hε hε1 hPb hEb T (I.toModAP N) hT
      (I.toModAP_hasIntegerRepresentatives hI hIN).isProper hk hm hmT hmI
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
  have hwidth2 (j : Fin (∑ a, n a)) : 2 ≤ (R' j).width := by
    have h := hfit j
    have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ hv
    omega
  have hsub (j : Fin (∑ a, n a)) :
      ((R' j).axis axis).carrier ⊆ ((P (e.symm j).1).axis axis).carrier :=
    (R' j).axis_carrier_subset_of_carrier_subset (P (e.symm j).1) (hne j)
      (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) axis
  choose d A hd hcommon hA using hPproper
  have hPcert (j : Fin b) : (P j).IsAscendingInteger :=
    ⟨d j, A j, hd j, hcommon j, hA j⟩
  let parent (j : Fin (∑ a, n a)) := A (e.symm j).1 axis
  have hparentN (j : Fin (∑ a, n a)) : (parent j).carrier ⊆ Finset.range N :=
    (hA (e.symm j).1 axis).2.2.1
  have hparentEq (j : Fin (∑ a, n a)) : (parent j).toModAP N = (P (e.symm j).1).axis axis :=
    (hA (e.symm j).1 axis).2.2.2
  have hparentLen (j : Fin (∑ a, n a)) : 2 ≤ (parent j).length := by
    have hc := Finset.card_le_card (hsub j)
    rw [show ((R' j).axis axis).carrier.card = ((R' j).axis axis).length from
      (hRproper (e.symm j).1 (e.symm j).2).isProper axis,
      show ((P (e.symm j).1).axis axis).carrier.card = ((P (e.symm j).1).axis axis).length from
        (hPcert (e.symm j).1).isProper axis] at hc
    change 2 ≤ ((parent j).toModAP N).length
    rw [hparentEq j]
    exact (hwidth2 j).trans (((R' j).width_le_axis_length axis).trans hc)
  have hparallel (j : Fin (∑ a, n a)) : (parent j).step = I.step := by
    apply (parent j).step_eq_of_mod_step_eq I (hparentN j) hIN (hparentLen j) (by omega)
    rw [hparentEq j, (P _).axis_step, hPstep, hstep]
  have hparentI (j : Fin (∑ a, n a)) : (parent j).length ≤ I.length := by
    change ((parent j).toModAP N).length ≤ (I.toModAP N).length
    rw [hparentEq j]
    exact (hPaxes (e.symm j).1 axis).2.2
  have hlift : ∀ (a : ι) (j : Fin (∑ a, n a)),
      ∃ nu : Fin (section16CompressedCandidateCount r p) → Point N (k + 1) → ZMod N,
        (∀ ij, IsMultilinear (nu ij)) ∧
        ∀ h ∈ H ∩ (R' j).carrier, ∀ x, appendCoordinate h x ∈ D a →
          appendCoordinate h x ∈ F a →
            ∃ ij, phi a (appendCoordinate h x) = nu ij (appendCoordinate h x) := by
    intro a j
    apply (ha a).compressed_multilinear_cover hr (H ∩ (R' j).carrier)
      (fun _ => mu (e.symm j).1 (e.symm j).2) (fun _ => hmu _ _)
    intro h hh i hi _
    obtain ⟨hhH, hhR⟩ := Finset.mem_inter.mp hh
    exact hc (e.symm j).1 (e.symm j).2 h hhR hhH (phi a (appendCoordinate h (sample a i)))
      (hGs a h i hi)
  choose nu hnu hcov using hlift
  let G := F' ∩ lastProductSet H (I.toModAP N).carrier
  have hprod := lastProductSet_good_mass T.carrier H (I.toModAP N).carrier ε hH hHm
  have hGmass := good_intersection_mass (lastProductSet T.carrier (I.toModAP N).carrier) F'
    (lastProductSet H (I.toModAP N).carrier) η ε hF hprod.1 hFm hprod.2
  let nuAll : Fin (∑ a, n a) → ι × Fin (section16CompressedCandidateCount r p) →
      Point N (k + 1) → ZMod N := fun j c => nu c.1 j c.2
  have hcover : ∀ a j z, section16Init z ∈ (R' j).carrier → z ∈ D a →
      z ∈ (fun _ : ι => G) a → ∃ c, phi a z = nuAll j c z := by
    intro a j z hzR hzD hzG
    obtain ⟨hzF, hzH⟩ := Finset.mem_inter.mp hzG
    have hhH := (Finset.mem_filter.mp hzH).2.1
    have hd : appendCoordinate (section16Init z) (section16Last z) ∈ D a := by
      simpa only [appendCoordinate_init_last] using hzD
    have hf : appendCoordinate (section16Init z) (section16Last z) ∈ F a := by
      simpa only [appendCoordinate_init_last] using hF'c a hzF
    obtain ⟨ij, hij⟩ := hcov a j (section16Init z)
      (Finset.mem_inter.mpr ⟨hhH, hzR⟩) (section16Last z) hd hf
    refine ⟨(a, ij), ?_⟩
    simpa only [appendCoordinate_init_last] using hij
  obtain ⟨L, S, nu', hSpart, hSproper, hnu', hc'⟩ := section16_synchronize_integer_base_cover_family
    T I hI hIN R' hR'part (fun j => hRproper _ _) parent axis
    (fun j => (hA (e.symm j).1 axis).1) hparentN hparallel
    (fun j => by rw [hparentEq j]; exact hsub j) hparentI hv hfit D (fun _ => G) phi nuAll
    (fun j c => hnu c.1 j c.2) hcover
  exact ⟨p, G, L, S, nu', hp, Finset.inter_subset_left, hGmass, hSpart, hSproper, hnu',
    fun a j z hz hzD hzG => hc' a j z hz hzD hzG⟩


end LeanProofs.GowersSzemeredi
