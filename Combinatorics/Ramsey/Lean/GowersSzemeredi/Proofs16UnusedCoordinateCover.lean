import GowersSzemeredi.Proofs16SynchronizedSliceCover
import GowersSzemeredi.Proofs16LiftWidth

/-! Extend a multiply-linear partial function across one unused coordinate.
Compatible box tiling retains the number of graphs and the exceptional mass;
only the explicit square-root width loss remains. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem MultiplyLinearFunction.unused_coordinate_cover {N k m v : Nat} [NeZero N]
    {gamma s : Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearFunction gamma s B phi)
    (epsilon : Real) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (T : Box N k) (I : ModAP N) (hT : T.IsProper) (hI : I.IsProper)
    (hstep : I.step = T.commonDiff) (u : (ZMod N)ˣ) (hu : I.step = (↑u : ZMod N))
    (hk : 0 < k) (hm : 4 ≤ m) (hmT : m ≤ T.width) (hmI : m ≤ I.length)
    (hv : 1 ≤ v)
    (hfit : (v : Real) ^ 2 + 1 ≤ ((m : Real) / 8) ^ ((multipleC (s⁻¹ * epsilon) gamma k) ^ s)) :
    ∃ (q : Nat) (G : Finset (Point N (k + 1))) (L : Nat)
      (S : Fin L → Box N (k + 1)) (mu : Fin L → Fin q → Point N (k + 1) → ZMod N),
      (q : Real) ≤ (multipleQ (s⁻¹ * epsilon) gamma k) ^ s ∧
      G ⊆ lastProductSet T.carrier I.carrier ∧
      (1 - epsilon) * ((lastProductSet T.carrier I.carrier).card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (S j).carrier → section16Init z ∈ B → z ∈ G →
        ∃ i, phi (section16Init z) = mu j i z := by
  classical
  obtain ⟨q, H, b, P, n, R, mu, hq, hH, hHm, hPpart, hPproper,
      hPaxes, hPstep, hRpart, hRproper, hRwidth, hmu, hc⟩ :=
    hML.short_parent_cover epsilon he he1 T I hT hI hk hm hmT hmI
  let e := section5NatFlattenEquiv n
  let R' := boxFlatten n R
  have hR'part : IsBoxPartition R' T := boxFlatten_partition T P n R hPpart hRpart
  have hvfit (j : Fin (∑ a, n a)) : v ^ 2 ≤ (R' j).width - 1 := by
    have hh := hfit.trans (hRwidth (e.symm j).1 (e.symm j).2)
    have hh' : v ^ 2 + 1 ≤ (R' j).width := by exact_mod_cast hh
    omega
  have hne (j : Fin (∑ a, n a)) : (R' j).carrier.Nonempty := by
    apply Box.carrier_nonempty_of_axis_pos
    intro a
    have hw := (R' j).width_le_axis_length a
    have hh := hvfit j
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
  let G := lastProductSet H I.carrier
  let D := lastProductSet B Finset.univ
  let nu := fun j : Fin (∑ a, n a) => fun i : Fin q =>
    fun z : Point N (k + 1) => mu (e.symm j).1 (e.symm j).2 i (section16Init z)
  have hnu : ∀ j i, IsMultilinear (nu j i) := by
    intro j i
    exact (hmu (e.symm j).1 (e.symm j).2 i).lift_last
  have hcover : ∀ j z, section16Init z ∈ (R' j).carrier → z ∈ D → z ∈ G →
      ∃ i, phi (section16Init z) = nu j i z := by
    intro j z hzR hzD hzG
    have hzB := (Finset.mem_filter.mp hzD).2.1
    have hzH := (Finset.mem_filter.mp hzG).2.1
    exact hc (e.symm j).1 (e.symm j).2 (section16Init z) hzR hzH
      (phi (section16Init z)) (Finset.mem_image.mpr ⟨section16Init z, hzB, rfl⟩)
  obtain ⟨L, S, nu', hSpart, hSproper, hnu', hc'⟩ := section16_synchronize_base_cover
    T I hI R' hR'part (fun j => hRproper _ _) parent axis (fun _ => u)
    hparentstep hparallel hsub (fun j => (hPaxes (e.symm j).1 axis).2.1)
    (fun j => (hPaxes (e.symm j).1 axis).2.2) hv hvfit D G
    (fun z => phi (section16Init z)) nu hnu hcover
  obtain ⟨hG, hGm⟩ := lastProductSet_good_mass T.carrier H I.carrier epsilon hH hHm
  refine ⟨q, G, L, S, nu', hq, hG, hGm, hSpart, hSproper, hnu', ?_⟩
  intro j z hz hzB hzG
  exact hc' j z hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzB, Finset.mem_univ _⟩) hzG

/-- Rounded form: extension across the unused coordinate preserves the
lower-dimensional graph bound and loses only sqrt(width)/4 in width. -/
theorem MultiplyLinearFunction.unused_coordinate_cover_sqrt {N k m : Nat} [NeZero N]
    {gamma s : Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearFunction gamma s B phi)
    (epsilon : Real) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (T : Box N k) (I : ModAP N) (hT : T.IsProper) (hI : I.IsProper)
    (hstep : I.step = T.commonDiff) (u : (ZMod N)ˣ) (hu : I.step = (↑u : ZMod N))
    (hk : 0 < k) (hm : 4 ≤ m) (hmT : m ≤ T.width) (hmI : m ≤ I.length)
    (hw : 16 ≤ ((m : Real) / 8) ^ ((multipleC (s⁻¹ * epsilon) gamma k) ^ s)) :
    ∃ (q : Nat) (G : Finset (Point N (k + 1))) (L : Nat)
      (S : Fin L → Box N (k + 1)) (mu : Fin L → Fin q → Point N (k + 1) → ZMod N),
      (q : Real) ≤ (multipleQ (s⁻¹ * epsilon) gamma k) ^ s ∧
      G ⊆ lastProductSet T.carrier I.carrier ∧
      (1 - epsilon) * ((lastProductSet T.carrier I.carrier).card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ Real.sqrt (((m : Real) / 8) ^
        ((multipleC (s⁻¹ * epsilon) gamma k) ^ s)) / 4 ≤ (S j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (S j).carrier → section16Init z ∈ B → z ∈ G →
        ∃ i, phi (section16Init z) = mu j i z := by
  obtain ⟨v, hv, hvfit, hvwidth⟩ := section16_lift_width_rounding hw
  obtain ⟨q, G, L, S, mu, hq, hG, hGm, hpart, hproper, hmu, hc⟩ :=
    hML.unused_coordinate_cover epsilon he he1 T I hT hI hstep u hu hk hm hmT hmI hv hvfit
  exact ⟨q, G, L, S, mu, hq, hG, hGm, hpart,
    fun j => ⟨(hproper j).1, hvwidth.trans (by exact_mod_cast (hproper j).2)⟩, hmu, hc⟩

end LeanProofs.GowersSzemeredi
