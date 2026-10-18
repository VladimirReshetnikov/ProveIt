import GowersSzemeredi.Proofs16FamilyLemma6
import GowersSzemeredi.Proofs16Lemma9WithRemainderSide

/-! Declarations of `Proofs16FamilyLemma6` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The family Lemma 16.6 contains the single-piece one: take one member and
the restricted spectrum relation as `Γ`. -/
theorem AllScaleFamilyLemma166At.single {k : Nat} {W : Nat → Nat → Real → Real → Real}
    (hfam : AllScaleFamilyLemma166At k W) : AllScaleLemma166WidthAt k W := by
  unfold AllScaleLemma166WidthAt
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime
  dsimp only
  intro hH1 hML hselection P Q I hP hproduct hmP
  have hfreq : ∀ _c : Unit, ∀ x ∈ H1, ∀ r ∈ section16LargeSpectrum B x
      (section16Delta (section16ThetaOne theta gamma k)),
      (x, r) ∈ restrictRelation (section16SpectrumRelation B
        (section16Delta (section16ThetaOne theta gamma k))) Jbase := by
    intro _ x hx r hr
    have hxJ := (Finset.mem_inter.mp (hH1 ▸ hx)).2
    simpa only [restrictRelation, section16SpectrumRelation, Finset.mem_filter,
      Finset.mem_univ, true_and] using And.intro hr hxJ
  have hsub : ∀ _c : Unit, H1 ⊆ H := fun _ => by
    rw [hH1]; exact Finset.inter_subset_left
  obtain ⟨G, M, S, T, A, hGsub, hGmass, hpart, hproper, hprod', hwidth, hlin⟩ :=
    hfam N m hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1 _ hML Unit
      (fun _ => B) (fun _ => phi) (fun _ => H) (fun _ => H1) (fun _ => Y) (fun _ => phiPrime)
      hfreq hsub (fun _ => hselection) P Q I hP hproduct hmP
  exact ⟨G, M, S, T, A, hGsub, hGmass, hpart, hproper, hprod', hwidth,
    fun u h hhG hhH hhT => hlin () u h hhG hhH hhT⟩

end LeanProofs.GowersSzemeredi
