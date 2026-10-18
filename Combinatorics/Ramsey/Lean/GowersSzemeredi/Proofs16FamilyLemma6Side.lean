import GowersSzemeredi.Proofs16FamilyLemma6
import GowersSzemeredi.Proofs16Lemma9WithRemainderSide
import GowersSzemeredi.Proofs16ShortScaleSide

/-! Declarations of `Proofs16FamilyLemma6` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The divisor `2p(q+1)^(2^(k+2))` of the simultaneous recurrence exponent. -/
def familyRecDivisor (k p q : Nat) : Nat := 2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))

/-- **Lemma 16.6 for a family, at every scale.** One relation `Γ` covers
the large spectra of all members; one partition makes every member's
induced function linear. -/
def AllScaleFamilyLemma166At (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb sigma → 0 < Eb sigma → Eb sigma ≤ 1 →
    ∀ (Gamma : Finset (Point N k × ZMod N)), MultiplyLinearWith Qb Eb Gamma →
    ∀ (ι : Type) (B : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
      (H H1 : ι → Finset (Point N k))
      (Y : (c : ι) → (h : Point N k) → Finset (Section16CubeElement (B c) h))
      (phiPrime : ι → Point N k → ZMod N → ZMod N),
    (∀ c, ∀ x ∈ H1 c, ∀ r ∈ section16LargeSpectrum (B c) x
      (section16Delta (section16ThetaOne theta gamma k)), (x, r) ∈ Gamma) →
    (∀ c, H1 c ⊆ H c) →
    (∀ c, Section16InducedSelection (B c) (phi c) (H c) (Y c)
      (fun h => section16LargeSpectrum (B c) h (section16Delta (section16ThetaOne theta gamma k)))
      (section16Zeta theta gamma k) (phiPrime c)) →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      P.IsProper → IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, W m (Nat.floor (Qb sigma)) (Eb sigma) (section16Zeta theta gamma k) ≤
                (S u).width) ∧
              ∀ c u h, h ∈ G → h ∈ H1 c → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain (B c) (H c) (Y c)) (phiPrime c h)

/-- **The family Lemma 16.6 from the recurrence profile.** -/
theorem allScaleFamilyLemma166At_of (k : Nat) {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hrec : Section16RecurrenceProfileWith k (familyRecThr k C p) (familyRecExp k p)) :
    AllScaleFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor C) (familyWidthDivisor k p)) := by
  unfold AllScaleFamilyLemma166At
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1 Gamma hML
    ι B phi H H1 Y phiPrime hfreq hH1 hselection P Q I hP hproduct hmP
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  obtain ⟨G, M, S, T, J, hGQ, hGm, hSP, hSpr, hSpd, hSw, hlin⟩ :=
    abstractFamilyLemma166At_of k hC hp hrec N m hk _ sigma hz hzHalf hs hs1 Qb Eb hQ ha ha1 Gamma
      hML ι H1 (fun c x => section16LargeSpectrum (B c) x (section16Delta (section16ThetaOne theta gamma k)))
      (fun c x => Finset.univ.filter fun y => (x, y) ∈ section16InducedDomain (B c) (H c) (Y c))
      phiPrime hfreq (fun c x hx v hv J hJ hd => by
        simpa only [Finset.inter_filter, Finset.inter_univ] using
          (hselection c).2 x (hH1 c hx) v hv J.step hd J rfl hJ)
      P Q I hP hproduct hmP
  refine ⟨G, M, S, T, J, hGQ, hGm, hSP, hSpr, hSpd, hSw, fun c u h hhG hhH hhT => ?_⟩
  simpa only [Finset.inter_filter, Finset.inter_univ] using hlin c u h hhG hhH hhT

end LeanProofs.GowersSzemeredi

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
