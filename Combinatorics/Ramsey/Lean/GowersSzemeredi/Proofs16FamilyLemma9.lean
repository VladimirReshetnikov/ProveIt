import GowersSzemeredi.Proofs16FamilyLemma6
import GowersSzemeredi.Proofs16FamilyAffineLift

/-! Lemma 16.9 for a family of pieces, on one partition.

Step (B) of Notes L.3, fourth stage. Every member `c` has its own data
`(B c, φ c, H c, H1 c, Y c, φ′ c, x₀ c)` and a sub-domain `D c` of its
good domain. Two common inputs make the members share their cells:
* one relation `Γ` covering all members' large spectra, with a
  `MultiplyLinearWith Qb Eb` cover;
* one relation `Γr` in dimension `k + 1` containing all members' remainder
  graphs on `D c`, with a `MultiplyLinearWith Qr Er` cover.

The remainder cover gives the outer partition and the shared candidate
maps `μ`. On each of its cells the family Lemma 16.6 gives one inner
partition. Each member's lines are its own affine extension of `φ′_c` plus
the shared `μ`. The output is a `Section16LineCoverFamily` with the
single-piece width `W m ⌊Qb(σ/2)⌋ (Er(σ/2)·Eb(σ/2)) ζ` and count
`Qr(σ/2)`.
* `AllScaleFamilyLemma169At`, `allScaleFamilyLemma169At_of`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- **Lemma 16.9 for a family.** -/
def AllScaleFamilyLemma169At (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb Qr Er : Real → Real), 0 ≤ Qb (sigma / 2) → 0 < Eb (sigma / 2) →
      Eb (sigma / 2) ≤ 1 → 0 ≤ Er (sigma / 2) →
    ∀ (Gamma : Finset (Point N k × ZMod N)), MultiplyLinearWith Qb Eb Gamma →
    ∀ (Gr : Finset (Point N (k + 1) × ZMod N)), MultiplyLinearWith Qr Er Gr →
    ∀ (ι : Type) (B : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
      (H H1 : ι → Finset (Point N k))
      (Y : (c : ι) → (h : Point N k) → Finset (Section16CubeElement (B c) h))
      (phiPrime : ι → Point N k → ZMod N → ZMod N) (x0 : ι → Point N k)
      (D : ι → Finset (Point N (k + 1))),
    (∀ c, ∀ x ∈ H1 c, ∀ r ∈ section16LargeSpectrum (B c) x
      (section16Delta (section16ThetaOne theta gamma k)), (x, r) ∈ Gamma) →
    (∀ c, H1 c ⊆ H c) →
    (∀ c, Section16InducedSelection (B c) (phi c) (H c) (Y c)
      (fun h => section16LargeSpectrum (B c) h (section16Delta (section16ThetaOne theta gamma k)))
      (section16Zeta theta gamma k) (phiPrime c)) →
    (∀ c, Section16PhiOneIdentity (section16GoodDomain (B c) (H1 c) (Y c) (x0 c))
      (phi c) (x0 c) (phiPrime c)) →
    (∀ c, D c ⊆ section16GoodDomain (B c) (H1 c) (Y c) (x0 c)) →
    (∀ c, ∀ z ∈ D c, (z, section16PhiRemainder (phi c) (x0 c) z) ∈ Gr) →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ Qr (sigma / 2) ∧
        Section16LineCoverFamily P D (fun c => section16PhiOne (phi c) (x0 c)) sigma
          (W m (Nat.floor (Qb (sigma / 2))) (Er (sigma / 2) * Eb (sigma / 2))
            (section16Zeta theta gamma k))
          qGamma

/-- The family Lemma 16.9 from the family Lemma 16.6. -/
theorem allScaleFamilyLemma169At_of (k : Nat) {W : Nat → Nat → Real → Real → Real}
    (hW : Section16WidthTransfer W)
    (hlemma6 : AllScaleFamilyLemma166At k W) : AllScaleFamilyLemma169At k W := by
  unfold AllScaleFamilyLemma169At
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb Qr Er hQ ha ha1 hEr
    Gamma hML Gr hrem ι B phi H H1 Y phiPrime x0 D hfreq hH1 hselection hidentity hD hGr
    P hP hmP
  classical
  let zeta := section16Zeta theta gamma k
  have hsHalf : 0 < sigma / 2 := by positivity
  have hsHalf1 : sigma / 2 ≤ 1 := by linarith
  obtain ⟨M, qGamma, F, R, mu, hFsub, hFmass, hRpart, hRproper, hqGamma,
      hRwidth, hmu, hremCover⟩ := hrem (sigma / 2) hsHalf hsHalf1 P hP
  have hlocal (j : Fin M) := hlemma6 N (R j).width hk theta gamma (sigma / 2)
    ht ht1 hg hg1 hsHalf hsHalf1 Qb Eb hQ ha ha1 Gamma hML ι B phi H H1 Y phiPrime
    hfreq hH1 hselection
    (R j) (boxInit (R j)) ((R j).axis (Fin.last k)) (hRproper j) (boxInit_last_product (R j)) le_rfl
  choose G L S T J hGsub hGmass hSpart hSproper hSproduct hSwidth hSlin using hlocal
  let qDelta := Nat.floor (Qb (sigma / 2))
  have hz : 0 ≤ zeta := (section16Zeta_pos_le_half k ht ht1 hg hg1).1.le
  have hwidth (j : Fin M) (a : Fin (L j)) :
      W m qDelta (Er (sigma / 2) * Eb (sigma / 2)) zeta ≤ (S j a).width := by
    have hcell : (m : Real) ^ (Er (sigma / 2)) ≤ (R j).width :=
      (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) hEr).trans (hRwidth j)
    exact (hW m (R j).width qDelta (Eb (sigma / 2)) (Er (sigma / 2)) zeta hz ha.le hEr hcell).trans
      (hSwidth j a)
  let U (j : Fin M) := lastProductSet (G j) ((R j).axis (Fin.last k)).carrier
  have hU (j : Fin M) : U j ⊆ (R j).carrier ∧
      (1 - sigma / 2) * ((R j).carrier.card : Real) ≤ (U j).card := by
    have h := lastProductSet_good_mass (boxInit (R j)).carrier (G j)
      ((R j).axis (Fin.last k)).carrier (sigma / 2) (hGsub j) (hGmass j)
    simpa only [U, (boxInit_last_product (R j)).1, lastProductSet] using h
  let V := Finset.univ.biUnion U
  have hV := IsPartition.good_union hRpart U (sigma / 2) (fun j => (hU j).1) (fun j => (hU j).2)
  let E := F ∩ V
  have hEsub : E ⊆ P.carrier := Finset.Subset.trans Finset.inter_subset_left hFsub
  have hEmass : (1 - sigma) * (P.carrier.card : Real) ≤ E.card := by
    have h := good_intersection_mass P.carrier F V (sigma / 2) (sigma / 2) hFsub hV.1 hFmass hV.2
    convert h using 1; ring
  have hext (c : ι) (j : Fin M) (a : Fin (L j)) (h : Point N k) :
      ∃ ell : ZMod N → ZMod N, LinearOn Finset.univ ell ∧
        (h ∈ G j ∧ h ∈ H1 c ∧ h ∈ (T j a).carrier →
          ∀ x ∈ (J j a).carrier.filter
              (fun x => (h, x) ∈ section16InducedDomain (B c) (H c) (Y c)),
            phiPrime c h x = ell x) :=
    conditional_affine_extension _ _ _ (fun hh => hSlin j c a h hh.1 hh.2.1 hh.2.2)
  choose ell hell hellEq using hext
  let e := section5NatFlattenEquiv L
  let lines (c : ι) (j : Fin M) (a : Fin (L j)) (h : Point N k) (i : Fin qGamma) (x : ZMod N) :=
    (-1 : ZMod N) ^ k * ell c j a h x + mu j i (appendCoordinate h x)
  refine ⟨qGamma, hqGamma, E, ∑ j, L j, boxFlatten L S,
    (fun a => T (e.symm a).1 (e.symm a).2),
    (fun a => J (e.symm a).1 (e.symm a).2),
    (fun c a => lines c (e.symm a).1 (e.symm a).2), hEsub, hEmass,
    boxFlatten_partition P R L S hRpart hSpart, (fun a => hSproper _ _), ?_, ?_, ?_, ?_⟩
  · intro a
    exact hSproduct _ _
  · intro a
    exact hwidth _ _
  · intro c a h i
    exact affine_plus_multilinear_fibres (mu (e.symm a).1) (hmu (e.symm a).1) h
      (ell c (e.symm a).1 (e.symm a).2 h) (hell _ _ _ _) ((-1 : ZMod N) ^ k) i
  · intro c a h x hhT hzB hzE hzS
    let j := (e.symm a).1
    let b := (e.symm a).2
    change appendCoordinate h x ∈ (S j b).carrier at hzS
    have hzR : appendCoordinate h x ∈ (R j).carrier := IsPartition.cell_subset (hSpart j) b hzS
    have hzF : appendCoordinate h x ∈ F := (Finset.mem_inter.mp hzE).1
    have hzV : appendCoordinate h x ∈ V := (Finset.mem_inter.mp hzE).2
    have hzU := (IsPartition.good_union_mem_iff hRpart U (fun j => (hU j).1) j hzR).mp hzV
    have hhG : h ∈ G j := by
      have h := (Finset.mem_filter.mp hzU).2.1
      simpa only [section16Init_appendCoordinate] using h
    have hdomain := section16GoodDomain_fibre_mem (B c) (H c) (H1 c) (Y c) (x0 c) h x
      (hH1 c) (hD c hzB)
    have hxJ : x ∈ (J j b).carrier := by
      have h := ((hSproduct j b).mem_snoc h x).mp (by simpa only [appendCoordinate_eq_snoc] using hzS)
      exact h.2
    have hphi := hellEq c j b h ⟨hhG, hdomain.1, hhT⟩ x (Finset.mem_filter.mpr ⟨hxJ, hdomain.2⟩)
    obtain ⟨i, hi⟩ := hremCover j (appendCoordinate h x) hzR hzF _ (hGr c _ hzB)
    refine ⟨i, ?_⟩
    have hid := hidentity c (appendCoordinate h x) (hD c hzB)
    simp only [section16PhiPrimeLift, section16Init_appendCoordinate,
      section16Last_appendCoordinate] at hid
    change _ = lines c j b h i x
    dsimp only [lines]
    rw [hid, hphi, hi]

end LeanProofs.GowersSzemeredi
