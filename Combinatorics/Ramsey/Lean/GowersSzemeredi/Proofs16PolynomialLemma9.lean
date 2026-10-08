import GowersSzemeredi.Proofs16PolynomialLemma6
import GowersSzemeredi.Proofs16WithLemma9

/-! The polynomial recurrence in the line-cover assembly of Lemma 16.9.

The remainder cover supplies a common lower cell width. Above the stated
localized threshold, the improved Lemma 16.6 gives a common width depending
on the supplied spectrum-count bound. Flattening the local covers preserves
this width, the original remainder graph-count bound, and the required good
mass. Spectrum structure, induced selection, and the remainder cover remain
explicit hypotheses.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Lemma 16.9 with a uniform reciprocal-polynomial spectrum-count width,
above the localized input threshold in each remainder-cover cell. -/
theorem exists_polynomial_lemma_16_9 (k : Nat) :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N m n : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb (sigma / 2) → 0 ≤ Eb (sigma / 2) →
    0 < n → section16SimultaneousThreshold k C p (Nat.floor (Qb (sigma / 2))) ≤ n →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let r := section16Lemma9R theta gamma k
    let B1 := section16GoodDomain B H1 Y x0
    let w := (m : Real) ^ ((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r)
    4 ≤ w → (n : Real) ≤ (w / 8) ^ (Eb (sigma / 2)) →
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    MultiplyLinearFunction gamma r B1 (section16PhiRemainder phi x0) →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
        Section16LineCover P B1 (section16PhiOne phi x0) sigma
          ((zeta / 2) * Real.sqrt
            ((n : Real) ^ section16SimultaneousExponent k p (Nat.floor (Qb (sigma / 2)))))
          qGamma := by
  obtain ⟨C, p, hC, hp, hlemma6⟩ := exists_polynomial_lemma_16_6 k
  refine ⟨C, p, hC, hp, ?_⟩
  intro N m n _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha hn hnthreshold
    B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hw hncell hH1 hML hselection hidentity hrem P hP hmP
  classical
  let theta1 := section16ThetaOne theta gamma k
  let delta := section16Delta theta1
  let zeta := section16Zeta theta gamma k
  let r := section16Lemma9R theta gamma k
  let B1 := section16GoodDomain B H1 Y x0
  have hsHalf : 0 < sigma / 2 := by positivity
  have hsHalf1 : sigma / 2 ≤ 1 := by linarith
  obtain ⟨M, qGamma, F, R, mu, hFsub, hFmass, hRpart, hRproper, hqGamma,
      hRwidth, hmu, hremCover⟩ := hrem (sigma / 2) hsHalf hsHalf1 P hP
  let w := (m : Real) ^ ((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r)
  have harg (s : Real) : s⁻¹ * (sigma / 2) = sigma / (2 * s) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hcell (j : Fin M) : w ≤ (R j).width := by
    have hc : 0 ≤ multipleC (r⁻¹ * (sigma / 2)) gamma (k + 1) :=
      (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 1 + 8) ≠ 0)).pow_nonneg _
    have hexp : 0 ≤ (multipleC (r⁻¹ * (sigma / 2)) gamma (k + 1)) ^ r := Real.rpow_nonneg hc _
    have h := (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) hexp).trans (hRwidth j)
    simpa only [w, harg] using h
  have hfour (j : Fin M) : 4 ≤ (R j).width := by
    exact_mod_cast hw.trans (hcell j)
  have hnscale (j : Fin M) : (n : Real) ≤ (((R j).width : Real) / 8) ^ (Eb (sigma / 2)) := by
    exact hncell.trans (Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right (hcell j) (by norm_num)) ha)
  have hlocal (j : Fin M) := hlemma6 N (R j).width n hk theta gamma (sigma / 2)
    ht ht1 hg hg1 hsHalf hsHalf1 Qb Eb hQ ha (hfour j) hn (hnscale j) hnthreshold
    B phi H Jbase H1 Y phiPrime hH1 hML hselection
    (R j) (boxInit (R j)) ((R j).axis (Fin.last k)) (hRproper j) (boxInit_last_product (R j)) le_rfl
  choose G L S T J hGsub hGmass hSpart hSproper hSproduct hSwidth hSlin using hlocal
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
  have hext (j : Fin M) (a : Fin (L j)) (h : Point N k) :
      ∃ ell : ZMod N → ZMod N, LinearOn Finset.univ ell ∧
        (h ∈ G j ∧ h ∈ H1 ∧ h ∈ (T j a).carrier →
          ∀ x ∈ (J j a).carrier.filter (fun x => (h, x) ∈ section16InducedDomain B H Y),
            phiPrime h x = ell x) :=
    conditional_affine_extension _ _ _ (fun hh => hSlin j a h hh.1 hh.2.1 hh.2.2)
  choose ell hell hellEq using hext
  let e := section5NatFlattenEquiv L
  let lines (j : Fin M) (a : Fin (L j)) (h : Point N k) (i : Fin qGamma) (x : ZMod N) :=
    (-1 : ZMod N) ^ k * ell j a h x + mu j i (appendCoordinate h x)
  refine ⟨qGamma, ?_, E, ∑ j, L j, boxFlatten L S,
    (fun a => T (e.symm a).1 (e.symm a).2),
    (fun a => J (e.symm a).1 (e.symm a).2),
    (fun a => lines (e.symm a).1 (e.symm a).2), hEsub, hEmass,
    boxFlatten_partition P R L S hRpart hSpart, (fun a => hSproper _ _), ?_, ?_, ?_, ?_⟩
  · simpa only [section16Lemma9QBound, harg] using hqGamma
  · intro a
    exact hSproduct _ _
  · intro a
    exact hSwidth _ _
  · intro a h i
    exact affine_plus_multilinear_fibres (mu (e.symm a).1) (hmu (e.symm a).1) h
      (ell (e.symm a).1 (e.symm a).2 h) (hell _ _ _) ((-1 : ZMod N) ^ k) i
  · intro a h x hhT hzB hzE hzS
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
    have hHsub : H1 ⊆ H := by rw [hH1]; exact Finset.inter_subset_left
    have hdomain := section16GoodDomain_fibre_mem B H H1 Y x0 h x hHsub hzB
    have hxJ : x ∈ (J j b).carrier := by
      have h := ((hSproduct j b).mem_snoc h x).mp (by simpa only [appendCoordinate_eq_snoc] using hzS)
      exact h.2
    have hphi := hellEq j b h ⟨hhG, hdomain.1, hhT⟩ x (Finset.mem_filter.mpr ⟨hxJ, hdomain.2⟩)
    have hgraph : (appendCoordinate h x, section16PhiRemainder phi x0 (appendCoordinate h x)) ∈
        partialGraph B1 (section16PhiRemainder phi x0) :=
      Finset.mem_image.mpr ⟨appendCoordinate h x, hzB, rfl⟩
    obtain ⟨i, hi⟩ := hremCover j (appendCoordinate h x) hzR hzF _ hgraph
    refine ⟨i, ?_⟩
    have hid := hidentity (appendCoordinate h x) hzB
    simp only [section16PhiPrimeLift, section16Init_appendCoordinate, section16Last_appendCoordinate] at hid
    change _ = lines j b h i x
    dsimp only [lines]
    rw [hid, hphi, hi]

end LeanProofs.GowersSzemeredi
