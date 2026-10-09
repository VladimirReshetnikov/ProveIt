import GowersSzemeredi.Proofs16PolynomialAllScaleLemma6
import GowersSzemeredi.Proofs16WithLemma9

/-! The all-scale polynomial recurrence bound in Lemma 16.9.

The remainder cover multiplies the input-width exponent, while the
polynomial spectrum-count prefactor and the graph-count bound are retained.
This version applies to every proper input box without a localized width
threshold. Spectrum structure, induced selection, and the remainder cover
are still hypotheses.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Transfer a common power lower bound on cell widths through the new
polynomial linearity-width function. -/
theorem section16PolynomialLinearityWidth_le_cell_width {m n k C p q : Nat}
    {a c zeta : Real} (hz : 0 ≤ zeta) (ha : 0 ≤ a)
    (hcell : (m : Real) ^ c ≤ n) :
    section16PolynomialLinearityWidth m k C p q (c * a) zeta ≤
      section16PolynomialLinearityWidth n k C p q a zeta := by
  unfold section16PolynomialLinearityWidth
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [mul_div_assoc, Real.rpow_mul (Nat.cast_nonneg m)]
  exact Real.rpow_le_rpow (by positivity) hcell (div_nonneg ha (by positivity))

/-- The statement of `exists_all_scale_polynomial_lemma_16_9` at fixed constants. -/
def AllScalePolynomialLemma169At (k : Nat) (C p : Nat) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb (sigma / 2) → 0 < Eb (sigma / 2) →
      Eb (sigma / 2) ≤ 1 →
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
          (section16PolynomialLinearityWidth m k C p (Nat.floor (Qb (sigma / 2)))
            (((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r) * Eb (sigma / 2)) zeta)
          qGamma

/-- `exists_all_scale_polynomial_lemma_16_9` at the constants of its input. -/
theorem allScalePolynomialLemma169At_of (k : Nat) {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hlemma6 : AllScalePolynomialLemma166At k C p) : AllScalePolynomialLemma169At k C p := by
  unfold AllScalePolynomialLemma169At
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hH1 hML hselection hidentity hrem P hP hmP
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
  have hlocal (j : Fin M) := hlemma6 N (R j).width hk theta gamma (sigma / 2)
    ht ht1 hg hg1 hsHalf hsHalf1 Qb Eb hQ ha ha1 B phi H Jbase H1 Y phiPrime hH1 hML hselection
    (R j) (boxInit (R j)) ((R j).axis (Fin.last k)) (hRproper j) (boxInit_last_product (R j)) le_rfl
  choose G L S T J hGsub hGmass hSpart hSproper hSproduct hSwidth hSlin using hlocal
  let qDelta := Nat.floor (Qb (sigma / 2))
  have hz : 0 ≤ zeta := (section16Zeta_pos_le_half k ht ht1 hg hg1).1.le
  have harg (s : Real) : s⁻¹ * (sigma / 2) = sigma / (2 * s) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hwidth (j : Fin M) (a : Fin (L j)) :
      section16PolynomialLinearityWidth m k C p qDelta
        (((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r) * Eb (sigma / 2)) zeta ≤ (S j a).width := by
    have hc : 0 ≤ multipleC (r⁻¹ * (sigma / 2)) gamma (k + 1) :=
      (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 1 + 8) ≠ 0)).pow_nonneg _
    have hexp : 0 ≤ (multipleC (r⁻¹ * (sigma / 2)) gamma (k + 1)) ^ r := Real.rpow_nonneg hc _
    have hcell : (m : Real) ^ ((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r) ≤ (R j).width := by
      have h := (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) hexp).trans (hRwidth j)
      simpa only [harg] using h
    exact (section16PolynomialLinearityWidth_le_cell_width hz ha.le hcell).trans (hSwidth j a)
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
    exact hwidth _ _
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

/-- Lemma 16.9 with a polynomial spectrum-count width at every input scale. -/
theorem exists_all_scale_polynomial_lemma_16_9 (k : Nat) :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb (sigma / 2) → 0 < Eb (sigma / 2) →
      Eb (sigma / 2) ≤ 1 →
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
          (section16PolynomialLinearityWidth m k C p (Nat.floor (Qb (sigma / 2)))
            (((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r) * Eb (sigma / 2)) zeta)
          qGamma := by
  obtain ⟨C, p, hC, hp, hlemma6⟩ := exists_all_scale_polynomial_lemma_16_6 k
  exact ⟨C, p, hC, hp, allScalePolynomialLemma169At_of k hC hp hlemma6⟩

end LeanProofs.GowersSzemeredi
