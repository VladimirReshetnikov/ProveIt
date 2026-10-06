import GowersSzemeredi.Proofs16FibreCovers

/-! # Lemma 16.9: two-stage partition and fibrewise affine covers -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The line-cover construction in the prime, positive-dimensional,
proper-input setting inherited from Lemma 16.6. -/
theorem proper_lemma_16_9 :
  ∀ (N k m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let t := section16T delta theta1 k
    let r := section16Lemma9R theta gamma k
    let B1 := section16GoodDomain B H1 Y x0
    H1 = H ∩ Jbase →
    MultiplyLinear delta t
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    MultiplyLinearFunction gamma r B1 (section16PhiRemainder phi x0) →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      ∃ qGamma qDelta : Nat,
        (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
        (qDelta : Real) ≤
          section16Lemma9DeltaQBound sigma delta theta1 k ∧
        Section16LineCover P B1 (section16PhiOne phi x0) sigma
          (section16Lemma9Width m qDelta k sigma theta gamma delta theta1 zeta)
          qGamma := by
  intro N k m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 B phi H Jbase H1 Y phiPrime x0
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
  have hlocal (j : Fin M) := proper_lemma_16_6 N k (R j).width hk theta gamma (sigma / 2)
    ht ht1 hg hg1 hsHalf hsHalf1 B phi H Jbase H1 Y phiPrime hH1 hML hselection
    (R j) (boxInit (R j)) ((R j).axis (Fin.last k)) (hRproper j) (boxInit_last_product (R j)) le_rfl
  choose qD hqD G L S T J hGsub hGmass hSpart hSproper hSproduct hSwidth hSlin using hlocal
  let bound := section16Lemma6QBound (sigma / 2) delta theta1 k
  have hb : 0 ≤ bound := by
    obtain ⟨hth, hth1, hd, hd1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
    have htb := section16T_one_le k hd hd1 hth hth1
    have htp : 0 < section16T (section16Delta (section16ThetaOne theta gamma k))
        (section16ThetaOne theta gamma k) k := by linarith
    dsimp [bound, delta, theta1]
    unfold section16Lemma6QBound multipleQ multipleC
    positivity
  let qDelta := Nat.floor bound
  have hqDle (j : Fin M) : qD j ≤ qDelta := Nat.le_floor (hqD j)
  obtain ⟨ha, ha1⟩ := section16_lemma6_exponent_bounds k ht ht1 hg hg1 hsHalf hsHalf1
  have hz : 0 ≤ zeta := (section16Zeta_pos_le_half k ht ht1 hg hg1).1.le
  have harg (s : Real) : s⁻¹ * (sigma / 2) = sigma / (2 * s) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hwidth (j : Fin M) (a : Fin (L j)) :
      section16Lemma9Width m qDelta k sigma theta gamma delta theta1 zeta ≤ (S j a).width := by
    have hc : 0 ≤ multipleC (r⁻¹ * (sigma / 2)) gamma (k + 1) :=
      (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 1 + 8) ≠ 0)).pow_nonneg _
    have hexp : 0 ≤ (multipleC (r⁻¹ * (sigma / 2)) gamma (k + 1)) ^ r := Real.rpow_nonneg hc _
    have hcell : (m : Real) ^ ((multipleC (sigma / (2 * r)) gamma (k + 1)) ^ r) ≤ (R j).width := by
      have h := (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) hexp).trans (hRwidth j)
      simpa only [harg] using h
    exact (section16Lemma9Width_le_cell_width hz ha.le hcell).trans
      ((section16Lemma6Width_antitone_count (hqDle j) hz ha).trans (hSwidth j a))
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
  refine ⟨qGamma, qDelta, ?_, ?_, E, ∑ j, L j, boxFlatten L S,
    (fun a => T (e.symm a).1 (e.symm a).2),
    (fun a => J (e.symm a).1 (e.symm a).2),
    (fun a => lines (e.symm a).1 (e.symm a).2), hEsub, hEmass,
    boxFlatten_partition P R L S hRpart hSpart, (fun a => hSproper _ _), ?_, ?_, ?_, ?_⟩
  · simpa only [section16Lemma9QBound, harg] using hqGamma
  · have hbound : bound = section16Lemma9DeltaQBound sigma delta theta1 k := by
      dsimp [bound, section16Lemma6QBound, section16Lemma9DeltaQBound]
      congr 2
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    change (qDelta : Real) ≤ section16Lemma9DeltaQBound sigma delta theta1 k
    rw [← hbound]
    exact Nat.floor_le hb
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

/-- Exact companion for the explicitly migrated proper-box statement. -/
theorem lemma_16_9_holds : lemma_16_9 := proper_lemma_16_9

/-- The proved line-cover construction supplies the proper all-box premise
used by the remaining multilinearity step. -/
theorem section16_all_box_line_covers :
  ∀ (N k : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let t := section16T delta theta1 k
    let r := section16Lemma9R theta gamma k
    let B1 := section16GoodDomain B H1 Y x0
    H1 = H ∩ Jbase →
    MultiplyLinear delta t
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    MultiplyLinearFunction gamma r B1 (section16PhiRemainder phi x0) →
    Section16AllBoxLineCovers theta gamma B1 (section16PhiOne phi x0) := by
  intro N k _ _ hk theta gamma ht ht1 hg hg1 B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hH1 hML hselection hidentity hrem
  intro sigma hs hs1 m P hP hmP
  exact proper_lemma_16_9 N k m hk theta gamma sigma ht ht1 hg hg1 hs hs1
    B phi H Jbase H1 Y phiPrime x0 hH1 hML hselection hidentity hrem P hP hmP

end LeanProofs.GowersSzemeredi
