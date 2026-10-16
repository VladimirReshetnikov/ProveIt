import GowersSzemeredi.Proofs16Lemma6Parameters

/-! # Lemma 16.6 for proper boxes in the positive-dimensional prime setting

This proof assembles the uniform multilinear cover, short parent geometry,
retiled recurrence, and singleton endpoints at the exact stated width.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Lemma 16.6 with arbitrary spectrum controls.** -/
theorem proper_lemma_16_6_with :
  ∀ (N k m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb sigma → 0 < Eb sigma → Eb sigma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      P.IsProper → IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ q : Nat,
        (q : Real) ≤ Qb sigma ∧
        ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, lemma6WidthWith m q k (Eb sigma) zeta ≤ (S u).width) ∧
              ∀ u h, h ∈ G → h ∈ H1 → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain B H Y) (phiPrime h) := by
  intro N k m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime
  dsimp only
  intro hH1 hML hselection P Q I hP hproduct hmP
  let theta1 := section16ThetaOne theta gamma k
  let delta := section16Delta theta1
  let D (x : Point N k) := Finset.univ.filter (fun y => (x, y) ∈ section16InducedDomain B H Y)
  by_cases hm : m < 4
  · have hl := lemma6WidthWith_small (q := 0) (k := k) ht ht1 hg hg1 ha.le ha1 hm
    obtain ⟨M, S, hpart, hproper, hwidth, hlin⟩ :=
      section16_local_linearity_singletons P _ hl D phiPrime
    refine ⟨0, by simpa using hQ, Q.carrier, M, S, (fun j => boxInit (S j)),
      (fun j => (S j).axis (Fin.last k)), Finset.Subset.refl _, ?_, hpart, hproper,
      (fun j => boxInit_last_product (S j)), hwidth, ?_⟩
    · have _ : (0 : Real) ≤ Q.carrier.card := Nat.cast_nonneg _
      nlinarith
    · intro j x _ _ _
      simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and] using hlin j x
  · have hm4 : 4 ≤ m := by omega
    have hwidthpos : 0 < P.width := by omega
    have hcanon := hproduct.canonical_factors hwidthpos
    let Q' := boxInit P
    let I' := P.axis (Fin.last k)
    have hQ' : Q'.IsProper := boxInit_isProper P hP
    have hI' : I'.IsProper := hP (Fin.last k)
    have hmQ' : m ≤ Q'.width := hmP.trans (boxInit_width P (by omega))
    have hmI' : m ≤ I'.length := hmP.trans (P.width_le_axis_length (Fin.last k))
    obtain ⟨u, hu⟩ := I'.step_isUnit_of_prime hI' (by omega)
    have hu' : I'.step = (↑u : ZMod N) := hu.symm
    have hstep : I'.step = Q'.commonDiff := P.axis_step (Fin.last k)
    have hfreq (x : Point N k) (hx : x ∈ H1) (r : ZMod N)
        (hr : r ∈ section16LargeSpectrum B x delta) :
        (x, r) ∈ restrictRelation (section16SpectrumRelation B delta) Jbase := by
      have hxJ := (Finset.mem_inter.mp (hH1 ▸ hx)).2
      simpa only [restrictRelation, section16SpectrumRelation, Finset.mem_filter,
        Finset.mem_univ, true_and] using And.intro hr hxJ
    have hlinear (x : Point N k) (hx : x ∈ H1) (v : Nat) (hv : 0 < v)
        (J : ModAP N) (hJ : J.length ≤ v)
        (hdJ : J.step ∈ bohr (section16LargeSpectrum B x delta)
          (section16Zeta theta gamma k / v)) :
        LinearOn (J.carrier ∩ D x) (phiPrime x) := by
      have hxH := (Finset.mem_inter.mp (hH1 ▸ hx)).1
      have h := hselection.2 x hxH v hv J.step hdJ J rfl hJ
      simpa only [D, Finset.inter_filter, Finset.inter_univ] using h
    obtain ⟨q, G, M, S, T, J, hq, hGsub, hGmass, hpart, hSproper, hSproduct, hSlin⟩ :=
      hML.product_linearity_large_m sigma theta gamma hs hs1 ht ht1 hg hg1 hQ ha ha1
        Q' I' u hQ' hI' hstep hu' hk hm4 hmQ' hmI' H1
        (fun x => section16LargeSpectrum B x delta) D phiPrime hfreq hlinear
    refine ⟨q, hq, G, M, S, T, J, ?_, ?_, ?_, (fun j => (hSproper j).1), hSproduct, ?_, ?_⟩
    · simpa only [Q', hcanon.1] using hGsub
    · simpa only [Q', hcanon.1] using hGmass
    · change IsPartition (fun j => (S j).carrier) P.carrier
      simpa only [(boxInit_last_product P).1, lastProductSet, Q', I'] using hpart
    · intro j
      exact (hSproper j).2
    · intro j x hxG hxH hxT
      have h := hSlin j x hxG hxH hxT
      simpa only [D, Finset.inter_filter, Finset.inter_univ] using h

/-- Proper-input version of Lemma 16.6, with proper output boxes. The prime
modulus is the paper's standing convention; positive base dimension is the
range of the Section 16 induction. -/
theorem proper_lemma_16_6 :
  ∀ (N k m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let t := section16T delta theta1 k
    H1 = H ∩ Jbase →
    MultiplyLinear delta t
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      P.IsProper → IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ q : Nat,
        (q : Real) ≤ section16Lemma6QBound sigma delta theta1 k ∧
        ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, section16Lemma6Width m q k sigma delta theta1 zeta ≤
                (S u).width) ∧
              ∀ u h, h ∈ G → h ∈ H1 → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain B H Y) (phiPrime h) := by
  intro N k m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 B phi H Jbase H1 Y phiPrime
  dsimp only
  intro hH1 hML hselection P Q I hP hproduct hmP
  let theta1 := section16ThetaOne theta gamma k
  let delta := section16Delta theta1
  let t := section16T delta theta1 k
  obtain ⟨ha, ha1⟩ := section16_lemma6_exponent_bounds k ht ht1 hg hg1 hs hs1
  have hc : 0 ≤ multipleC (t⁻¹ * sigma) delta k :=
    (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 8) ≠ 0)).pow_nonneg _
  simpa only [section16Lemma6QBound, section16Lemma6Width_eq_sqrt, lemma6WidthWith,
      div_eq_mul_inv, mul_comm] using
    proper_lemma_16_6_with N k m hk theta gamma sigma ht ht1 hg hg1 hs hs1
      (fun x => (multipleQ (t⁻¹ * x) delta k) ^ t)
      (fun x => (multipleC (t⁻¹ * x) delta k) ^ t)
      (Real.rpow_nonneg (inv_nonneg.mpr hc) _) ha ha1 B phi H Jbase H1 Y phiPrime
      hH1 ((multiplyLinear_iff_with delta t _).mp hML) hselection P Q I hP hproduct hmP

/-- Exact companion for the explicitly migrated prime, positive-dimensional,
proper-box catalogue statement. -/
theorem lemma_16_6_holds : lemma_16_6 := proper_lemma_16_6

end LeanProofs.GowersSzemeredi
