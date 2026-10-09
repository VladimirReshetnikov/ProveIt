import GowersSzemeredi.Proofs16PolynomialUniformWidth

/-! The improved recurrence in the induced-function setting of Lemma 16.6.

Above the localized recurrence threshold, the spectrum cover gives proper
product cells on which the selected induced function is linear. The width
uses the reciprocal-polynomial phase-count exponent evaluated at the known
spectrum-count bound. The spectrum structure and induced-selection inputs
remain explicit hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The statement of `exists_polynomial_lemma_16_6` at fixed constants. -/
def PolynomialLemma166At (k : Nat) (C p : Nat) : Prop :=
  ∀ (N m n : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb sigma → 0 ≤ Eb sigma →
    4 ≤ m → 0 < n → (n : Real) ≤ ((m : Real) / 8) ^ (Eb sigma) →
    section16SimultaneousThreshold k C p (Nat.floor (Qb sigma)) ≤ n →
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
      ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, (zeta / 2) * Real.sqrt
                ((n : Real) ^ section16SimultaneousExponent k p (Nat.floor (Qb sigma))) ≤ (S u).width) ∧
              ∀ u h, h ∈ G → h ∈ H1 → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain B H Y) (phiPrime h)

/-- `exists_polynomial_lemma_16_6` at the constants of its input. -/
theorem polynomialLemma166At_of (k : Nat) {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hassembly : UniformPolynomialSpectrumProductLinearityAt k C p) : PolynomialLemma166At k C p := by
  unfold PolynomialLemma166At
  intro N m n _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha
    hm4 hn hnscale hnthreshold B phi H Jbase H1 Y phiPrime
  dsimp only
  intro hH1 hML hselection P Q I hP hproduct hmP
  classical
  let theta1 := section16ThetaOne theta gamma k
  let delta := section16Delta theta1
  let D (x : Point N k) := Finset.univ.filter (fun y => (x, y) ∈ section16InducedDomain B H Y)
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
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  obtain ⟨G, M, S, T, J, hGsub, hGmass, hpart, hSproper, hSproduct, hSlin⟩ :=
    hassembly N m n Qb Eb _ hML sigma (section16Zeta theta gamma k) hs hs1 hz hzHalf hQ ha
      Q' I' u hQ' hI' hstep hu' hk hm4 hmQ' hmI' hn hnscale hnthreshold H1
      (fun x => section16LargeSpectrum B x delta) D phiPrime hfreq hlinear
  refine ⟨G, M, S, T, J, ?_, ?_, ?_, (fun j => (hSproper j).1), hSproduct, ?_, ?_⟩
  · simpa only [Q', hcanon.1] using hGsub
  · simpa only [Q', hcanon.1] using hGmass
  · change IsPartition (fun j => (S j).carrier) P.carrier
    simpa only [(boxInit_last_product P).1, lastProductSet, Q', I'] using hpart
  · intro j
    exact (hSproper j).2
  · intro j x hxG hxH hxT
    have h := hSlin j x hxG hxH hxT
    simpa only [D, Finset.inter_filter, Finset.inter_univ] using h

/-- Lemma 16.6 with the polynomial recurrence, above the explicit localized
input threshold. The graph-count bound controls one common width. -/
theorem exists_polynomial_lemma_16_6 (k : Nat) :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N m n : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb sigma → 0 ≤ Eb sigma →
    4 ≤ m → 0 < n → (n : Real) ≤ ((m : Real) / 8) ^ (Eb sigma) →
    section16SimultaneousThreshold k C p (Nat.floor (Qb sigma)) ≤ n →
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
      ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, (zeta / 2) * Real.sqrt
                ((n : Real) ^ section16SimultaneousExponent k p (Nat.floor (Qb sigma))) ≤ (S u).width) ∧
              ∀ u h, h ∈ G → h ∈ H1 → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain B H Y) (phiPrime h) := by
  obtain ⟨C, p, hC, hp, hassembly⟩ := exists_uniform_polynomial_spectrum_product_linearity k
  exact ⟨C, p, hC, hp, polynomialLemma166At_of k hC hp hassembly⟩

end LeanProofs.GowersSzemeredi
