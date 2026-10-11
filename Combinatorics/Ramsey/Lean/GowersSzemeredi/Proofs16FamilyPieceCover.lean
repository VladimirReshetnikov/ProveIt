import GowersSzemeredi.Proofs16FamilyLemma9

/-! **The simultaneous union: one cover for a whole family of pieces.**

Step (B) of Notes L.3, final assembly. A finite family of structured pieces
`(B c, φ c, H c, H1 c, Y c, φ′ c, x₀ c, D c)`, `c : ι`, has common inputs:
* one relation `Γ` covering all large spectra, with controls `(Qb, Eb)`;
* one relation `Γr` containing all remainder graphs, with controls
  `(Qr, Er)`;
* a stacked slice provider `Gs` whose relations contain all members'
  sampled slices, with controls `(Pb, Es)`.

Then the union `⋃_c graph(D c, φ₁ c)` is `MultiplyLinearWith` at every
scale. The width exponent is the single-piece one at the sample bound
`famPieceSamples ≈ 24·Qr(ρ/8)·|ι|/ρ`. The count is
`|ι|·max(Pb, C(S,2)·Pb²)`, or `3^(k+1)·|ι|` on short boxes. Nothing is
refined sequentially, so the exponent is not raised to the power `|ι|`.
That is the difference from `MultiplyLinearWith.union`, which this
replaces for unions of pieces (Part H.2).
* `card_biUnion_partialGraph_fiber_le`.
* `section16_family_piece_large_box_profile`,
  `section16_family_piece_cover_with`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The sample bound for a family of `n` members at loss `ρ`. -/
def famPieceSamples (Qr : Real → Real) (n : Nat) (rho : Real) : Nat :=
  ⌈6 * max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) / (rho / 4)⌉₊

/-- The graph count of the family cover on large boxes. -/
def famPieceGraphBound (Qr : Real → Real) (Pb : Nat → Real → Real) (n : Nat) (rho : Real) :
    Real :=
  (n : Real) * max (Pb (famPieceSamples Qr n rho) (rho / 4))
    (((famPieceSamples Qr n rho).choose 2 : Nat) * Pb (famPieceSamples Qr n rho) (rho / 4) *
      Pb (famPieceSamples Qr n rho) (rho / 4))

/-- The slice exponent at the family sample bound. -/
def famPieceSliceExponent (Qr : Real → Real) (Es : Nat → Real → Real) (n : Nat)
    (rho : Real) : Real :=
  Es (famPieceSamples Qr n rho) (rho / 4)

theorem famPieceSamples_pos {Qr : Real → Real} {n : Nat} {rho : Real} (hrho : 0 < rho) :
    0 < famPieceSamples Qr n rho := by
  unfold famPieceSamples
  apply Nat.ceil_pos.mpr
  have h1 : (0 : Real) < max 1 (Qr (rho / 8)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h2 : (0 : Real) < ((max 1 n : Nat) : Real) := by
    have : 0 < max 1 n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    exact_mod_cast this
  positivity

/-- A union of `|ι|` partial graphs has at most `|ι|` values over each point. -/
theorem card_biUnion_partialGraph_fiber_le {N k : Nat} {ι : Type} [Fintype ι]
    (D : ι → Finset (Point N k)) (f : ι → Point N k → ZMod N) (x : Point N k) :
    ((Finset.univ.biUnion fun c => partialGraph (D c) (f c)).filter
      fun z => z.1 = x).card ≤ Fintype.card ι := by
  classical
  rw [Finset.filter_biUnion]
  calc (Finset.univ.biUnion fun c => (partialGraph (D c) (f c)).filter fun z => z.1 = x).card
      ≤ ∑ c, ((partialGraph (D c) (f c)).filter fun z => z.1 = x).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _c : ι, 1 := Finset.sum_le_sum fun c _ => partialGraph_fiber_card_le_one _ _ x
    _ = Fintype.card ι := by simp

/-- **The large-box profile of a family of pieces.** -/
theorem section16_family_piece_large_box_profile {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AllScaleFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {Gamma : Finset (Point N k × ZMod N)} (hML : MultiplyLinearWith Qb Eb Gamma)
    {Gr : Finset (Point N (k + 1) × ZMod N)} (hrem : MultiplyLinearWith Qr Er Gr)
    {ι : Type} [Fintype ι] {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {H H1 : ι → Finset (Point N k)}
    {Y : (c : ι) → (h : Point N k) → Finset (Section16CubeElement (B c) h)}
    {phiPrime : ι → Point N k → ZMod N → ZMod N} {x0 : ι → Point N k}
    {D : ι → Finset (Point N (k + 1))}
    (hfreq : ∀ c, ∀ x ∈ H1 c, ∀ r ∈ section16LargeSpectrum (B c) x
      (section16Delta (section16ThetaOne theta gamma k)), (x, r) ∈ Gamma)
    (hH1 : ∀ c, H1 c ⊆ H c)
    (hselection : ∀ c, Section16InducedSelection (B c) (phi c) (H c) (Y c)
      (fun h => section16LargeSpectrum (B c) h (section16Delta (section16ThetaOne theta gamma k)))
      (section16Zeta theta gamma k) (phiPrime c))
    (hidentity : ∀ c, Section16PhiOneIdentity (section16GoodDomain (B c) (H1 c) (Y c) (x0 c))
      (phi c) (x0 c) (phiPrime c))
    (hD : ∀ c, D c ⊆ section16GoodDomain (B c) (H1 c) (Y c) (x0 c))
    (hGr : ∀ c, ∀ z ∈ D c, (z, section16PhiRemainder (phi c) (x0 c) z) ∈ Gr)
    {Pb Es : Nat → Real → Real}
    (Gs : (r : Nat) → (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ r sample, MultiplyLinearWith (Pb r) (Es r) (Gs r sample))
    (hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ D c →
      (h, section16PhiOne (phi c) (x0 c) (appendCoordinate h (sample c i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, 0 < ε → Antitone (fun r => Es r ε)) :
    ∀ rho : Real, 0 < rho → rho ≤ 1 →
      LargeBoxMultilinearCover
        (Finset.univ.biUnion fun c => partialGraph (D c) (section16PhiOne (phi c) (x0 c))) rho
        (famPieceGraphBound Qr Pb (Fintype.card ι) rho)
        (pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb (section16Zeta theta gamma k) rho)
          (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)) := by
  classical
  intro rho hrho hrho1 P hP hlarge
  let sigma := rho / 4
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hs1 : sigma ≤ 1 := by dsimp [sigma]; linarith
  have hhalf : sigma / 2 = rho / 8 := by dsimp [sigma]; ring
  have h8 : 0 < rho / 8 := by positivity
  have h81 : rho / 8 ≤ 1 := by linarith
  obtain ⟨hQ, ha, ha1⟩ := hQb (rho / 8) h8 h81
  have hEr8 := hEr (rho / 8) h8 h81
  have hsub := allScaleFamilyLemma169At_of k (section16PowerWidth_transfer hA hB) hlemma6
  obtain ⟨qGamma, hqGamma, hcover⟩ := hsub N P.width hk theta gamma sigma ht ht1 hg hg1 hs hs1
    Qb Eb Qr Er (by rw [hhalf]; exact hQ) (by rw [hhalf]; exact ha) (by rw [hhalf]; exact ha1)
    (by rw [hhalf]; exact hEr8.le) Gamma hML Gr hrem ι B phi H H1 Y phiPrime x0 D
    hfreq hH1 hselection hidentity hD hGr P hP le_rfl
  rw [hhalf] at hcover hqGamma
  let zeta := section16Zeta theta gamma k
  have hz := (section16Zeta_pos_le_half k ht ht1 hg hg1).1
  let l := section16PowerWidth A Bq P.width ⌊Qb (rho / 8)⌋₊ (Er (rho / 8) * Eb (rho / 8)) zeta
  have hl : 0 ≤ l := by
    have := hA ⌊Qb (rho / 8)⌋₊
    dsimp only [l, section16PowerWidth]
    positivity
  obtain ⟨n, Hc, L, Q, mu, hn, hH, hmass, hpart, hproper, hw, hmu, hcov⟩ :=
    hcover.global_affine_lift_rounded_family Gs hslice hGs hranges (by omega) hl
      sigma sigma hs hs1 hs hs1
  set r := ⌈6 * (max 1 qGamma : Real) * ((max 1 (Fintype.card ι) : Nat) : Real) / sigma⌉₊
    with hr
  set S := famPieceSamples Qr (Fintype.card ι) rho with hS
  have hrS : r ≤ S := by
    rw [hr, hS, famPieceSamples]
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hs.le
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le_max le_rfl hqGamma
  have hSpos : 0 < S := famPieceSamples_pos hrho
  obtain ⟨hPbS, hEsS, hEsS1⟩ := hranges S sigma hSpos hs hs1
  have hPbr : Pb r sigma ≤ Pb S sigma := hPb sigma hrS
  have hEsr : Es S sigma ≤ Es r sigma := hEs sigma hs hrS
  have hrpos : 0 < r := by
    rw [hr]
    apply Nat.ceil_pos.mpr
    have h1 : (0 : Real) < max 1 (qGamma : Real) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h2 : (0 : Real) < ((max 1 (Fintype.card ι) : Nat) : Real) := by
      have : 0 < max 1 (Fintype.card ι) := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      exact_mod_cast this
    positivity
  have hPbr1 := (hranges r sigma hrpos hs hs1).1
  have he : 0 < pieceLineExponent Bq Qb Eb Er rho := by
    have := hB ⌊Qb (rho / 8)⌋₊
    unfold pieceLineExponent
    positivity
  have hzA : 0 < pieceWidthScale A Qb zeta rho := by
    have := hA ⌊Qb (rho / 8)⌋₊
    unfold pieceWidthScale
    positivity
  have hlpow : pieceWidthScale A Qb zeta rho * (P.width : Real) ^ pieceLineExponent Bq Qb Eb Er rho
      ≤ l := le_of_eq rfl
  obtain ⟨hbase, hpow⟩ := section16_rounded_power_width hzA he hEsS hlpow hlarge
  refine ⟨L, n, Hc, Q, mu, hH, ?_, hpart, hproper, ?_, ?_, hmu, ?_⟩
  · have hm : 1 - sigma - 2 * sigma - sigma = 1 - rho := by dsimp [sigma]; ring
    simpa only [hm] using hmass
  · refine hn.trans ?_
    unfold famPieceGraphBound
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    refine max_le_max hPbr ?_
    have hch : ((r.choose 2 : Nat) : Real) ≤ ((S.choose 2 : Nat) : Real) := by
      exact_mod_cast Nat.choose_le_choose 2 hrS
    have h0 : (0 : Real) ≤ Pb r sigma := zero_le_one.trans hPbr1
    calc ((r.choose 2 : Nat) : Real) * Pb r sigma * Pb r sigma
        ≤ ((S.choose 2 : Nat) : Real) * Pb S sigma * Pb S sigma := by
          apply mul_le_mul (mul_le_mul hch hPbr h0 (Nat.cast_nonneg _)) hPbr h0
          exact mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hPbS)
      _ = _ := rfl
  · intro j
    refine hpow.trans (le_trans ?_ (hw j))
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Real.sqrt_le_sqrt
    exact Real.rpow_le_rpow_of_exponent_le hbase hEsr
  · intro j x hx hh y hxy
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hxy
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact hcov c j z hx hz hh

/-- **The simultaneous union of a family of pieces, at every scale.** -/
theorem section16_family_piece_cover_with {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AllScaleFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {Gamma : Finset (Point N k × ZMod N)} (hML : MultiplyLinearWith Qb Eb Gamma)
    {Gr : Finset (Point N (k + 1) × ZMod N)} (hrem : MultiplyLinearWith Qr Er Gr)
    {ι : Type} [Fintype ι] {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {H H1 : ι → Finset (Point N k)}
    {Y : (c : ι) → (h : Point N k) → Finset (Section16CubeElement (B c) h)}
    {phiPrime : ι → Point N k → ZMod N → ZMod N} {x0 : ι → Point N k}
    {D : ι → Finset (Point N (k + 1))}
    (hfreq : ∀ c, ∀ x ∈ H1 c, ∀ r ∈ section16LargeSpectrum (B c) x
      (section16Delta (section16ThetaOne theta gamma k)), (x, r) ∈ Gamma)
    (hH1 : ∀ c, H1 c ⊆ H c)
    (hselection : ∀ c, Section16InducedSelection (B c) (phi c) (H c) (Y c)
      (fun h => section16LargeSpectrum (B c) h (section16Delta (section16ThetaOne theta gamma k)))
      (section16Zeta theta gamma k) (phiPrime c))
    (hidentity : ∀ c, Section16PhiOneIdentity (section16GoodDomain (B c) (H1 c) (Y c) (x0 c))
      (phi c) (x0 c) (phiPrime c))
    (hD : ∀ c, D c ⊆ section16GoodDomain (B c) (H1 c) (Y c) (x0 c))
    (hGr : ∀ c, ∀ z ∈ D c, (z, section16PhiRemainder (phi c) (x0 c) z) ∈ Gr)
    {Pb Es : Nat → Real → Real}
    (Gs : (r : Nat) → (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ r sample, MultiplyLinearWith (Pb r) (Es r) (Gs r sample))
    (hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ D c →
      (h, section16PhiOne (phi c) (x0 c) (appendCoordinate h (sample c i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, 0 < ε → Antitone (fun r => Es r ε)) :
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound Qr Pb (Fintype.card ι) rho)
        ((3 ^ (k + 1) * Fintype.card ι : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb (section16Zeta theta gamma k) rho)
          (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)))
      (Finset.univ.biUnion fun c => partialGraph (D c) (section16PhiOne (phi c) (x0 c))) := by
  have hpos (rho : Real) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
      0 < pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4 := by
    have h8 : 0 < rho / 8 := by positivity
    have h81 : rho / 8 ≤ 1 := by linarith
    have hEb := (hQb (rho / 8) h8 h81).2.1
    have hEr8 := hEr (rho / 8) h8 h81
    have hBq := hB ⌊Qb (rho / 8)⌋₊
    have hEs' := (hranges (famPieceSamples Qr (Fintype.card ι) rho) (rho / 4)
      (famPieceSamples_pos hrho) (by positivity) (by linarith)).2.1
    unfold pieceLineExponent famPieceSliceExponent
    positivity
  exact multiplyLinearWith_of_large_box_covers (by omega : 0 < k + 1) (Fintype.card ι)
    (card_biUnion_partialGraph_fiber_le D (fun c => section16PhiOne (phi c) (x0 c)))
    (fun rho => famPieceGraphBound Qr Pb (Fintype.card ι) rho)
    (fun rho => pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
    (fun rho => section16RoundedPowerThreshold
      (pieceWidthScale A Qb (section16Zeta theta gamma k) rho)
      (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)) hpos
    (section16_family_piece_large_box_profile hk hA hB hlemma6 ht ht1 hg hg1 hQb hEr hML hrem
      hfreq hH1 hselection hidentity hD hGr Gs hslice hGs hranges hPb hEs)

end LeanProofs.GowersSzemeredi
