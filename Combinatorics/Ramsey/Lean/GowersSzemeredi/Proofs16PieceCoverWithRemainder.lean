import GowersSzemeredi.Proofs16Lemma9WithRemainder
import GowersSzemeredi.Proofs16CubicCapBound

/-! The cover of one structured piece with every control explicit.

The existing piece covers (`AllScalePolynomialMultilinearCoverAt`,
`Section16AllBoxLineCoversWith.cubic_multiplyLinearWith`) take the
cross-section remainder with Gowers's printed `(γ, R)` controls. Here the
remainder has arbitrary controls `(Qr, Er)` on a sub-domain `D ⊆ B₁`. The
spectrum has controls `(Qb, Eb)`, and the slices have a provider `(Pb, Es)`.
The result is a `MultiplyLinearWith` cover of `φ₁` on `D` at every scale:
* the graph count is `pieceGraphBound`, polynomial in `Pb` at the sample
  bound `pieceSamples ≈ 24·Qr(ρ/8)/ρ`;
* the width exponent is the capped `e·a/4` of the line exponent
  `e = Er·Eb / B(⌊Qb⌋)` and the slice exponent `a = Es`. By
  `piece_cover_exponent_lower` it is at least `e·a/(16 + 4 log(16/z))`,
  where `z = ζ/A(⌊Qb⌋)`.

So the piece cover is polynomial whenever the inputs are. Lemma 16.6
enters through `AllScaleLemma166WidthAt` at the power width
`section16PowerWidth A B`. The polynomial width
`section16PolynomialLinearityWidth` is this form, with `A`, `B` polynomial
in the spectrum count. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A power-shaped linearity width `ζ/A(q) · m^(a/B(q))`. -/
def section16PowerWidth (A Bq : Nat → Real) (m q : Nat) (a zeta : Real) : Real :=
  zeta / A q * (m : Real) ^ (a / Bq q)

theorem section16PowerWidth_transfer {A Bq : Nat → Real}
    (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q) : Section16WidthTransfer (section16PowerWidth A Bq) := by
  intro m n q a c zeta hz ha _ hcell
  unfold section16PowerWidth
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hz (hA q).le)
  rw [mul_div_assoc, Real.rpow_mul (Nat.cast_nonneg m)]
  exact Real.rpow_le_rpow (by positivity) hcell (div_nonneg ha (hB q).le)

/-- The bound on the number of sampled slices at loss `ρ`. -/
def pieceSamples (Qr : Real → Real) (rho : Real) : Nat :=
  ⌈6 * max 1 (Qr (rho / 8)) / (rho / 4)⌉₊

/-- The graph count of the piece cover at loss `ρ`. -/
def pieceGraphBound (Qr : Real → Real) (Pb : Nat → Real → Real) (rho : Real) : Real :=
  max (Pb (pieceSamples Qr rho) (rho / 4))
    (((pieceSamples Qr rho).choose 2 : Nat) * Pb (pieceSamples Qr rho) (rho / 4) *
      Pb (pieceSamples Qr rho) (rho / 4))

/-- The line exponent: the remainder and spectrum exponents through the power width. -/
def pieceLineExponent (Bq : Nat → Real) (Qb Eb Er : Real → Real) (rho : Real) : Real :=
  Er (rho / 8) * Eb (rho / 8) / Bq ⌊Qb (rho / 8)⌋₊

/-- The slice exponent at the sample bound. -/
def pieceSliceExponent (Qr : Real → Real) (Es : Nat → Real → Real) (rho : Real) : Real :=
  Es (pieceSamples Qr rho) (rho / 4)

/-- The prefactor of the power width at loss `ρ`. -/
def pieceWidthScale (A : Nat → Real) (Qb : Real → Real) (zeta rho : Real) : Real :=
  zeta / A ⌊Qb (rho / 8)⌋₊

theorem pieceSamples_pos {Qr : Real → Real} {rho : Real} (hrho : 0 < rho) :
    0 < pieceSamples Qr rho := by
  unfold pieceSamples
  apply Nat.ceil_pos.mpr
  have h1 : (0 : Real) < max 1 (Qr (rho / 8)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

/-- **The large-box profile of one piece.** -/
theorem section16_piece_large_box_profile {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AllScaleLemma166WidthAt k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {H Jbase H1 : Finset (Point N k)}
    {Y : (h : Point N k) → Finset (Section16CubeElement B h)}
    {phiPrime : Point N k → ZMod N → ZMod N} {x0 : Point N k}
    (hH1 : H1 = H ∩ Jbase)
    (hML : MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B
        (section16Delta (section16ThetaOne theta gamma k))) Jbase))
    (hselection : Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
      (section16Zeta theta gamma k) phiPrime)
    (hidentity : Section16PhiOneIdentity (section16GoodDomain B H1 Y x0) phi x0 phiPrime)
    {D : Finset (Point N (k + 1))} (hD : D ⊆ section16GoodDomain B H1 Y x0)
    (hrem : MultiplyLinearWith Qr Er (partialGraph D (section16PhiRemainder phi x0)))
    {Pb Es : Nat → Real → Real}
    (hslice : Section16SliceProvider D (section16PhiOne phi x0) Pb Es)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, Antitone (fun r => Es r ε)) :
    ∀ rho : Real, 0 < rho → rho ≤ 1 →
      LargeBoxMultilinearCover (partialGraph D (section16PhiOne phi x0)) rho
        (pieceGraphBound Qr Pb rho)
        (pieceLineExponent Bq Qb Eb Er rho * pieceSliceExponent Qr Es rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb (section16Zeta theta gamma k) rho)
          (pieceLineExponent Bq Qb Eb Er rho) (pieceSliceExponent Qr Es rho)) := by
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
  have hsub := allScaleLemma169SubdomainAt_of k (section16PowerWidth_transfer hA hB) hlemma6
  obtain ⟨qGamma, hqGamma, hcover⟩ := hsub N P.width hk theta gamma sigma ht ht1 hg hg1 hs hs1
    Qb Eb Qr Er (by rw [hhalf]; exact hQ) (by rw [hhalf]; exact ha) (by rw [hhalf]; exact ha1)
    (by rw [hhalf]; exact hEr8.le) B phi H Jbase H1 Y phiPrime x0
    hH1 hML hselection hidentity D hD hrem P hP le_rfl
  rw [hhalf] at hcover hqGamma
  let zeta := section16Zeta theta gamma k
  have hz := (section16Zeta_pos_le_half k ht ht1 hg hg1).1
  let l := section16PowerWidth A Bq P.width ⌊Qb (rho / 8)⌋₊ (Er (rho / 8) * Eb (rho / 8)) zeta
  have hl : 0 ≤ l := by
    have := hA ⌊Qb (rho / 8)⌋₊
    dsimp only [l, section16PowerWidth]
    positivity
  obtain ⟨n, Hc, L, Q, mu, hn, hH, hmass, hpart, hproper, hw, hmu, hcov⟩ :=
    hcover.global_affine_lift_rounded_with hslice hranges (by omega) hl sigma sigma hs hs1 hs hs1
  set r := ⌈6 * (max 1 qGamma : Real) / sigma⌉₊ with hr
  set S := pieceSamples Qr rho with hS
  have hrS : r ≤ S := by
    rw [hr, hS, pieceSamples]
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hs.le
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le_max le_rfl hqGamma
  have hSpos : 0 < S := pieceSamples_pos hrho
  obtain ⟨hPbS, hEsS, hEsS1⟩ := hranges S sigma hSpos hs hs1
  have hPbr : Pb r sigma ≤ Pb S sigma := hPb sigma hrS
  have hEsr : Es S sigma ≤ Es r sigma := hEs sigma hrS
  have hrpos : 0 < r := by
    rw [hr]
    apply Nat.ceil_pos.mpr
    have h1 : (0 : Real) < max 1 (qGamma : Real) := lt_of_lt_of_le one_pos (le_max_left _ _)
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
  · refine hn.trans (max_le_max hPbr ?_)
    have hch : ((r.choose 2 : Nat) : Real) ≤ ((S.choose 2 : Nat) : Real) := by
      exact_mod_cast Nat.choose_le_choose 2 hrS
    have h0 : (0 : Real) ≤ Pb r sigma := zero_le_one.trans hPbr1
    have hc0 : (0 : Real) ≤ ((r.choose 2 : Nat) : Real) := Nat.cast_nonneg _
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
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact hcov j z hx hz hh

/-- **The cover of one piece, at every scale.** -/
theorem section16_piece_cover_with {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AllScaleLemma166WidthAt k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {H Jbase H1 : Finset (Point N k)}
    {Y : (h : Point N k) → Finset (Section16CubeElement B h)}
    {phiPrime : Point N k → ZMod N → ZMod N} {x0 : Point N k}
    (hH1 : H1 = H ∩ Jbase)
    (hML : MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B
        (section16Delta (section16ThetaOne theta gamma k))) Jbase))
    (hselection : Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
      (section16Zeta theta gamma k) phiPrime)
    (hidentity : Section16PhiOneIdentity (section16GoodDomain B H1 Y x0) phi x0 phiPrime)
    {D : Finset (Point N (k + 1))} (hD : D ⊆ section16GoodDomain B H1 Y x0)
    (hrem : MultiplyLinearWith Qr Er (partialGraph D (section16PhiRemainder phi x0)))
    {Pb Es : Nat → Real → Real}
    (hslice : Section16SliceProvider D (section16PhiOne phi x0) Pb Es)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, Antitone (fun r => Es r ε)) :
    MultiplyLinearWith
      (fun rho => max (pieceGraphBound Qr Pb rho) ((3 ^ (k + 1) : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq Qb Eb Er rho * pieceSliceExponent Qr Es rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb (section16Zeta theta gamma k) rho)
          (pieceLineExponent Bq Qb Eb Er rho) (pieceSliceExponent Qr Es rho)))
      (partialGraph D (section16PhiOne phi x0)) := by
  have hpos (rho : Real) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
      0 < pieceLineExponent Bq Qb Eb Er rho * pieceSliceExponent Qr Es rho / 4 := by
    have h8 : 0 < rho / 8 := by positivity
    have h81 : rho / 8 ≤ 1 := by linarith
    have hEb := (hQb (rho / 8) h8 h81).2.1
    have hEr8 := hEr (rho / 8) h8 h81
    have hBq := hB ⌊Qb (rho / 8)⌋₊
    have hEs := (hranges (pieceSamples Qr rho) (rho / 4) (pieceSamples_pos hrho)
      (by positivity) (by linarith)).2.1
    unfold pieceLineExponent pieceSliceExponent
    positivity
  simpa only [Nat.mul_one] using
    multiplyLinearWith_of_large_box_covers (by omega : 0 < k + 1) 1
      (partialGraph_fiber_card_le_one D (section16PhiOne phi x0))
      (fun rho => pieceGraphBound Qr Pb rho)
      (fun rho => pieceLineExponent Bq Qb Eb Er rho * pieceSliceExponent Qr Es rho / 4)
      (fun rho => section16RoundedPowerThreshold
        (pieceWidthScale A Qb (section16Zeta theta gamma k) rho)
        (pieceLineExponent Bq Qb Eb Er rho) (pieceSliceExponent Qr Es rho)) hpos
      (section16_piece_large_box_profile hk hA hB hlemma6 ht ht1 hg hg1 hQb hEr hH1 hML
        hselection hidentity hD hrem hslice hranges hPb hEs)

/-- The capped exponent of the piece cover keeps a constant multiple of the
product of the line and slice exponents. -/
theorem piece_cover_exponent_lower {A Bq : Nat → Real} {Qb Eb Qr Er : Real → Real}
    {Es : Nat → Real → Real} {zeta rho : Real}
    (hz : 0 < pieceWidthScale A Qb zeta rho) (hz1 : pieceWidthScale A Qb zeta rho ≤ 1)
    (he : 0 < pieceLineExponent Bq Qb Eb Er rho) (he1 : pieceLineExponent Bq Qb Eb Er rho ≤ 1)
    (ha : 0 < pieceSliceExponent Qr Es rho) (ha1 : pieceSliceExponent Qr Es rho ≤ 1) :
    pieceLineExponent Bq Qb Eb Er rho * pieceSliceExponent Qr Es rho /
        (16 + 4 * Real.log (16 / pieceWidthScale A Qb zeta rho)) ≤
      section16CappedWidthExponent
        (pieceLineExponent Bq Qb Eb Er rho * pieceSliceExponent Qr Es rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb zeta rho)
          (pieceLineExponent Bq Qb Eb Er rho) (pieceSliceExponent Qr Es rho)) :=
  section16_cubic_capped_exponent_lower hz hz1 he he1 ha ha1

end LeanProofs.GowersSzemeredi
