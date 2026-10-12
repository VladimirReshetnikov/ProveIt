import GowersSzemeredi.Proofs16IntegerFamilyAffineLift
import GowersSzemeredi.Proofs16IntegerAllScaleCover

/-! Simultaneous multilinear covers of genuine abstract piece families.
The explicit rounded thresholds, graph counts and positive width controls
are identical to the existing family construction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem integer_abstract_family_piece_large_box_profile {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : IntegerAbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {Gamma : Finset (Point N k × ZMod N)} (hML : IntegerMultiplyLinearWith Qb Eb Gamma)
    {Gr : Finset (Point N (k + 1) × ZMod N)} (hrem : IntegerMultiplyLinearWith Qr Er Gr)
    {ι : Type} [Fintype ι] {H1 : ι → Finset (Point N k)} {K Adom : ι → Point N k → Finset (ZMod N)}
    {f : ι → Point N k → ZMod N → ZMod N} {D : ι → Finset (Point N (k + 1))}
    {phi rem : ι → Point N (k + 1) → ZMod N}
    (hfreq : ∀ c, ∀ x ∈ H1 c, ∀ r ∈ K c x, (x, r) ∈ Gamma)
    (hlinear : ∀ c, ∀ x ∈ H1 c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ Adom c x) (f c x))
    (hdom : ∀ c, ∀ z ∈ D c, section16Init z ∈ H1 c ∧ section16Last z ∈ Adom c (section16Init z))
    (hid : ∀ c, ∀ z ∈ D c,
      phi c z = (-1 : ZMod N) ^ k * f c (section16Init z) (section16Last z) + rem c z)
    (hGr : ∀ c, ∀ z ∈ D c, (z, rem c z) ∈ Gr)
    {Pb Es : Nat → Real → Real}
    (Gs : (r : Nat) → (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ r sample, IntegerMultiplyLinearWith (Pb r) (Es r) (Gs r sample))
    (hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ D c →
      (h, phi c (appendCoordinate h (sample c i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, 0 < ε → Antitone (fun r => Es r ε)) :
    ∀ rho : Real, 0 < rho → rho ≤ 1 →
      IntegerLargeBoxMultilinearCover
        (Finset.univ.biUnion fun c => partialGraph (D c) (phi c)) rho
        (famPieceGraphBound Qr Pb (Fintype.card ι) rho)
        (pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb zeta rho)
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
  have hsub := integerAbstractFamilyLemma169At_of k (section16PowerWidth_transfer hA hB) hlemma6
  obtain ⟨qGamma, hqGamma, hcover⟩ := hsub N P.width hk zeta sigma hz hzHalf hs hs1
    Qb Eb Qr Er (by rw [hhalf]; exact hQ) (by rw [hhalf]; exact ha) (by rw [hhalf]; exact ha1)
    (by rw [hhalf]; exact hEr8.le) Gamma hML Gr hrem ι H1 K Adom f D phi rem
    hfreq hlinear hdom hid hGr P hP le_rfl
  rw [hhalf] at hcover hqGamma
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

/-- **The simultaneous union of a family of abstract pieces, at every scale.** -/
theorem integer_abstract_family_piece_cover_with {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : IntegerAbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {Gamma : Finset (Point N k × ZMod N)} (hML : IntegerMultiplyLinearWith Qb Eb Gamma)
    {Gr : Finset (Point N (k + 1) × ZMod N)} (hrem : IntegerMultiplyLinearWith Qr Er Gr)
    {ι : Type} [Fintype ι] {H1 : ι → Finset (Point N k)} {K Adom : ι → Point N k → Finset (ZMod N)}
    {f : ι → Point N k → ZMod N → ZMod N} {D : ι → Finset (Point N (k + 1))}
    {phi rem : ι → Point N (k + 1) → ZMod N}
    (hfreq : ∀ c, ∀ x ∈ H1 c, ∀ r ∈ K c x, (x, r) ∈ Gamma)
    (hlinear : ∀ c, ∀ x ∈ H1 c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ Adom c x) (f c x))
    (hdom : ∀ c, ∀ z ∈ D c, section16Init z ∈ H1 c ∧ section16Last z ∈ Adom c (section16Init z))
    (hid : ∀ c, ∀ z ∈ D c,
      phi c z = (-1 : ZMod N) ^ k * f c (section16Init z) (section16Last z) + rem c z)
    (hGr : ∀ c, ∀ z ∈ D c, (z, rem c z) ∈ Gr)
    {Pb Es : Nat → Real → Real}
    (Gs : (r : Nat) → (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ r sample, IntegerMultiplyLinearWith (Pb r) (Es r) (Gs r sample))
    (hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ D c →
      (h, phi c (appendCoordinate h (sample c i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, 0 < ε → Antitone (fun r => Es r ε)) :
    IntegerMultiplyLinearWith
      (fun rho => max (famPieceGraphBound Qr Pb (Fintype.card ι) rho)
        ((3 ^ (k + 1) * Fintype.card ι : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb zeta rho)
          (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)))
      (Finset.univ.biUnion fun c => partialGraph (D c) (phi c)) := by
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
  exact integerMultiplyLinearWith_of_large_box_covers (by omega : 0 < k + 1) (Fintype.card ι)
    (card_biUnion_partialGraph_fiber_le D phi)
    (fun rho => famPieceGraphBound Qr Pb (Fintype.card ι) rho)
    (fun rho => pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
    (fun rho => section16RoundedPowerThreshold
      (pieceWidthScale A Qb zeta rho)
      (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)) hpos
    (integer_abstract_family_piece_large_box_profile hk hA hB hlemma6 hz hzHalf hQb hEr hML hrem
      hfreq hlinear hdom hid hGr Gs hslice hGs hranges hPb hEs)

end LeanProofs.GowersSzemeredi
