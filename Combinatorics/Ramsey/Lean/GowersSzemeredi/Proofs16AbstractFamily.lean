import GowersSzemeredi.Proofs16FamilyPieceCover

/-! The simultaneous union for abstract pieces, in one common frame.

`Proofs16FamilyLemma6` through `Proofs16FamilyPieceCover` state the family
results for Gowers's data `(B, H, Y, φ′, x₀)`. That data lives in the
shifted frame `(h, x) ↦ (x₀ + h, x)`. Pieces with different `x₀` cannot be
translated back to the original frame together.

The proofs never use the frame. They only use, per member `c`:
* a frequency map `K c` with a common covering relation `Γ`;
* Bohr-linearity of `f c x` on `A c x` for `x ∈ H1 c`;
* a domain `D c` and the identity `φ c = (−1)^k f c + rem c` on it;
* a common relation `Γr` containing every remainder graph.

Here they are restated over these abstract members. A piece produced in
its own frame enters in the original frame with every ingredient
translated by `x₀`: `K(· − x₀)`, `A(· − x₀)`, `f(· − x₀)`, `H1 + x₀`. Its
frequencies are then covered by translated multilinear graphs.
* `AbstractFamilyLemma166At`, `abstractFamilyLemma166At_of`
  (`Proofs16FamilyLemma6`).
* `AbstractFamilyLemma169At`, `abstractFamilyLemma169At_of`.
* `abstract_family_piece_large_box_profile`,
  `abstract_family_piece_cover_with`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- **Lemma 16.9 for abstract members.** -/
def AbstractFamilyLemma169At (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (zeta sigma : Real), 0 < zeta → zeta ≤ 1 / 2 → 0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb Qr Er : Real → Real), 0 ≤ Qb (sigma / 2) → 0 < Eb (sigma / 2) →
      Eb (sigma / 2) ≤ 1 → 0 ≤ Er (sigma / 2) →
    ∀ (Gamma : Finset (Point N k × ZMod N)), MultiplyLinearWith Qb Eb Gamma →
    ∀ (Gr : Finset (Point N (k + 1) × ZMod N)), MultiplyLinearWith Qr Er Gr →
    ∀ (ι : Type) (H1 : ι → Finset (Point N k)) (K A : ι → Point N k → Finset (ZMod N))
      (f : ι → Point N k → ZMod N → ZMod N) (D : ι → Finset (Point N (k + 1)))
      (phi rem : ι → Point N (k + 1) → ZMod N),
    (∀ c, ∀ x ∈ H1 c, ∀ r ∈ K c x, (x, r) ∈ Gamma) →
    (∀ c, ∀ x ∈ H1 c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ A c x) (f c x)) →
    (∀ c, ∀ z ∈ D c, section16Init z ∈ H1 c ∧ section16Last z ∈ A c (section16Init z)) →
    (∀ c, ∀ z ∈ D c,
      phi c z = (-1 : ZMod N) ^ k * f c (section16Init z) (section16Last z) + rem c z) →
    (∀ c, ∀ z ∈ D c, (z, rem c z) ∈ Gr) →
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ Qr (sigma / 2) ∧
        Section16LineCoverFamily P D phi sigma
          (W m (Nat.floor (Qb (sigma / 2))) (Er (sigma / 2) * Eb (sigma / 2)) zeta) qGamma

/-- The abstract family Lemma 16.9 from the abstract family Lemma 16.6. -/
theorem abstractFamilyLemma169At_of (k : Nat) {W : Nat → Nat → Real → Real → Real}
    (hW : Section16WidthTransfer W)
    (hlemma6 : AbstractFamilyLemma166At k W) : AbstractFamilyLemma169At k W := by
  unfold AbstractFamilyLemma169At
  intro N m _ _ hk zeta sigma hz hzHalf hs hs1 Qb Eb Qr Er hQ ha ha1 hEr
    Gamma hML Gr hrem ι H1 K A f D phi rem hfreq hlinear hdom hid hGr P hP hmP
  have hsHalf : 0 < sigma / 2 := by positivity
  have hsHalf1 : sigma / 2 ≤ 1 := by linarith
  obtain ⟨M, qGamma, F, R, mu, hFsub, hFmass, hRpart, hRproper, hqGamma,
      hRwidth, hmu, hremCover⟩ := hrem (sigma / 2) hsHalf hsHalf1 P hP
  have hlocal (j : Fin M) := hlemma6 N (R j).width hk zeta (sigma / 2) hz hzHalf
    hsHalf hsHalf1 Qb Eb hQ ha ha1 Gamma hML ι H1 K A f hfreq hlinear
    (R j) (boxInit (R j)) ((R j).axis (Fin.last k)) (hRproper j) (boxInit_last_product (R j)) le_rfl
  choose G L S T J hGsub hGmass hSpart hSproper hSproduct hSwidth hSlin using hlocal
  let qDelta := Nat.floor (Qb (sigma / 2))
  have hwidth (j : Fin M) (a : Fin (L j)) :
      W m qDelta (Er (sigma / 2) * Eb (sigma / 2)) zeta ≤ (S j a).width := by
    have hcell : (m : Real) ^ (Er (sigma / 2)) ≤ (R j).width :=
      (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) hEr).trans (hRwidth j)
    exact (hW m (R j).width qDelta (Eb (sigma / 2)) (Er (sigma / 2)) zeta hz.le ha.le hEr
      hcell).trans (hSwidth j a)
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
          ∀ x ∈ (J j a).carrier ∩ A c h, f c h x = ell x) :=
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
  · intro c a h x hhT hzD hzE hzS
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
    have hdomain := hdom c _ hzD
    simp only [section16Init_appendCoordinate, section16Last_appendCoordinate] at hdomain
    have hxJ : x ∈ (J j b).carrier := by
      have h := ((hSproduct j b).mem_snoc h x).mp (by simpa only [appendCoordinate_eq_snoc] using hzS)
      exact h.2
    have hphi := hellEq c j b h ⟨hhG, hdomain.1, hhT⟩ x (Finset.mem_inter.mpr ⟨hxJ, hdomain.2⟩)
    obtain ⟨i, hi⟩ := hremCover j (appendCoordinate h x) hzR hzF _ (hGr c _ hzD)
    refine ⟨i, ?_⟩
    have hidz := hid c _ hzD
    simp only [section16Init_appendCoordinate, section16Last_appendCoordinate] at hidz
    change _ = lines c j b h i x
    dsimp only [lines]
    rw [hidz, hphi, hi]

/-- **The large-box profile of a family of abstract pieces.** -/
theorem abstract_family_piece_large_box_profile {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {Gamma : Finset (Point N k × ZMod N)} (hML : MultiplyLinearWith Qb Eb Gamma)
    {Gr : Finset (Point N (k + 1) × ZMod N)} (hrem : MultiplyLinearWith Qr Er Gr)
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
    (hslice : ∀ r sample, MultiplyLinearWith (Pb r) (Es r) (Gs r sample))
    (hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ D c →
      (h, phi c (appendCoordinate h (sample c i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, 0 < ε → Antitone (fun r => Es r ε)) :
    ∀ rho : Real, 0 < rho → rho ≤ 1 →
      LargeBoxMultilinearCover
        (Finset.univ.biUnion fun c => partialGraph (D c) (phi c)) rho
        (famPieceGraphBound Qr Pb (Fintype.card ι) rho)
        (pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A Qb zeta rho)
          (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)) := by
  intro rho hrho hrho1 P hP hlarge
  let sigma := rho / 4
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hs1 : sigma ≤ 1 := by dsimp [sigma]; linarith
  have hhalf : sigma / 2 = rho / 8 := by dsimp [sigma]; ring
  have h8 : 0 < rho / 8 := by positivity
  have h81 : rho / 8 ≤ 1 := by linarith
  obtain ⟨hQ, ha, ha1⟩ := hQb (rho / 8) h8 h81
  have hEr8 := hEr (rho / 8) h8 h81
  have hsub := abstractFamilyLemma169At_of k (section16PowerWidth_transfer hA hB) hlemma6
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
  obtain ⟨hPbS, hEsS, _⟩ := hranges S sigma hSpos hs hs1
  have hPbr : Pb r sigma ≤ Pb S sigma := hPb sigma hrS
  have hEsr : Es S sigma ≤ Es r sigma := hEs sigma hs hrS
  have hrpos : 0 < r := by
    rw [hr]
    apply Nat.ceil_pos.mpr
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
theorem abstract_family_piece_cover_with {k : Nat} (hk : 1 ≤ k)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {Qb Eb Qr Er : Real → Real}
    (hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hEr : ∀ s, 0 < s → s ≤ 1 → 0 < Er s)
    {Gamma : Finset (Point N k × ZMod N)} (hML : MultiplyLinearWith Qb Eb Gamma)
    {Gr : Finset (Point N (k + 1) × ZMod N)} (hrem : MultiplyLinearWith Qr Er Gr)
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
    (hslice : ∀ r sample, MultiplyLinearWith (Pb r) (Es r) (Gs r sample))
    (hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ D c →
      (h, phi c (appendCoordinate h (sample c i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Es)
    (hPb : ∀ ε, Monotone (fun r => Pb r ε)) (hEs : ∀ ε, 0 < ε → Antitone (fun r => Es r ε)) :
    MultiplyLinearWith
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
  exact multiplyLinearWith_of_large_box_covers (by omega : 0 < k + 1) (Fintype.card ι)
    (card_biUnion_partialGraph_fiber_le D phi)
    (fun rho => famPieceGraphBound Qr Pb (Fintype.card ι) rho)
    (fun rho => pieceLineExponent Bq Qb Eb Er rho * famPieceSliceExponent Qr Es (Fintype.card ι) rho / 4)
    (fun rho => section16RoundedPowerThreshold
      (pieceWidthScale A Qb zeta rho)
      (pieceLineExponent Bq Qb Eb Er rho) (famPieceSliceExponent Qr Es (Fintype.card ι) rho)) hpos
    (abstract_family_piece_large_box_profile hk hA hB hlemma6 hz hzHalf hQb hEr hML hrem
      hfreq hlinear hdom hid hGr Gs hslice hGs hranges hPb hEs)

end LeanProofs.GowersSzemeredi
