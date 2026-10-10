import GowersSzemeredi.Proofs16SinglePieceRemainder
import GowersSzemeredi.Proofs16DenseSelection
import GowersSzemeredi.Proofs16CommonBase
import GowersSzemeredi.Proofs16SpectrumInduction
import GowersSzemeredi.Proofs16GoodDomainTransport
import GowersSzemeredi.Proofs16VertexIdentity
import GowersSzemeredi.Proofs08AffineFrequencyProgression

/-! The single-piece lift, step 5 (Notes L.1): the assembly with Gowers's
own objects.

Take a pair `(B, φ)` with Lemma 16.4's arrangement conditions (ii) and
(iii) and the product property; condition (i), the cover-form
cross-section hypothesis, is not used. `single_piece_lift` produces one
proper `(k+1)`-box `S` and one multilinear `μ` with
`ρ·|S| ≤ |{z ∈ B ∩ S : φ z = μ z}|`, where `ρ` is polynomial in the input
densities whenever the providers are. The chain:
1. Lemma 16.5 without (i) (`section16_dense_induced_selection_of_arrangements`)
   and Lemma 16.7 (`lemma_16_7_holds`) give `H`, `Y`, `φ′`, `x₀`. The good
   domain `B₁` has density `θ₂` in the full box, and
   `φ₁ = (−1)^k φ′ + φ″` on `B₁`.
2. `remainder_piece`: one multilinear `M″` for `φ″` on a
   `C^[2^k−1](θ₂)` fraction of a sub-box.
3. A short-parent cell of that sub-box (`exists_short_parent_dense_cell`).
4. `single_piece_of_spectrum_cover`, with the spectrum relation `Δ`
   (product property by Lemma 14.3, fibres `≤ δ⁻²` by Parseval). The slice
   providers for `φ₁(·, x)` come from translated last-coordinate faces
   (`slice_localPieceFor`).
5. Translate the piece of `φ₁` back to a piece of `φ`.

**Warning.** `single_piece_lift` assumes the box-local inputs
`LocalRelationCoverAt` and `LocalMultilinearPieceAt`, which are false for
growing widths (Notes L.2). It is therefore vacuous as stated. The
provider form `single_piece_lift_core` (`Proofs16SinglePieceGlobal`) is the
usable statement. The helpers here (`lastSliceFace`, `fullSpaceBox`,
`exists_short_parent_dense_cell`, `section16SpectrumRelation_fibre_le`)
remain valid. The inputs of `single_piece_lift`:
* `LocalRelationCoverAt k δ`;
* `LocalMultilinearPieceAt k` for the slices;
* vertex providers `(C, W)`, which `vertex_localPieceFor` supplies from
  lower-dimensional inputs;
* the retiled linearity bound, supplied by
  `exists_polynomial_retiled_linearity_profile`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The face of `(k+1)`-space with free first coordinates and last coordinate `x`. -/
def lastSliceFace {N : Nat} (k : Nat) (x : ZMod N) : CoordinateFace N (k + 1) k where
  free := ⟨Fin.castSucc, Fin.castSucc_injective k⟩
  anchor := appendCoordinate 0 x
  map h := appendCoordinate h x
  map_free := by
    intro h i
    simp [appendCoordinate_eq_snoc]
  map_fixed := by
    intro h j hj
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · exact ((hj i) rfl).elim
    · simp [appendCoordinate_eq_snoc]

/-- **Slice providers.** The translated cross-section `h ↦ φ(x₀ + h, x)`
has a provider from the dimension-`k` input. -/
theorem LocalMultilinearPieceAt.slice_localPieceFor {N k : Nat} [NeZero N] [Fact N.Prime]
    {gamma : Real} {c : Real → Real} {w : Real → Nat → Nat}
    (hprov : LocalMultilinearPieceAt k gamma c w)
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (hB : HasProductProperty B phi gamma) (x0 : Point N k) (x : ZMod N) :
    LocalPieceFor c w (Finset.univ.filter fun h => appendCoordinate (h + x0) x ∈ B)
      (fun h => phi (appendCoordinate (h + x0) x)) := by
  set F := lastSliceFace k x with hFdef
  have h1 : LocalPieceFor c w (F.domain B) (F.pullback phi) :=
    hprov.localPieceFor fun B' hB' => (hB.coordinateFace F).mono hB'
  refine (h1.translate x0).congr ?_ (fun h => rfl)
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, CoordinateFace.mem_domain]
  rfl

/-- The spectrum relation has fibres of size at most `⌊δ⁻²⌋`. -/
theorem section16SpectrumRelation_fibre_le {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) {delta : Real} (hd : 0 < delta) (h : Point N k) :
    ((section16SpectrumRelation B delta).filter fun z => z.1 = h).card ≤
      ⌊delta ^ (-(2 : Int))⌋₊ := by
  have heq : ((section16SpectrumRelation B delta).filter fun z => z.1 = h) =
      (section16LargeSpectrum B h delta).image fun r => (h, r) := by
    ext z
    simp only [section16SpectrumRelation, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨hz, rfl⟩
      exact ⟨z.2, hz, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨hr, rfl⟩
  rw [heq, Finset.card_image_of_injective _ (fun r r' hrr => (Prod.mk.inj hrr).2)]
  exact Nat.le_floor (section16_large_spectrum_card B h hd)

/-- The full box of `(ℤ/N)^d`. -/
def fullSpaceBox (N d : Nat) : Box N d where
  axis := fun _ => modInterval N 0 N
  commonDiff := 1
  axis_step := fun _ => rfl

theorem fullSpaceBox_carrier (N d : Nat) [NeZero N] :
    (fullSpaceBox N d).carrier = Finset.univ := by
  ext x
  simp [fullSpaceBox, Box.carrier, modInterval_zero_modulus_carrier]

theorem fullSpaceBox_isProper (N d : Nat) [NeZero N] : (fullSpaceBox N d).IsProper := by
  intro i
  change (modInterval N 0 N).carrier.card = N
  rw [modInterval_zero_modulus_carrier, Finset.card_univ, ZMod.card]

theorem fullSpaceBox_width (N d : Nat) (hd : 0 < d) : (fullSpaceBox N d).width = N := by
  apply Nat.le_antisymm
  · exact (fullSpaceBox N d).width_le_axis_length ⟨0, hd⟩
  · exact Box.le_width_of_le_axis _ hd (fun _ => le_rfl)

/-- **A short-parent dense cell** of a proper `(k+1)`-box. -/
theorem exists_short_parent_dense_cell {N k : Nat} [NeZero N] [Fact N.Prime] (hk : 0 < k)
    (R : Box N (k + 1)) (hR : R.IsProper) (h4 : 4 ≤ R.width)
    (E : Finset (Point N (k + 1))) (hER : E ⊆ R.carrier) (hEne : E.Nonempty)
    {ρ : Real} (hρ : ρ * R.carrier.card ≤ E.card) :
    ∃ Q : Box N k, Q.IsProper ∧ Q.carrier ⊆ (boxInit R).carrier ∧
      (R.width : Real) / 8 ≤ Q.width ∧
      2 * (Q.axis ⟨0, hk⟩).length ≤ N ∧
      (Q.axis ⟨0, hk⟩).length ≤ (R.axis (Fin.last k)).length ∧
      Q.commonDiff = R.commonDiff ∧ Q.commonDiff ≠ 0 ∧
      ρ * (lastProductSet Q.carrier (R.axis (Fin.last k)).carrier).card ≤
        (E.filter fun z => z ∈ lastProductSet Q.carrier (R.axis (Fin.last k)).carrier).card := by
  set I := R.axis (Fin.last k) with hIdef
  have hI : I.IsProper := hR (Fin.last k)
  have hIlen : R.width ≤ I.length := R.width_le_axis_length (Fin.last k)
  obtain ⟨L, Q, hQpart, hQprop, hQaxes, hQstep⟩ :=
    (boxInit R).short_parent_partition I (boxInit_isProper R hR) hI hk h4
      (boxInit_width R hk) hIlen
  have hRcarrier : R.carrier = lastProductSet (boxInit R).carrier I.carrier :=
    (boxInit_last_product R).1
  obtain ⟨l, hl⟩ := exists_dense_cell (fun l => lastProductSet (Q l).carrier I.carrier)
    _ (lastProductSet_partition _ _ _ hQpart) E id
    (fun z hz => by rw [← hRcarrier]; exact hER hz) hEne (by rw [← hRcarrier]; exact hρ)
  have hu := I.step_isUnit_of_prime hI (by omega)
  refine ⟨Q l, (hQprop l).1, IsPartition.cell_subset hQpart l, (hQprop l).2,
    (hQaxes l _).2.1, (hQaxes l _).2.2, hQstep l, ?_, hl⟩
  rw [hQstep l]
  have hstep : I.step = R.commonDiff := R.axis_step (Fin.last k)
  rw [hstep] at hu
  exact hu.ne_zero

/-- The density after the remainder step. -/
def liftRemainderRho (C : Real → Real) (theta gamma : Real) (k : Nat) : Real :=
  nestC (fun _ => C) (2 ^ k - 1) (section16ThetaTwo (section16ThetaOne theta gamma k))

/-- The width after the remainder step. -/
def liftRemainderWidth (C : Real → Real) (W : Real → Nat → Nat) (theta gamma : Real)
    (k N : Nat) : Nat :=
  nestW (fun _ => C) (fun _ => W) (2 ^ k - 1)
    (section16ThetaTwo (section16ThetaOne theta gamma k)) N


theorem appendCoordinate_add {N k : Nat} (a b : Point N k) (x y : ZMod N) :
    appendCoordinate a x + appendCoordinate b y = appendCoordinate (a + b) (x + y) := by
  funext i
  by_cases hi : i.val < k
  · simp [appendCoordinate, hi]
  · simp [appendCoordinate, hi]

/-- **The single-piece lift.** One proper `(k+1)`-box and one multilinear map
agree with `φ` on a polynomial fraction of `B`, from local inputs only. -/
theorem single_piece_lift {k : Nat} (hk : 1 ≤ k) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qc : Real → Nat → Real} {cR : Real → Real} {wR : Real → Nat → Nat}
    {c : Real → Real} {w : Real → Nat → Nat} {C : Real → Real} {W : Real → Nat → Nat}
    (hcover : LocalRelationCoverAt k (section16Delta (section16ThetaOne theta gamma k)) Qc cR wR)
    (hcR : ∀ t, 0 < t → t ≤ 1 → 0 < cR t ∧ cR t ≤ 1) (hwR : ∀ t, Monotone (wR t))
    (hslprov : LocalMultilinearPieceAt k gamma c w)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hB : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma)
    (hvert : ∀ (x0 : Point N k) (e : Fin k → Bool), e ≠ (fun _ => true) →
      LocalPieceFor C W (vertexDomain B x0 e) (section16TranslatedVertex phi x0 e))
    (hL4 : 4 ≤ liftRemainderWidth C W theta gamma k N)
    (m : Nat) (hm1 : 1 ≤ m)
    (hm : m ≤ wR (liftRemainderRho C theta gamma k / 2)
      ⌈(liftRemainderWidth C W theta gamma k N : Real) / 8⌉₊)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qc (liftRemainderRho C theta gamma k / 2)
        ⌊(section16Delta (section16ThetaOne theta gamma k)) ^ (-(2 : Int))⌋₊ →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
      2 ≤ spectrumPieceRho cR (liftRemainderRho C theta gamma k) ^ 3 *
        spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
      2 ≤ w (c (singlePieceTheta (spectrumPieceRho cR (liftRemainderRho C theta gamma k)) 1))
        (w (singlePieceTheta (spectrumPieceRho cR (liftRemainderRho C theta gamma k)) 1)
          ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊)) :
    ∃ q : Nat, (q : Real) ≤ Qc (liftRemainderRho C theta gamma k / 2)
        ⌊(section16Delta (section16ThetaOne theta gamma k)) ^ (-(2 : Int))⌋₊ ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (w (c (singlePieceTheta (spectrumPieceRho cR (liftRemainderRho C theta gamma k)) 1))
          (w (singlePieceTheta (spectrumPieceRho cR (liftRemainderRho C theta gamma k)) 1)
            ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊) - 1) - 1 ≤
          S.width ∧
        singlePieceDensity c (spectrumPieceRho cR (liftRemainderRho C theta gamma k)) 1 *
            S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card := by
  have hk0 : 0 < k := hk
  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  obtain ⟨hζpos, hζle⟩ := section16Zeta_pos_le_one_div_32 k ht ht1 hg hg1
  -- 1. Lemmas 16.5 (without condition (i)) and 16.7
  obtain ⟨H, Y, phiPrime, hH, hcube, hselected, hselection⟩ :=
    section16_dense_induced_selection_of_arrangements (Fact.out : N.Prime) theta gamma B phi
      ht ht1 hg hg1 hB
  have hmass : section16ThetaOne theta gamma k / 8 * (N : Real) ^ k ≤ H.card := by
    refine le_trans ?_ hH
    have : (0 : Real) ≤ (N : Real) ^ k := by positivity
    nlinarith
  obtain ⟨x0, hgood, hidentity⟩ := lemma_16_7_holds N k theta gamma B phi H Y phiPrime
    hmass hcube hselected hselection
  have hid : Section16PhiOneIdentity (section16GoodDomain B H Y x0) phi x0 phiPrime :=
    section16_phi_one_identity_of_common_base B phi H Y x0 phiPrime hidentity
  set B1 := section16GoodDomain B H Y x0 with hB1def
  set θ₂ := section16ThetaTwo (section16ThetaOne theta gamma k) with hθ₂def
  have hθ₂pos : 0 < θ₂ := by rw [hθ₂def, section16ThetaTwo]; positivity
  have hθ₂le : θ₂ ≤ 1 := by
    rw [hθ₂def, section16ThetaTwo]
    have h8 : section16ThetaOne theta gamma k ^ 8 ≤ 1 := pow_le_one₀ hθ₁pos.le hθ₁le
    have h2 : (2 : Real) ^ (-(32 : Real)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    calc (2 : Real) ^ (-(32 : Real)) * section16ThetaOne theta gamma k ^ 8 ≤ 1 * 1 :=
          mul_le_mul h2 h8 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  -- 2. the remainder piece on the full box
  set P0 := fullSpaceBox N (k + 1) with hP0def
  have hP0 : P0.IsProper := fullSpaceBox_isProper N (k + 1)
  have hP0carrier : P0.carrier = Finset.univ := fullSpaceBox_carrier N (k + 1)
  have hP0width : P0.width = N := fullSpaceBox_width N (k + 1) (Nat.succ_pos k)
  have hP0card : (P0.carrier.card : Real) = (N : Real) ^ (k + 1) := by
    rw [hP0carrier, Finset.card_univ]
    simp [Point, ZMod.card]
  have hB1card : θ₂ * (P0.carrier.card : Real) ≤ B1.card := by
    rw [hP0card, hB1def, section16GoodDomain_card]
    exact hgood
  obtain ⟨R1, Mrem, hR1, -, hR1w, hMrem, hR1c⟩ := remainder_piece (fun e he => hvert x0 e he)
    hC hW hθ₂pos hθ₂le P0 B1 hP0 (by rw [hP0carrier]; exact Finset.subset_univ _)
    (fun e _ z hz => by
      simp only [vertexDomain, Finset.mem_filter, Finset.mem_univ, true_and]
      exact section16GoodDomain_vertex_mem B H Y x0 hz e)
    hB1card
  rw [hP0width] at hR1w
  set ρ1 := liftRemainderRho C theta gamma k with hρ1def
  have hρ1 : 0 < ρ1 ∧ ρ1 ≤ 1 := nestC_pos_le (c := fun _ => C) (fun _ => hC) _ θ₂ hθ₂pos hθ₂le
  set E1 := B1.filter fun x => x ∈ R1.carrier ∧ section16PhiRemainder phi x0 x = Mrem x
    with hE1def
  have hR1w4 : 4 ≤ R1.width := hL4.trans hR1w
  have hR1ne : R1.carrier.Nonempty :=
    R1.carrier_nonempty_of_axis_pos fun z => lt_of_lt_of_le (by omega) (R1.width_le_axis_length z)
  have hR1pos : (0 : Real) < R1.carrier.card := by exact_mod_cast hR1ne.card_pos
  have hE1R1 : E1 ⊆ R1.carrier := fun x hx => (Finset.mem_filter.mp hx).2.1
  have hE1ne : E1.Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.cast_pos.mp (lt_of_lt_of_le (mul_pos hρ1.1 hR1pos) hR1c)
  -- 3. a short-parent dense cell
  obtain ⟨Q, hQ, -, hQw, hshort, hQI, hQstep, hQd, hQc⟩ :=
    exists_short_parent_dense_cell hk0 R1 hR1 hR1w4 E1 hE1R1 hE1ne hR1c
  set I := R1.axis (Fin.last k) with hIdef
  have hI : I.IsProper := hR1 (Fin.last k)
  have hIlen : R1.width ≤ I.length := R1.width_le_axis_length (Fin.last k)
  set E2 := E1.filter fun z => z ∈ lastProductSet Q.carrier I.carrier with hE2def
  set E := E2.image fun z => (section16Init z, section16Last z) with hEdef
  have hEcard : E.card = E2.card := Finset.card_image_of_injective _ initLast_injective
  have hEmem : ∀ p ∈ E, appendCoordinate p.1 p.2 ∈ E2 := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    simpa only [appendCoordinate_init_last] using hz
  have hEB1 : ∀ p ∈ E, appendCoordinate p.1 p.2 ∈ B1 := fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hEmem p hp)).1).1
  have hEsub : E ⊆ Q.carrier ×ˢ I.carrier := by
    intro p hp
    have h := (Finset.mem_filter.mp (hEmem p hp)).2
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
      section16Init_appendCoordinate, section16Last_appendCoordinate] at h
    exact Finset.mem_product.mpr h
  have hEc : ρ1 * Q.carrier.card * I.carrier.card ≤ E.card := by
    rw [hEcard, mul_assoc]
    have h := hQc
    rw [lastProductSet_card] at h
    push_cast at h
    exact h
  -- good pairs
  have hgoodpair : ∀ p ∈ E, Section16GoodInducedPair B H Y x0 (p.1, p.2) := by
    intro p hp
    have h := (Finset.mem_filter.mp (hEB1 p hp)).2
    simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate] using h
  have hvertex : ∀ p ∈ E, appendCoordinate (p.1 + x0) p.2 ∈ B := by
    intro p hp
    have h := section16GoodDomain_vertex_mem B H Y x0 (hEB1 p hp) (fun _ => true)
    simp only [if_true, section16Init_appendCoordinate, section16Last_appendCoordinate] at h
    have heq : (fun i => x0 i + p.1 i) = p.1 + x0 := by
      funext i
      simp [add_comm]
    rw [heq] at h
    exact h
  -- 4. the spectrum step
  set phi1 : Point N k × ZMod N → ZMod N :=
    fun p => section16PhiOne phi x0 (appendCoordinate p.1 p.2) with hphi1def
  have hident : ∀ p ∈ E, phi1 p =
      (-1 : ZMod N) ^ k * phiPrime p.1 p.2 + Mrem (appendCoordinate p.1 p.2) := by
    intro p hp
    have h1 := hid _ (hEB1 p hp)
    have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp (hEmem p hp)).1).2.2
    simp only [section16PhiPrimeLift, section16Init_appendCoordinate,
      section16Last_appendCoordinate] at h1
    rw [hphi1def]
    dsimp only
    rw [h1, h2]
  have hK : ∀ h x, (h, x) ∈ E → ∀ r ∈ section16LargeSpectrum B h
      (section16Delta (section16ThetaOne theta gamma k)),
      (h, r) ∈ section16SpectrumRelation B (section16Delta (section16ThetaOne theta gamma k)) := by
    intro h x _ r hr
    simp only [section16SpectrumRelation, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hr
  have hA : ∀ p ∈ E, p.2 ∈ (Finset.univ.filter fun x =>
      (p.1, x) ∈ section16InducedDomain B H Y) := by
    intro p hp
    obtain ⟨hpH, C0, hC0, -, hC0x⟩ := hgoodpair p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, section16InducedDomain]
    exact ⟨hpH, C0, hC0, hC0x⟩
  have hlinear : ∀ h x, (h, x) ∈ E → ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
        (section16Zeta theta gamma k / v) →
      LinearOn (J.carrier ∩ Finset.univ.filter fun x =>
        (h, x) ∈ section16InducedDomain B H Y) (phiPrime h) := by
    intro h x hx v hv J hJ hd
    have hhH : h ∈ H := (hgoodpair (h, x) hx).1
    have hlin := hselection.2 h hhH v hv J.step hd J rfl hJ
    simpa only [Finset.inter_filter, Finset.inter_univ] using hlin
  have hsl : ∀ x ∈ I.carrier, LocalPieceFor c w
      (Finset.univ.filter fun h => appendCoordinate (h + x0) x ∈ B) (fun h => phi1 (h, x)) := by
    intro x _
    refine (hslprov.slice_localPieceFor hprodB x0 x).congr rfl (fun h => ?_)
    rw [hphi1def]
    simp only [section16PhiOne, section16Init_appendCoordinate, section16Last_appendCoordinate]
    congr 2
    funext i
    simp [add_comm]
  have hDom : ∀ p ∈ E, p.1 ∈ (Finset.univ.filter fun h => appendCoordinate (h + x0) p.2 ∈ B) :=
    fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvertex p hp⟩
  have hQwidth : ⌈(liftRemainderWidth C W theta gamma k N : Real) / 8⌉₊ ≤ Q.width := by
    apply Nat.ceil_le.mpr
    refine le_trans ?_ hQw
    exact div_le_div_of_nonneg_right (by exact_mod_cast hR1w) (by norm_num)
  obtain ⟨q, hq, S, mu, hS, hSsub, hSw, hmu, hcount⟩ :=
    single_piece_of_spectrum_cover hk0 hcover hcR hc hw eps thr hretile hζpos
      (by linarith) Q I hQ hI hQd (by rw [hQstep]; exact R1.axis_step _) hshort hQI
      (by omega) E hEsub hρ1.1 hρ1.2 hEc phi1 phiPrime ((-1 : ZMod N) ^ k) Mrem hMrem hident
      (section16SpectrumRelation B (section16Delta (section16ThetaOne theta gamma k)))
      ⌊(section16Delta (section16ThetaOne theta gamma k)) ^ (-(2 : Int))⌋₊
      (section16_spectrum_relation_product B hδpos) (section16SpectrumRelation_fibre_le B hδpos)
      (fun h => section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
      hK (fun h => Finset.univ.filter fun x => (h, x) ∈ section16InducedDomain B H Y) hA hlinear
      (fun x => Finset.univ.filter fun h => appendCoordinate (h + x0) x ∈ B) hsl hDom
      m hm1 (hm.trans (hwR _ hQwidth)) hpar
  -- 5. translate the piece of `φ₁` back to `φ`
  set t : Point N (k + 1) := appendCoordinate x0 0 with htdef
  refine ⟨q, hq, S.translate t, fun z => mu (z + -t), hS.translate t, hmu.translate (-t), ?_, ?_⟩
  · rw [Box.translate_width]; exact hSw
  · rw [Box.translate_card]
    refine hcount.trans ?_
    have hshift : ∀ p : Point N k × ZMod N,
        appendCoordinate p.1 p.2 + t = appendCoordinate (p.1 + x0) p.2 := by
      intro p
      rw [htdef, appendCoordinate_add, add_zero]
    exact_mod_cast Finset.card_le_card_of_injOn
      (fun p : Point N k × ZMod N => appendCoordinate p.1 p.2 + t)
      (fun p hp => by
        obtain ⟨hpE, hpS, hpmu⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
        · dsimp only; rw [hshift]; exact hvertex p hpE
        · exact (Box.translate_mem_carrier S t _).mpr hpS
        · dsimp only
          rw [add_neg_cancel_right, hshift, ← hpmu, hphi1def]
          simp only [section16PhiOne, section16Init_appendCoordinate,
            section16Last_appendCoordinate]
          congr 2
          funext i
          simp [add_comm])
      (fun p _ p' _ h => appendCoordinate_pair_injective (add_right_cancel h))


/-- **Vertex providers from lower-dimensional inputs.** If the inputs in
dimensions `1, …, k` hold and `(C, W)` lies below every lifted parameter
pair, then every non-top translated vertex has a `(C, W)` provider. -/
theorem vertex_providers_of_low {N k : Nat} [NeZero N] [Fact N.Prime] {gamma : Real}
    {cl : Nat → Real → Real} {wl : Nat → Real → Nat → Nat} {C : Real → Real}
    {W : Real → Nat → Nat}
    (hlow : ∀ l, 1 ≤ l → l ≤ k → LocalMultilinearPieceAt l gamma (cl l) (wl l))
    (hcl : ∀ l t, 0 < t → t ≤ 1 → 0 < cl l t ∧ cl l t ≤ 1) (hwl : ∀ l t, Monotone (wl l t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, C t ≤ (liftLastC^[k + 1 - l] (cl l)) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, W t L ≤ (liftLastW^[k + 1 - l] (wl l)) t L)
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (hB : HasProductProperty B phi gamma) :
    ∀ (x0 : Point N k) (e : Fin k → Bool), e ≠ (fun _ => true) →
      LocalPieceFor C W (vertexDomain B x0 e) (section16TranslatedVertex phi x0 e) := by
  intro x0 e he
  set l := (section16VertexDirections e).card with hldef
  have hl1 : 1 ≤ l := Finset.card_pos.mpr ⟨_, section16VertexDirections_last e⟩
  have hlk : l ≤ k := by
    have := section16VertexDirections_card_lt he
    omega
  exact (LocalMultilinearPieceAt.vertex_localPieceFor e (hlow l hl1 hlk) (hcl l) (hwl l) hB
    x0).mono (hCle l hl1 hlk) (hWle l hl1 hlk)

end LeanProofs.GowersSzemeredi
