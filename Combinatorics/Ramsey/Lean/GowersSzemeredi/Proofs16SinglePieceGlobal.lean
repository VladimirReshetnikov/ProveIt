import GowersSzemeredi.Proofs16GlobalCoverProviders
import GowersSzemeredi.Proofs16SinglePieceLift

/-! The single-piece lift on good domains (Notes L.1 correction, L.2).

`single_piece_lift_core` is the lift with every input a *provider on an
explicit domain*:
* translated cube vertices on domains `DomV e`;
* the spectrum relation on `DomG`;
* the translated last-coordinate slices on `DomS x`.

It works on any dense part `B₁′` of Gowers's good domain `B₁` that lies inside
all of these domains. The providers are exactly what global-to-local covers
give on their good sets (`MultiplyLinearWith.localPieceFor`,
`MultiplyLinearWith.localRelationCoverFor`). Unlike the refuted box-local
inputs, they are satisfiable. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **The single-piece lift from providers on good domains.** -/
theorem single_piece_lift_core {k : Nat} (hk : 1 ≤ k) {delta zeta : Real}
    (hz : 0 < zeta) (hz2 : zeta ≤ 1 / 2)
    {Qc : Real → Real} {cR : Real → Real} {wR : Real → Nat → Nat}
    {c : Real → Real} {w : Real → Nat → Nat} {C : Real → Real} {W : Real → Nat → Nat}
    (hcR : ∀ t, 0 < t → t ≤ 1 → 0 < cR t ∧ cR t ≤ 1) (hwR : ∀ t, Monotone (wR t))
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k)
    (hselection : Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime)
    (hid : Section16PhiOneIdentity (section16GoodDomain B H Y x0) phi x0 phiPrime)
    (B1 : Finset (Point N (k + 1))) (hB1 : B1 ⊆ section16GoodDomain B H Y x0)
    {theta2 : Real} (hθ₂pos : 0 < theta2) (hθ₂le : theta2 ≤ 1)
    (hB1card : theta2 * (N : Real) ^ (k + 1) ≤ B1.card)
    (DomV : (Fin k → Bool) → Finset (Point N (k + 1)))
    (hvert : ∀ e : Fin k → Bool, e ≠ (fun _ => true) →
      LocalPieceFor C W (DomV e) (section16TranslatedVertex phi x0 e))
    (hB1V : ∀ e : Fin k → Bool, e ≠ (fun _ => true) → B1 ⊆ DomV e)
    (DomG : Finset (Point N k))
    (hcovG : LocalRelationCoverFor cR Qc wR DomG (section16SpectrumRelation B delta))
    (hB1G : ∀ z ∈ B1, section16Init z ∈ DomG)
    (DomS : ZMod N → Finset (Point N k))
    (hsl : ∀ x, LocalPieceFor c w (DomS x) (fun h => phi (appendCoordinate (h + x0) x)))
    (hB1S : ∀ z ∈ B1, section16Init z ∈ DomS (section16Last z))
    (hL4 : 4 ≤ nestW (fun _ => C) (fun _ => W) (2 ^ k - 1) theta2 N)
    (m : Nat) (hm1 : 1 ≤ m)
    (hm : m ≤ wR (nestC (fun _ => C) (2 ^ k - 1) theta2 / 2)
      ⌈(nestW (fun _ => C) (fun _ => W) (2 ^ k - 1) theta2 N : Real) / 8⌉₊)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qc (nestC (fun _ => C) (2 ^ k - 1) theta2 / 2) →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth zeta m (eps q) ∧
      2 ≤ spectrumPieceRho cR (nestC (fun _ => C) (2 ^ k - 1) theta2) ^ 3 *
        spectrumCellWidth zeta m (eps q) ∧
      2 ≤ w (c (singlePieceTheta (spectrumPieceRho cR (nestC (fun _ => C) (2 ^ k - 1) theta2)) 1))
        (w (singlePieceTheta (spectrumPieceRho cR (nestC (fun _ => C) (2 ^ k - 1) theta2)) 1)
          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊)) :
    ∃ q : Nat, (q : Real) ≤ Qc (nestC (fun _ => C) (2 ^ k - 1) theta2 / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (w (c (singlePieceTheta
            (spectrumPieceRho cR (nestC (fun _ => C) (2 ^ k - 1) theta2)) 1))
          (w (singlePieceTheta (spectrumPieceRho cR (nestC (fun _ => C) (2 ^ k - 1) theta2)) 1)
            ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) - 1) - 1 ≤ S.width ∧
        singlePieceDensity c (spectrumPieceRho cR (nestC (fun _ => C) (2 ^ k - 1) theta2)) 1 *
            S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card := by
  have hk0 : 0 < k := hk
  -- 1. the remainder piece on the full box
  set P0 := fullSpaceBox N (k + 1) with hP0def
  have hP0 : P0.IsProper := fullSpaceBox_isProper N (k + 1)
  have hP0carrier : P0.carrier = Finset.univ := fullSpaceBox_carrier N (k + 1)
  have hP0width : P0.width = N := fullSpaceBox_width N (k + 1) (Nat.succ_pos k)
  have hP0card : (P0.carrier.card : Real) = (N : Real) ^ (k + 1) := by
    rw [hP0carrier, Finset.card_univ]
    simp [Point, ZMod.card]
  obtain ⟨R1, Mrem, hR1, -, hR1w, hMrem, hR1c⟩ := remainder_piece_on DomV hvert hC hW
    hθ₂pos hθ₂le P0 B1 hP0 (by rw [hP0carrier]; exact Finset.subset_univ _) hB1V
    (by rw [hP0card]; exact hB1card)
  rw [hP0width] at hR1w
  set ρ1 := nestC (fun _ => C) (2 ^ k - 1) theta2 with hρ1def
  have hρ1 : 0 < ρ1 ∧ ρ1 ≤ 1 :=
    nestC_pos_le (c := fun _ => C) (fun _ => hC) _ theta2 hθ₂pos hθ₂le
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
  -- 2. a short-parent dense cell
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
  have hEB1' : ∀ p ∈ E, appendCoordinate p.1 p.2 ∈ B1 := fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hEmem p hp)).1).1
  have hEB1 : ∀ p ∈ E, appendCoordinate p.1 p.2 ∈ section16GoodDomain B H Y x0 := fun p hp =>
    hB1 (hEB1' p hp)
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
  -- 3. the spectrum step
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
  have hK : ∀ h x, (h, x) ∈ E → ∀ r ∈ section16LargeSpectrum B h delta,
      (h, r) ∈ section16SpectrumRelation B delta := by
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
      J.step ∈ bohr (section16LargeSpectrum B h delta) (zeta / v) →
      LinearOn (J.carrier ∩ Finset.univ.filter fun x =>
        (h, x) ∈ section16InducedDomain B H Y) (phiPrime h) := by
    intro h x hx v hv J hJ hd
    have hhH : h ∈ H := (hgoodpair (h, x) hx).1
    have hlin := hselection.2 h hhH v hv J.step hd J rfl hJ
    simpa only [Finset.inter_filter, Finset.inter_univ] using hlin
  have hsl' : ∀ x ∈ I.carrier, LocalPieceFor c w (DomS x) (fun h => phi1 (h, x)) := by
    intro x _
    refine (hsl x).congr rfl (fun h => ?_)
    rw [hphi1def]
    simp only [section16PhiOne, section16Init_appendCoordinate, section16Last_appendCoordinate]
    congr 2
    funext i
    simp [add_comm]
  have hDom : ∀ p ∈ E, p.1 ∈ DomS p.2 := by
    intro p hp
    have h := hB1S _ (hEB1' p hp)
    simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate] using h
  have hEG : ∀ p ∈ E, p.1 ∈ DomG := by
    intro p hp
    have h := hB1G _ (hEB1' p hp)
    simpa only [section16Init_appendCoordinate] using h
  have hQwidth : ⌈(nestW (fun _ => C) (fun _ => W) (2 ^ k - 1) theta2 N : Real) / 8⌉₊ ≤
      Q.width := by
    apply Nat.ceil_le.mpr
    refine le_trans ?_ hQw
    exact div_le_div_of_nonneg_right (by exact_mod_cast hR1w) (by norm_num)
  obtain ⟨q, hq, S, mu, hS, -, hSw, hmu, hcount⟩ :=
    single_piece_of_spectrum_cover_for hk0 hcR hc hw eps thr hretile hz hz2
      Q I hQ hI hQd (by rw [hQstep]; exact R1.axis_step _) hshort hQI
      (by omega) E hEsub hρ1.1 hρ1.2 hEc phi1 phiPrime ((-1 : ZMod N) ^ k) Mrem hMrem hident
      (section16SpectrumRelation B delta) DomG hcovG hEG
      (fun h => section16LargeSpectrum B h delta) hK
      (fun h => Finset.univ.filter fun x => (h, x) ∈ section16InducedDomain B H Y) hA hlinear
      DomS hsl' hDom m hm1 (hm.trans (hwR _ hQwidth)) hpar
  -- 4. translate the piece of `φ₁` back to `φ`
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


/-- The deletion budget of each good set: `θ₂/(2(2^k+1))`. -/
def globalBudget (theta gamma : Real) (k : Nat) : Real :=
  section16ThetaTwo (section16ThetaOne theta gamma k) / (2 * (2 ^ k + 1))

/-- The density of the retained good domain: `θ₂/2`. -/
def globalTheta2 (theta gamma : Real) (k : Nat) : Real :=
  section16ThetaTwo (section16ThetaOne theta gamma k) / 2

theorem section16ThetaTwo_pos_le {theta gamma : Real} (k : Nat) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16ThetaTwo (section16ThetaOne theta gamma k) ∧
      section16ThetaTwo (section16ThetaOne theta gamma k) ≤ 1 := by
  obtain ⟨h1, h2, -, -⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  refine ⟨by unfold section16ThetaTwo; positivity, ?_⟩
  unfold section16ThetaTwo
  have h8 : section16ThetaOne theta gamma k ^ 8 ≤ 1 := pow_le_one₀ h1.le h2
  have h22 : (2 : Real) ^ (-(32 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  calc (2 : Real) ^ (-(32 : Real)) * section16ThetaOne theta gamma k ^ 8 ≤ 1 * 1 :=
        mul_le_mul h22 h8 (by positivity) zero_le_one
    _ = 1 := one_mul 1

/-- A face pullback of a product-property function has a cover on a good
set, from `PolyCoverAt` in the face dimension. -/
theorem PolyCoverAt.face_cover {l d : Nat} {Qb Eb : Real → Real → Real → Real}
    (hcov : PolyCoverAt l Qb Eb) {N : Nat} [NeZero N] [Fact N.Prime] {gamma theta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    {B : Finset (Point N d)} {phi : Point N d → ZMod N} (hB : HasProductProperty B phi gamma)
    (F : CoordinateFace N d l) :
    ∃ J : Finset (Point N l), (1 - theta) * (N : Real) ^ l ≤ J.card ∧
      MultiplyLinearWith (Qb gamma theta) (Eb gamma theta)
        (restrictRelation (partialGraph (F.domain B) (F.pullback phi)) J) := by
  apply hcov N gamma theta hg hg1 ht ht1
  · rw [partialGraph_card]
    have hle : ((F.domain B).card : Real) ≤ (N : Real) ^ l := by
      exact_mod_cast (show (F.domain B).card ≤ N ^ l by
        simpa [Point, ZMod.card] using Finset.card_le_univ (F.domain B))
    have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
      rw [zpow_neg, zpow_ofNat]
      exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
    calc ((F.domain B).card : Real) ≤ (N : Real) ^ l := hle
      _ ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ l :=
          le_mul_of_one_le_left (by positivity) hginv
  · exact partialGraph_relationProductProperty (hB.coordinateFace F)

/-- **The single-piece lift from global-to-local covers.** -/
theorem single_piece_lift_global {k : Nat} (hk : 1 ≤ k) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {C : Real → Real} {W : Real → Nat → Nat}
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, C t ≤ (liftLastC^[k + 1 - l]
      (fun s => s / 2 / Qb l gamma (globalBudget theta gamma k) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, W t L ≤ (liftLastW^[k + 1 - l]
      (coverWidth (Eb l gamma (globalBudget theta gamma k)))) t L)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hB : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma)
    (hL4 : 4 ≤ nestW (fun _ => C) (fun _ => W) (2 ^ k - 1) (globalTheta2 theta gamma k) N)
    (m : Nat) (hm1 : 1 ≤ m)
    (hm : m ≤ coverWidth (Eb k (section16Delta (section16ThetaOne theta gamma k))
        (globalBudget theta gamma k))
      (nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k) / 2)
      ⌈(nestW (fun _ => C) (fun _ => W) (2 ^ k - 1) (globalTheta2 theta gamma k) N : Real) / 8⌉₊)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qb k (section16Delta (section16ThetaOne theta gamma k))
        (globalBudget theta gamma k)
        (nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k) / 2 / 2) →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
      2 ≤ spectrumPieceRho (fun t => t / 2)
          (nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k)) ^ 3 *
        spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
      2 ≤ coverWidth (Eb k gamma (globalBudget theta gamma k))
          ((fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k))) 1))
        (coverWidth (Eb k gamma (globalBudget theta gamma k))
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k))) 1)
          ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊)) :
    ∃ q : Nat, (q : Real) ≤ Qb k (section16Delta (section16ThetaOne theta gamma k))
        (globalBudget theta gamma k)
        (nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k) / 2 / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (coverWidth (Eb k gamma (globalBudget theta gamma k))
          ((fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k))) 1))
          (coverWidth (Eb k gamma (globalBudget theta gamma k))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k))) 1)
            ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊) - 1) - 1 ≤
          S.width ∧
        singlePieceDensity (fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2))
            (spectrumPieceRho (fun t => t / 2)
              (nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k))) 1 *
            S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card := by
  have hk0 : 0 < k := hk
  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  obtain ⟨hζpos, hζle⟩ := section16Zeta_pos_le_one_div_32 k ht ht1 hg hg1
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le k ht ht1 hg hg1
  set θ₂ := section16ThetaTwo (section16ThetaOne theta gamma k) with hθ₂def
  set θ' := globalBudget theta gamma k with hθ'def
  have hθ'pos : 0 < θ' := by rw [hθ'def, globalBudget]; positivity
  have hθ'le : θ' ≤ 1 := by
    rw [hθ'def, globalBudget, div_le_one (by positivity)]
    have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  set δ := section16Delta (section16ThetaOne theta gamma k) with hδdef
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
  have hB1card : θ₂ * (N : Real) ^ (k + 1) ≤ B1.card := by
    rw [hB1def, section16GoodDomain_card]; exact hgood
  set t := appendCoordinate x0 0 with htdef
  -- 2. the spectrum cover
  obtain ⟨JΔ, hJΔ, hMLΔ⟩ := hcov k hk le_rfl N δ θ' hδpos hδle hθ'pos hθ'le
    (section16SpectrumRelation B δ) (section16_spectrum_relation_card B hδpos)
    (section16_spectrum_relation_product B hδpos)
  have hcovG := hMLΔ.localRelationCoverFor (hEb k δ θ')
  -- 3. the vertex covers
  have hvex : ∀ e : Fin k → Bool, ∃ J : Finset (Point N (section16VertexDirections e).card),
      e ≠ (fun _ => true) →
        (1 - θ') * (N : Real) ^ (section16VertexDirections e).card ≤ J.card ∧
        MultiplyLinearWith (Qb (section16VertexDirections e).card gamma θ')
          (Eb (section16VertexDirections e).card gamma θ')
          (restrictRelation (partialGraph
            ((coordinateSubsetFace (section16VertexDirections e) t).domain B)
            ((coordinateSubsetFace (section16VertexDirections e) t).pullback phi)) J) := by
    intro e
    by_cases he : e = fun _ => true
    · exact ⟨∅, fun h => absurd he h⟩
    · have hl1 : 1 ≤ (section16VertexDirections e).card :=
        Finset.card_pos.mpr ⟨_, section16VertexDirections_last e⟩
      have hlk : (section16VertexDirections e).card ≤ k := by
        have := section16VertexDirections_card_lt he
        omega
      obtain ⟨J, hJ, hML⟩ := (hcov _ hl1 hlk).face_cover hg hg1 hθ'pos hθ'le hprodB
        (coordinateSubsetFace (section16VertexDirections e) t)
      exact ⟨J, fun _ => ⟨hJ, hML⟩⟩
  choose Jv hJv using hvex
  set DomV : (Fin k → Bool) → Finset (Point N (k + 1)) := fun e =>
    Finset.univ.filter fun z => selectedCoordinates
      (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∈
        (coordinateSubsetFace (section16VertexDirections e) t).domain B ∩ Jv e with hDomVdef
  have hvert : ∀ e : Fin k → Bool, e ≠ (fun _ => true) →
      LocalPieceFor C W (DomV e) (section16TranslatedVertex phi x0 e) := by
    intro e he
    have hl1 : 1 ≤ (section16VertexDirections e).card :=
      Finset.card_pos.mpr ⟨_, section16VertexDirections_last e⟩
    have hlk : (section16VertexDirections e).card ≤ k := by
      have := section16VertexDirections_card_lt he
      omega
    obtain ⟨-, hML⟩ := hJv e he
    have hF := hML.localPieceFor (hQb _ gamma θ') (hEb _ gamma θ')
    have hcF : ∀ s, 0 < s → s ≤ 1 →
        0 < s / 2 / Qb (section16VertexDirections e).card gamma θ' (s / 2) ∧
          s / 2 / Qb (section16VertexDirections e).card gamma θ' (s / 2) ≤ 1 := by
      intro s hs hs1
      have hq := hQb (section16VertexDirections e).card gamma θ' (s / 2) (by positivity)
        (by linarith)
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by linarith)]
      linarith
    exact (vertex_localPieceFor_of_face e hcF (coverWidth_mono _) x0 hF).mono
      (hCle _ hl1 hlk) (hWle _ hl1 hlk)
  -- 4. the slice covers
  have hsex : ∀ x : ZMod N, ∃ J : Finset (Point N k),
      (1 - θ') * (N : Real) ^ k ≤ J.card ∧
      MultiplyLinearWith (Qb k gamma θ') (Eb k gamma θ')
        (restrictRelation (partialGraph ((lastSliceFace k x).domain B)
          ((lastSliceFace k x).pullback phi)) J) := fun x =>
    (hcov k hk le_rfl).face_cover hg hg1 hθ'pos hθ'le hprodB (lastSliceFace k x)
  choose Js hJs hMLs using hsex
  set DomS : ZMod N → Finset (Point N k) := fun x =>
    Finset.univ.filter fun h => h + x0 ∈ (lastSliceFace k x).domain B ∩ Js x with hDomSdef
  have hsl : ∀ x, LocalPieceFor (fun s => s / 2 / Qb k gamma θ' (s / 2))
      (coverWidth (Eb k gamma θ')) (DomS x) (fun h => phi (appendCoordinate (h + x0) x)) :=
    fun x => ((hMLs x).localPieceFor (hQb k gamma θ') (hEb k gamma θ')).translate x0
  -- 5. the retained good domain
  set E := Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true with hEdef
  set B1' := B1.filter fun z => section16Init z ∈ JΔ ∧
      (∀ e ∈ E, selectedCoordinates
        (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∈ Jv e) ∧
      section16Init z + x0 ∈ Js (section16Last z) with hB1'def
  -- the three bad sets are sparse
  have hbadΔ : ((Finset.univ.filter fun z : Point N (k + 1) =>
      section16Init z ∉ JΔ).card : Real) ≤ θ' * (N : Real) ^ (k + 1) := by
    have h := card_filter_selected_not_mem_le (n := k + 1) (l := k)
      ⟨Fin.castSucc, Fin.castSucc_injective k⟩ 0 JΔ hJΔ (by omega)
    have hfun : ∀ z : Point N (k + 1),
        (fun i => z ((⟨Fin.castSucc, Fin.castSucc_injective k⟩ : Fin k ↪ Fin (k + 1)) i) +
          (0 : Point N k) i) = section16Init z := fun z => by
      funext i; simp [section16Init]
    simp only [hfun] at h
    exact h
  have hbadV : ∀ e ∈ E, ((Finset.univ.filter fun z : Point N (k + 1) => selectedCoordinates
      (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∉ Jv e).card : Real) ≤
      θ' * (N : Real) ^ (k + 1) := by
    intro e he
    have hne : e ≠ fun _ => true := (Finset.mem_filter.mp he).2
    have hlk : (section16VertexDirections e).card ≤ k + 1 := by
      have := section16VertexDirections_card_lt hne
      omega
    exact card_filter_selected_not_mem_le
      (coordinateSubsetFace (section16VertexDirections e) t).free
      (fun i => t ((coordinateSubsetFace (section16VertexDirections e) t).free i))
      (Jv e) (hJv e hne).1 hlk
  have hbadS : ((Finset.univ.filter fun z : Point N (k + 1) =>
      section16Init z + x0 ∉ Js (section16Last z)).card : Real) ≤
      θ' * (N : Real) ^ (k + 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := section16Last) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast
    have hfib : ∀ x : ZMod N, (((Finset.univ.filter fun z : Point N (k + 1) =>
        section16Init z + x0 ∉ Js (section16Last z)).filter fun z => section16Last z = x).card :
          Real) ≤ θ' * (N : Real) ^ k := by
      intro x
      have h1 : ((Finset.univ.filter fun z : Point N (k + 1) =>
          section16Init z + x0 ∉ Js (section16Last z)).filter fun z =>
            section16Last z = x).card ≤
          (Finset.univ.filter fun h : Point N k => h + x0 ∉ Js x).card := by
        refine Finset.card_le_card_of_injOn section16Init (fun z hz => ?_) ?_
        · obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
          have hz1' := (Finset.mem_filter.mp hz1).2
          rw [hz2] at hz1'
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz1'⟩
        · intro z hz z' hz' hzz
          apply initLast_injective
          simp only [Prod.mk.injEq]
          exact ⟨hzz, ((Finset.mem_filter.mp hz).2).trans ((Finset.mem_filter.mp hz').2).symm⟩
      have h2 := card_filter_selected_not_mem_le (n := k) (l := k)
        (Function.Embedding.refl (Fin k)) x0 (Js x) (hJs x) le_rfl
      simp only [Function.Embedding.refl_apply, pow_zero] at h2
      have h1' : (((Finset.univ.filter fun z : Point N (k + 1) =>
          section16Init z + x0 ∉ Js (section16Last z)).filter fun z =>
            section16Last z = x).card : Real) ≤
          ((Finset.univ.filter fun h : Point N k => h + x0 ∉ Js x).card : Real) := by
        exact_mod_cast h1
      exact h1'.trans h2
    calc ∑ x : ZMod N, (((Finset.univ.filter fun z : Point N (k + 1) =>
          section16Init z + x0 ∉ Js (section16Last z)).filter fun z =>
            section16Last z = x).card : Real)
        ≤ ∑ _x : ZMod N, θ' * (N : Real) ^ k := Finset.sum_le_sum fun x _ => hfib x
      _ = θ' * (N : Real) ^ (k + 1) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, pow_succ]; ring
  -- the retained domain is dense
  have hE : (E.card : Real) = 2 ^ k - 1 := by
    rw [hEdef, nonTopVertices_card]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    push_cast [this]
    ring
  have hcover : B1 ⊆ B1' ∪ (Finset.univ.filter fun z : Point N (k + 1) =>
      section16Init z ∉ JΔ) ∪ (E.biUnion fun e => Finset.univ.filter fun z : Point N (k + 1) =>
        selectedCoordinates (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∉
          Jv e) ∪ (Finset.univ.filter fun z : Point N (k + 1) =>
        section16Init z + x0 ∉ Js (section16Last z)) := by
    intro z hz
    by_cases h1 : section16Init z ∈ JΔ
    · by_cases h2 : ∀ e ∈ E, selectedCoordinates
          (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∈ Jv e
      · by_cases h3 : section16Init z + x0 ∈ Js (section16Last z)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hz, h1, h2, h3⟩)))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩)
      · push_neg at h2
        obtain ⟨e, he, hbad⟩ := h2
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)))
  have hB1'card : globalTheta2 theta gamma k * (N : Real) ^ (k + 1) ≤ B1'.card := by
    set X1 := Finset.univ.filter fun z : Point N (k + 1) => section16Init z ∉ JΔ with hX1
    set X2 := E.biUnion fun e => Finset.univ.filter fun z : Point N (k + 1) =>
        selectedCoordinates (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∉
          Jv e with hX2
    set X3 := Finset.univ.filter fun z : Point N (k + 1) =>
        section16Init z + x0 ∉ Js (section16Last z) with hX3
    have hc := Finset.card_le_card hcover
    have hu1 := Finset.card_union_le (B1' ∪ X1 ∪ X2) X3
    have hu2 := Finset.card_union_le (B1' ∪ X1) X2
    have hu3 := Finset.card_union_le B1' X1
    have hb := Finset.card_biUnion_le (s := E) (t := fun e => Finset.univ.filter
      fun z : Point N (k + 1) => selectedCoordinates
        (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∉ Jv e)
    have hbR : (X2.card : Real) ≤ E.card * (θ' * (N : Real) ^ (k + 1)) := by
      have hb' : (X2.card : Real) ≤ ∑ e ∈ E, ((Finset.univ.filter fun z : Point N (k + 1) =>
          selectedCoordinates (coordinateSubsetFace (section16VertexDirections e) t).free
            (z + t) ∉ Jv e).card : Real) := by
        exact_mod_cast hb
      refine hb'.trans ?_
      calc ∑ e ∈ E, ((Finset.univ.filter fun z : Point N (k + 1) => selectedCoordinates
            (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∉
              Jv e).card : Real)
          ≤ ∑ _e ∈ E, θ' * (N : Real) ^ (k + 1) := Finset.sum_le_sum hbadV
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h' : (B1.card : Real) ≤ (B1'.card : Real) + (X1.card : Real) + (X2.card : Real) +
        (X3.card : Real) := by
      have h := (hc.trans hu1).trans (Nat.add_le_add_right (hu2.trans
        (Nat.add_le_add_right hu3 _)) _)
      exact_mod_cast h
    rw [hE] at hbR
    have hθ'eq : θ' * (2 ^ k + 1) = θ₂ / 2 := by
      rw [hθ'def, globalBudget, ← hθ₂def]
      field_simp
    have hNk1 : (0 : Real) ≤ (N : Real) ^ (k + 1) := by positivity
    rw [globalTheta2, ← hθ₂def]
    nlinarith
  -- memberships
  have hB1'B1 : B1' ⊆ section16GoodDomain B H Y x0 := Finset.filter_subset _ _
  have hB1V : ∀ e : Fin k → Bool, e ≠ (fun _ => true) → B1' ⊆ DomV e := by
    intro e he z hz
    obtain ⟨hzB1, -, hzV, -⟩ := Finset.mem_filter.mp hz
    have heq : (coordinateSubsetFace (section16VertexDirections e) t).map
        (selectedCoordinates (coordinateSubsetFace (section16VertexDirections e) t).free
          (z + t)) =
        appendCoordinate (fun i => x0 i + if e i then section16Init z i else 0)
          (section16Last z) := by
      rw [← section16_vertex_coordinate_mask x0 e z]
      funext j
      exact coordinateSubsetFace_retraction _ t (z + t) j
    simp only [hDomVdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      CoordinateFace.mem_domain]
    refine ⟨?_, hzV e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)⟩
    rw [heq]
    exact section16GoodDomain_vertex_mem B H Y x0 hzB1 e
  have hB1G : ∀ z ∈ B1', section16Init z ∈ JΔ := fun z hz => (Finset.mem_filter.mp hz).2.1
  have hB1S : ∀ z ∈ B1', section16Init z ∈ DomS (section16Last z) := by
    intro z hz
    obtain ⟨hzB1, -, -, hzS⟩ := Finset.mem_filter.mp hz
    simp only [hDomSdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      CoordinateFace.mem_domain]
    refine ⟨?_, hzS⟩
    have h := section16GoodDomain_vertex_mem B H Y x0 hzB1 (fun _ => true)
    simp only [if_true] at h
    have hcomm : (fun i => x0 i + section16Init z i) = section16Init z + x0 := by
      funext i; simp [add_comm]
    rw [hcomm] at h
    exact h
  have hcR : ∀ s : Real, 0 < s → s ≤ 1 → 0 < s / 2 ∧ s / 2 ≤ 1 := fun s hs hs1 =>
    ⟨by positivity, by linarith⟩
  have hc : ∀ s : Real, 0 < s → s ≤ 1 → 0 < s / 2 / Qb k gamma θ' (s / 2) ∧
      s / 2 / Qb k gamma θ' (s / 2) ≤ 1 := by
    intro s hs hs1
    have hq := hQb k gamma θ' (s / 2) (by positivity) (by linarith)
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨hθ₂'pos, hθ₂'le⟩ : 0 < globalTheta2 theta gamma k ∧ globalTheta2 theta gamma k ≤ 1 :=
    ⟨by rw [globalTheta2]; positivity, by rw [globalTheta2]; linarith⟩
  exact single_piece_lift_core hk hζpos (by linarith) (cR := fun s => s / 2)
    (Qc := fun s => Qb k δ θ' (s / 2)) (wR := coverWidth (Eb k δ θ')) hcR (coverWidth_mono _)
    hc (coverWidth_mono _) hC hW eps thr hretile B phi H Y phiPrime x0 hselection hid B1'
    hB1'B1 hθ₂'pos hθ₂'le hB1'card DomV hvert hB1V JΔ hcovG hB1G DomS hsl hB1S hL4 m hm1 hm hpar

end LeanProofs.GowersSzemeredi
