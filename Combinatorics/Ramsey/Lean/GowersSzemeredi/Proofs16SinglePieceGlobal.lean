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
inputs, they are satisfiable.

`section16ThetaTwo_pos_le`, `single_piece_lift_core` and
`single_piece_lift_global` are in `Proofs16SinglePieceGlobalSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **The single-piece lift from a remainder piece** of density `ρ1` and width `ω1`. -/
theorem single_piece_lift_core_rem_scheme {k : Nat} (hk : 1 ≤ k) {delta zeta : Real}
    (hz : 0 < zeta) (hz2 : zeta ≤ 1 / 2)
    {Qc : Real → Real} {cR : Real → Real} {wR : Real → Nat → Nat}
    (hcR : ∀ t, 0 < t → t ≤ 1 → 0 < cR t ∧ cR t ≤ 1) (hwR : ∀ t, Monotone (wR t))
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime] (Sc : SliceScheme N k)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k)
    (hselection : Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime)
    (hid : Section16PhiOneIdentity (section16GoodDomain B H Y x0) phi x0 phiPrime)
    (B1 : Finset (Point N (k + 1))) (hB1 : B1 ⊆ section16GoodDomain B H Y x0)
    {theta2 : Real} (hθ₂pos : 0 < theta2) (hθ₂le : theta2 ≤ 1)
    (hB1card : theta2 * (N : Real) ^ (k + 1) ≤ B1.card)
    (ρ1 : Real) (hρ1 : 0 < ρ1 ∧ ρ1 ≤ 1) (ω1 : Nat)
    (hrem : ∃ (R1 : Box N (k + 1)) (Mrem : Point N (k + 1) → ZMod N),
      R1.IsProper ∧ ω1 ≤ R1.width ∧ IsMultilinear Mrem ∧
      ρ1 * R1.carrier.card ≤
        (B1.filter fun x => x ∈ R1.carrier ∧ section16PhiRemainder phi x0 x = Mrem x).card)
    (DomG : Finset (Point N k))
    (hcovG : LocalRelationCoverFor cR Qc wR DomG (section16SpectrumRelation B delta))
    (hB1G : ∀ z ∈ B1, section16Init z ∈ DomG)
    (DomS : ZMod N → Finset (Point N k))
    (hsl : ∀ x, Sc.SL (DomS x) (fun h => phi (appendCoordinate (h + x0) x)))
    (hB1S : ∀ z ∈ B1, section16Init z ∈ DomS (section16Last z))
    (hL4 : 4 ≤ ω1)
    (m : Nat) (hm1 : 1 ≤ m)
    (hm : m ≤ wR (ρ1 / 2)
      ⌈(ω1 : Real) / 8⌉₊)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qc (ρ1 / 2) →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth zeta m (eps q) ∧
      2 ≤ spectrumPieceRho cR (ρ1) ^ 3 *
        spectrumCellWidth zeta m (eps q) ∧
      2 ≤ Sc.wid (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1)
        ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) :
    ∃ q : Nat, (q : Real) ≤ Qc (ρ1 / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (Sc.wid (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1)
          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊ - 1) - 1 ≤ S.width ∧
        singlePieceTheta (spectrumPieceRho cR (ρ1)) 1 *
            Sc.dens (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1) * S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card := by
  have hk0 : 0 < k := hk
  obtain ⟨R1, Mrem, hR1, hR1w, hMrem, hR1c⟩ := hrem
  set E1 := B1.filter fun x => x ∈ R1.carrier ∧ section16PhiRemainder phi x0 x = Mrem x
    with _
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
  set I := R1.axis (Fin.last k)
  have hI : I.IsProper := hR1 (Fin.last k)
  have hIlen : R1.width ≤ I.length := R1.width_le_axis_length (Fin.last k)
  set E2 := E1.filter fun z => z ∈ lastProductSet Q.carrier I.carrier
  set E := E2.image fun z => (section16Init z, section16Last z)
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
  have hsl' : ∀ x ∈ I.carrier, Sc.SL (DomS x) (fun h => phi1 (h, x)) := by
    intro x _
    refine Sc.congr (hsl x) (fun h => ?_)
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
  have hQwidth : ⌈(ω1 : Real) / 8⌉₊ ≤
      Q.width := by
    apply Nat.ceil_le.mpr
    exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hR1w) (by norm_num)) hQw
  obtain ⟨q, hq, S, mu, hS, -, hSw, hmu, hcount⟩ :=
    single_piece_of_spectrum_cover_for_scheme hk0 hcR eps thr hretile hz hz2 Sc
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

/-- **The single-piece lift from a remainder piece** of density `ρ1` and width `ω1`. -/
theorem single_piece_lift_core_rem {k : Nat} (hk : 1 ≤ k) {delta zeta : Real}
    (hz : 0 < zeta) (hz2 : zeta ≤ 1 / 2)
    {Qc : Real → Real} {cR : Real → Real} {wR : Real → Nat → Nat}
    {c : Real → Real} {w : Real → Nat → Nat}
    (hcR : ∀ t, 0 < t → t ≤ 1 → 0 < cR t ∧ cR t ≤ 1) (hwR : ∀ t, Monotone (wR t))
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
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
    (ρ1 : Real) (hρ1 : 0 < ρ1 ∧ ρ1 ≤ 1) (ω1 : Nat)
    (hrem : ∃ (R1 : Box N (k + 1)) (Mrem : Point N (k + 1) → ZMod N),
      R1.IsProper ∧ ω1 ≤ R1.width ∧ IsMultilinear Mrem ∧
      ρ1 * R1.carrier.card ≤
        (B1.filter fun x => x ∈ R1.carrier ∧ section16PhiRemainder phi x0 x = Mrem x).card)
    (DomG : Finset (Point N k))
    (hcovG : LocalRelationCoverFor cR Qc wR DomG (section16SpectrumRelation B delta))
    (hB1G : ∀ z ∈ B1, section16Init z ∈ DomG)
    (DomS : ZMod N → Finset (Point N k))
    (hsl : ∀ x, LocalPieceFor c w (DomS x) (fun h => phi (appendCoordinate (h + x0) x)))
    (hB1S : ∀ z ∈ B1, section16Init z ∈ DomS (section16Last z))
    (hL4 : 4 ≤ ω1)
    (m : Nat) (hm1 : 1 ≤ m)
    (hm : m ≤ wR (ρ1 / 2)
      ⌈(ω1 : Real) / 8⌉₊)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qc (ρ1 / 2) →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth zeta m (eps q) ∧
      2 ≤ spectrumPieceRho cR (ρ1) ^ 3 *
        spectrumCellWidth zeta m (eps q) ∧
      2 ≤ w (c (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1))
        (w (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1)
          ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊)) :
    ∃ q : Nat, (q : Real) ≤ Qc (ρ1 / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (w (c (singlePieceTheta
            (spectrumPieceRho cR (ρ1)) 1))
          (w (singlePieceTheta (spectrumPieceRho cR (ρ1)) 1)
            ⌈spectrumCellWidth zeta m (eps q) / 8⌉₊) - 1) - 1 ≤ S.width ∧
        singlePieceDensity c (spectrumPieceRho cR (ρ1)) 1 *
            S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card :=
  single_piece_lift_core_rem_scheme hk hz hz2 hcR hwR eps thr hretile (localPieceScheme c w hc hw) B
    phi H Y phiPrime x0 hselection hid B1 hB1 hθ₂pos hθ₂le hB1card ρ1 hρ1 ω1 hrem DomG hcovG hB1G
    DomS hsl hB1S hL4 m hm1 hm hpar

/-- The deletion budget of each good set: `θ₂/(2(2^k+1))`. -/
def globalBudget (theta gamma : Real) (k : Nat) : Real :=
  section16ThetaTwo (section16ThetaOne theta gamma k) / (2 * (2 ^ k + 1))

/-- The density of the retained good domain: `θ₂/2`. -/
def globalTheta2 (theta gamma : Real) (k : Nat) : Real :=
  section16ThetaTwo (section16ThetaOne theta gamma k) / 2

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

/-- Retaining the spectrum, every non-top vertex and each last-coordinate slice
loses at most one common budget for each of the `2^k + 1` conditions. -/
theorem section16_retained_domain_card {N k : Nat} [NeZero N]
    (B1 : Finset (Point N (k + 1))) (t : Point N (k + 1)) (x0 : Point N k)
    (JΔ : Finset (Point N k))
    (Jv : (e : Fin k → Bool) → Finset (Point N (section16VertexDirections e).card))
    (Js : ZMod N → Finset (Point N k)) {theta2 budget : Real}
    (hJΔ : (1 - budget) * (N : Real) ^ k ≤ JΔ.card)
    (hJv : ∀ e : Fin k → Bool, e ≠ (fun _ => true) →
      (1 - budget) * (N : Real) ^ (section16VertexDirections e).card ≤ (Jv e).card)
    (hJs : ∀ x, (1 - budget) * (N : Real) ^ k ≤ (Js x).card)
    (hB1card : theta2 * (N : Real) ^ (k + 1) ≤ B1.card)
    (hbudget : budget * (2 ^ k + 1) = theta2 / 2) :
    theta2 / 2 * (N : Real) ^ (k + 1) ≤
      (B1.filter fun z => section16Init z ∈ JΔ ∧
        (∀ e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true),
          selectedCoordinates (coordinateSubsetFace (section16VertexDirections e) t).free
            (z + t) ∈ Jv e) ∧
        section16Init z + x0 ∈ Js (section16Last z)).card := by
  set E := Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true with hEdef
  set B1' := B1.filter fun z => section16Init z ∈ JΔ ∧
      (∀ e ∈ E, selectedCoordinates
        (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∈ Jv e) ∧
      section16Init z + x0 ∈ Js (section16Last z) with _
  change theta2 / 2 * (N : Real) ^ (k + 1) ≤ B1'.card
  -- the three bad sets are sparse
  have hbadΔ : ((Finset.univ.filter fun z : Point N (k + 1) =>
      section16Init z ∉ JΔ).card : Real) ≤ budget * (N : Real) ^ (k + 1) := by
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
      budget * (N : Real) ^ (k + 1) := by
    intro e he
    have hne : e ≠ fun _ => true := (Finset.mem_filter.mp he).2
    have hlk : (section16VertexDirections e).card ≤ k + 1 := by
      have := section16VertexDirections_card_lt hne
      omega
    exact card_filter_selected_not_mem_le
      (coordinateSubsetFace (section16VertexDirections e) t).free
      (fun i => t ((coordinateSubsetFace (section16VertexDirections e) t).free i))
      (Jv e) (hJv e hne) hlk
  have hbadS : ((Finset.univ.filter fun z : Point N (k + 1) =>
      section16Init z + x0 ∉ Js (section16Last z)).card : Real) ≤
      budget * (N : Real) ^ (k + 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := section16Last) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast
    have hfib : ∀ x : ZMod N, (((Finset.univ.filter fun z : Point N (k + 1) =>
        section16Init z + x0 ∉ Js (section16Last z)).filter fun z => section16Last z = x).card :
          Real) ≤ budget * (N : Real) ^ k := by
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
      simp only [Function.Embedding.refl_apply] at h2
      have h1' : (((Finset.univ.filter fun z : Point N (k + 1) =>
          section16Init z + x0 ∉ Js (section16Last z)).filter fun z =>
            section16Last z = x).card : Real) ≤
          ((Finset.univ.filter fun h : Point N k => h + x0 ∉ Js x).card : Real) := by
        exact_mod_cast h1
      exact h1'.trans h2
    calc ∑ x : ZMod N, (((Finset.univ.filter fun z : Point N (k + 1) =>
          section16Init z + x0 ∉ Js (section16Last z)).filter fun z =>
            section16Last z = x).card : Real)
        ≤ ∑ _x : ZMod N, budget * (N : Real) ^ k := Finset.sum_le_sum fun x _ => hfib x
      _ = budget * (N : Real) ^ (k + 1) := by
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
  set X1 := Finset.univ.filter fun z : Point N (k + 1) => section16Init z ∉ JΔ
  set X2 := E.biUnion fun e => Finset.univ.filter fun z : Point N (k + 1) =>
      selectedCoordinates (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∉
        Jv e with _
  set X3 := Finset.univ.filter fun z : Point N (k + 1) =>
      section16Init z + x0 ∉ Js (section16Last z) with _
  have hc := Finset.card_le_card hcover
  have hu1 := Finset.card_union_le (B1' ∪ X1 ∪ X2) X3
  have hu2 := Finset.card_union_le (B1' ∪ X1) X2
  have hu3 := Finset.card_union_le B1' X1
  have hb := Finset.card_biUnion_le (s := E) (t := fun e => Finset.univ.filter
    fun z : Point N (k + 1) => selectedCoordinates
      (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∉ Jv e)
  have hbR : (X2.card : Real) ≤ E.card * (budget * (N : Real) ^ (k + 1)) := by
    have hb' : (X2.card : Real) ≤ ∑ e ∈ E, ((Finset.univ.filter fun z : Point N (k + 1) =>
        selectedCoordinates (coordinateSubsetFace (section16VertexDirections e) t).free
          (z + t) ∉ Jv e).card : Real) := by
      exact_mod_cast hb
    refine hb'.trans ?_
    calc ∑ e ∈ E, ((Finset.univ.filter fun z : Point N (k + 1) => selectedCoordinates
          (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∉
            Jv e).card : Real)
        ≤ ∑ _e ∈ E, budget * (N : Real) ^ (k + 1) := Finset.sum_le_sum hbadV
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h' : (B1.card : Real) ≤ (B1'.card : Real) + (X1.card : Real) + (X2.card : Real) +
      (X3.card : Real) := by
    have h := (hc.trans hu1).trans (Nat.add_le_add_right (hu2.trans
      (Nat.add_le_add_right hu3 _)) _)
    exact_mod_cast h
  rw [hE] at hbR
  have hbudgetN := congrArg (fun x : Real => x * (N : Real) ^ (k + 1)) hbudget
  nlinarith

end LeanProofs.GowersSzemeredi
