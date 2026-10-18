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

`section16ThetaTwo_pos_le`, `single_piece_lift_core`,
`single_piece_lift_core_rem` and `single_piece_lift_global` are in
`Proofs16SinglePieceGlobalSide`, outside the final route. -/
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
  obtain ⟨R1, Mrem, hR1, hR1w, hMrem, hR1c⟩ := hrem
  set E1 := B1.filter fun x => x ∈ R1.carrier ∧ section16PhiRemainder phi x0 x = Mrem x
  have hR1w4 : 4 ≤ R1.width := hL4.trans hR1w
  have hR1ne : R1.carrier.Nonempty :=
    R1.carrier_nonempty_of_axis_pos fun z => lt_of_lt_of_le (by omega) (R1.width_le_axis_length z)
  have hE1ne : E1.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos hρ1.1 (Nat.cast_pos.mpr hR1ne.card_pos)).trans_le hR1c))
  -- 2. a short-parent dense cell
  obtain ⟨Q, hQ, -, hQw, hshort, hQI, hQstep, hQd, hQc⟩ := exists_short_parent_dense_cell hk R1
    hR1 hR1w4 E1 (fun x hx => (Finset.mem_filter.mp hx).2.1) hE1ne hR1c
  set I := R1.axis (Fin.last k)
  have hIlen : R1.width ≤ I.length := R1.width_le_axis_length (Fin.last k)
  set E2 := E1.filter fun z => z ∈ lastProductSet Q.carrier I.carrier
  set E := E2.image fun z => (section16Init z, section16Last z)
  have hEmem : ∀ p ∈ E, appendCoordinate p.1 p.2 ∈ E2 := fun p hp => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    simpa only [appendCoordinate_init_last] using hz
  have hEB1 : ∀ p ∈ E, appendCoordinate p.1 p.2 ∈ B1 := fun p hp =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hEmem p hp)).1).1
  have hEsub : E ⊆ Q.carrier ×ˢ I.carrier := fun p hp => by
    simpa [lastProductSet] using (Finset.mem_filter.mp (hEmem p hp)).2
  have hEc : ρ1 * Q.carrier.card * I.carrier.card ≤ E.card := by
    rw [show E.card = E2.card from Finset.card_image_of_injective _ initLast_injective, mul_assoc]
    simpa only [lastProductSet_card, Nat.cast_mul] using hQc
  have hgoodpair : ∀ p ∈ E, Section16GoodInducedPair B H Y x0 (p.1, p.2) := fun p hp => by
    simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate] using
      (Finset.mem_filter.mp (hB1 (hEB1 p hp))).2
  have hcomm : ∀ h : Point N k, (fun i => x0 i + h i) = h + x0 :=
    fun h => funext fun i => add_comm _ _
  have hvertex : ∀ p ∈ E, appendCoordinate (p.1 + x0) p.2 ∈ B := fun p hp => by
    have h := section16GoodDomain_vertex_mem B H Y x0 (hB1 (hEB1 p hp)) (fun _ => true)
    simp only [if_true, section16Init_appendCoordinate, section16Last_appendCoordinate] at h
    rwa [hcomm p.1] at h
  -- 3. the spectrum step, for `φ₁(h, x) = φ(h + x₀, x)`
  set phi1 : Point N k × ZMod N → ZMod N := fun p => phi (appendCoordinate (p.1 + x0) p.2)
  have hident : ∀ p ∈ E, phi1 p =
      (-1 : ZMod N) ^ k * phiPrime p.1 p.2 + Mrem (appendCoordinate p.1 p.2) := fun p hp => by
    have h1 := hid _ (hB1 (hEB1 p hp))
    simp only [section16PhiOne, section16PhiPrimeLift, section16Init_appendCoordinate,
      section16Last_appendCoordinate] at h1
    rw [hcomm p.1, (Finset.mem_filter.mp (Finset.mem_filter.mp (hEmem p hp)).1).2.2] at h1
    exact h1
  have hA : ∀ p ∈ E, p.2 ∈ (Finset.univ.filter fun x =>
      (p.1, x) ∈ section16InducedDomain B H Y) := fun p hp => by
    obtain ⟨hpH, C0, hC0, -, hC0x⟩ := hgoodpair p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, section16InducedDomain]
    exact ⟨hpH, C0, hC0, hC0x⟩
  have hlinear : ∀ h x, (h, x) ∈ E → ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (section16LargeSpectrum B h delta) (zeta / v) →
      LinearOn (J.carrier ∩ Finset.univ.filter fun x =>
        (h, x) ∈ section16InducedDomain B H Y) (phiPrime h) := by
    intro h x hx v hv J hJ hd
    simpa only [Finset.inter_filter, Finset.inter_univ] using
      hselection.2 h (hgoodpair (h, x) hx).1 v hv J.step hd J rfl hJ
  have hDom : ∀ p ∈ E, p.1 ∈ DomS p.2 := fun p hp => by
    simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate] using
      hB1S _ (hEB1 p hp)
  have hEG : ∀ p ∈ E, p.1 ∈ DomG := fun p hp => by
    simpa only [section16Init_appendCoordinate] using hB1G _ (hEB1 p hp)
  have hQwidth : ⌈(ω1 : Real) / 8⌉₊ ≤ Q.width := Nat.ceil_le.mpr
    ((div_le_div_of_nonneg_right (by exact_mod_cast hR1w) (by norm_num)).trans hQw)
  obtain ⟨q, hq, S, mu, hS, -, hSw, hmu, hcount⟩ :=
    single_piece_of_spectrum_cover_for_scheme hk hcR eps thr hretile hz hz2 Sc
      Q I hQ (hR1 _) hQd (by rw [hQstep]; exact R1.axis_step _) hshort hQI
      (by omega) E hEsub hρ1.1 hρ1.2 hEc phi1 phiPrime ((-1 : ZMod N) ^ k) Mrem hMrem hident
      (section16SpectrumRelation B delta) DomG hcovG hEG
      (fun h => section16LargeSpectrum B h delta)
      (fun h x _ r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
      (fun h => Finset.univ.filter fun x => (h, x) ∈ section16InducedDomain B H Y) hA hlinear
      DomS (fun x _ => hsl x) hDom m hm1 (hm.trans (hwR _ hQwidth)) hpar
  -- 4. translate the piece of `φ₁` back to `φ`
  set t : Point N (k + 1) := appendCoordinate x0 0 with htdef
  have hshift : ∀ p : Point N k × ZMod N,
      appendCoordinate p.1 p.2 + t = appendCoordinate (p.1 + x0) p.2 := fun p => by
    rw [htdef, appendCoordinate_add, add_zero]
  refine ⟨q, hq, S.translate t, fun z => mu (z + -t), hS.translate t, hmu.translate (-t),
    by rw [Box.translate_width]; exact hSw, ?_⟩
  rw [Box.translate_card]
  refine hcount.trans ?_
  exact_mod_cast Finset.card_le_card_of_injOn
    (fun p : Point N k × ZMod N => appendCoordinate p.1 p.2 + t)
    (fun p hp => by
      obtain ⟨hpE, hpS, hpmu⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨?_, (Box.translate_mem_carrier S t _).mpr hpS, ?_⟩
      · dsimp only; rw [hshift]; exact hvertex p hpE
      · dsimp only; rw [add_neg_cancel_right, hshift]; exact hpmu)
    (fun p _ p' _ h => appendCoordinate_pair_injective (add_right_cancel h))

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
      section16Init z + x0 ∈ Js (section16Last z) with hB1'
  change theta2 / 2 * (N : Real) ^ (k + 1) ≤ B1'.card
  set X1 := Finset.univ.filter fun z : Point N (k + 1) => section16Init z ∉ JΔ with hX1
  set X2 := E.biUnion fun e => Finset.univ.filter fun z : Point N (k + 1) =>
    selectedCoordinates (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∉
      Jv e with hX2
  set X3 := Finset.univ.filter fun z : Point N (k + 1) =>
    section16Init z + x0 ∉ Js (section16Last z) with hX3
  -- the three bad sets are sparse
  have h1 : (X1.card : Real) ≤ budget * (N : Real) ^ (k + 1) := by
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun z hz => ?_))
      (card_filter_selected_not_mem_le (n := k + 1) ⟨Fin.castSucc, Fin.castSucc_injective k⟩ 0 JΔ
        hJΔ (by omega))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.zero_apply, add_zero]
    exact (Finset.mem_filter.mp hz).2
  have h2 : (X2.card : Real) ≤ (2 ^ k - 1) * (budget * (N : Real) ^ (k + 1)) := by
    have hE : (E.card : Real) = 2 ^ k - 1 := by
      rw [hEdef, nonTopVertices_card, Nat.cast_sub Nat.one_le_two_pow]; norm_num
    refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
    rw [Nat.cast_sum, ← hE, ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun e he => ?_
    have hne := (Finset.mem_filter.mp he).2
    exact card_filter_selected_not_mem_le _ _ (Jv e) (hJv e hne)
      (by have := section16VertexDirections_card_lt hne; omega)
  have h3 : (X3.card : Real) ≤ budget * (N : Real) ^ (k + 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := section16Last) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _), Nat.cast_sum]
    refine (Finset.sum_le_card_nsmul _ _ (budget * (N : Real) ^ k) fun x _ => ?_).trans_eq
      (by rw [Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring)
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card_of_injOn section16Init (fun z hz => ?_)
      fun z hz z' hz' hzz => ?_)) (card_filter_selected_not_mem_le
        (Function.Embedding.refl _) x0 (Js x) (hJs x) le_rfl)
    · simp only [hX3, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [← hz.2]; exact hz.1
    · exact initLast_injective (Prod.ext hzz
        ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm))
  -- the retained domain is dense
  have hcover : B1 ⊆ B1' ∪ X1 ∪ X2 ∪ X3 := by
    intro z hz
    simp only [hB1', hX1, hX2, hX3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_biUnion]
    by_cases h : ∀ e ∈ E, selectedCoordinates
        (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∈ Jv e
    · tauto
    · obtain ⟨e, he, hbad⟩ := not_forall₂.mp h
      exact Or.inl (Or.inr ⟨e, he, hbad⟩)
  have hc : (B1.card : Real) ≤ B1'.card + X1.card + X2.card + X3.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
  have hbudgetN : budget * (2 ^ k + 1) * (N : Real) ^ (k + 1) =
      theta2 / 2 * (N : Real) ^ (k + 1) := by rw [hbudget]
  linarith

end LeanProofs.GowersSzemeredi
