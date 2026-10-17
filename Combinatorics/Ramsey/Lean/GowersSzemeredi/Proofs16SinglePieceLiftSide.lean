import GowersSzemeredi.Proofs16SinglePieceLift
import GowersSzemeredi.Proofs16Lemma6Parameters

/-! Declarations of `Proofs16SinglePieceLift` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open Classical

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
  obtain ⟨hθ₁pos, hθ₁le, hδpos, _⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
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
  set P0 := fullSpaceBox N (k + 1)
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
  set ρ1 := liftRemainderRho C theta gamma k
  have hρ1 : 0 < ρ1 ∧ ρ1 ≤ 1 := nestC_pos_le (c := fun _ => C) (fun _ => hC) _ θ₂ hθ₂pos hθ₂le
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
  -- 3. a short-parent dense cell
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
    exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hR1w) (by norm_num)) hQw
  obtain ⟨q, hq, S, mu, hS, _, hSw, hmu, hcount⟩ :=
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

end

end LeanProofs.GowersSzemeredi
