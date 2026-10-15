import GowersSzemeredi.Proofs16SinglePieceGlobal
import GowersSzemeredi.Proofs16SinglePieceGradedRemainder

/-! The single-piece lift with graded vertex providers (Notes L.10, G3a).

`single_piece_lift_global` asks for one density `C` below the lifted covers
of every face dimension `l ≤ k`, so every remainder vertex pays for the
largest face. Here vertex `e` uses `Cg l` with `l = |S_e|`, the dimension of
its face (`section16VertexDirections e`).
* `single_piece_lift_core_rem` is `single_piece_lift_core` with the remainder
  piece given as data, at density `ρ1` and width `ω1`.
* `single_piece_lift_global_graded` builds that piece with
  `remainder_piece_graded_on`, at the graded nest
  `gradedNestC Cg (vertexFaceCounts k) (k + 1) θ₂`.

Everything else is the uniform proof verbatim. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The number of non-top vertices whose face has dimension `j`. -/
def vertexFaceCounts (k : Nat) (j : Nat) : Nat :=
  (vertexBlock k (fun e => (section16VertexDirections e).card) j).card


/-- **The single-piece lift from global-to-local covers, graded by face dimension.** -/
theorem single_piece_lift_global_graded {k : Nat} (hk : 1 ≤ k) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {Cg : Nat → Real → Real} {Wg : Nat → Real → Nat → Nat}
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < Cg j t ∧ Cg j t ≤ 1) (hW : ∀ j t, Monotone (Wg j t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, Cg l t ≤ (liftLastC^[k + 1 - l]
      (fun s => s / 2 / Qb l gamma (globalBudget theta gamma k) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, Wg l t L ≤ (liftLastW^[k + 1 - l]
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
    (hL4 : 4 ≤ gradedNestW Cg Wg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k) N)
    (m : Nat) (hm1 : 1 ≤ m)
    (hm : m ≤ coverWidth (Eb k (section16Delta (section16ThetaOne theta gamma k))
        (globalBudget theta gamma k))
      (gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k) / 2)
      ⌈(gradedNestW Cg Wg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k) N : Real) / 8⌉₊)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qb k (section16Delta (section16ThetaOne theta gamma k))
        (globalBudget theta gamma k)
        (gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k) / 2 / 2) →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
      2 ≤ spectrumPieceRho (fun t => t / 2)
          (gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k)) ^ 3 *
        spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
      2 ≤ coverWidth (Eb k gamma (globalBudget theta gamma k))
          ((fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k))) 1))
        (coverWidth (Eb k gamma (globalBudget theta gamma k))
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k))) 1)
          ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊)) :
    ∃ q : Nat, (q : Real) ≤ Qb k (section16Delta (section16ThetaOne theta gamma k))
        (globalBudget theta gamma k)
        (gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k) / 2 / 2) ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (coverWidth (Eb k gamma (globalBudget theta gamma k))
          ((fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k))) 1))
          (coverWidth (Eb k gamma (globalBudget theta gamma k))
            (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
              (gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k))) 1)
            ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊) - 1) - 1 ≤
          S.width ∧
        singlePieceDensity (fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2))
            (spectrumPieceRho (fun t => t / 2)
              (gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k))) 1 *
            S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card := by
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
  set δ := section16Delta (section16ThetaOne theta gamma k)
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
  set t := appendCoordinate x0 0
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
      LocalPieceFor (Cg (section16VertexDirections e).card) (Wg (section16VertexDirections e).card)
        (DomV e) (section16TranslatedVertex phi x0 e) := by
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
  set E := Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true
  set B1' := B1.filter fun z => section16Init z ∈ JΔ ∧
      (∀ e ∈ E, selectedCoordinates
        (coordinateSubsetFace (section16VertexDirections e) t).free (z + t) ∈ Jv e) ∧
      section16Init z + x0 ∈ Js (section16Last z) with hB1'def
  have hB1'card : globalTheta2 theta gamma k * (N : Real) ^ (k + 1) ≤ B1'.card := by
    have hbudget : θ' * (2 ^ k + 1) = θ₂ / 2 := by
      rw [hθ'def, globalBudget, ← hθ₂def]
      field_simp
    rw [globalTheta2, ← hθ₂def]
    exact section16_retained_domain_card B1 t x0 JΔ Jv Js hJΔ
      (fun e he => (hJv e he).1) hJs hB1card hbudget
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
  -- 6. the graded remainder piece on the full box
  set P0 := fullSpaceBox N (k + 1)
  have hP0 : P0.IsProper := fullSpaceBox_isProper N (k + 1)
  have hP0carrier : P0.carrier = Finset.univ := fullSpaceBox_carrier N (k + 1)
  have hP0width : P0.width = N := fullSpaceBox_width N (k + 1) (Nat.succ_pos k)
  have hP0card : (P0.carrier.card : Real) = (N : Real) ^ (k + 1) := by
    rw [hP0carrier, Finset.card_univ]
    simp [Point, ZMod.card]
  obtain ⟨R1, Mrem, hR1, -, hR1w, hMrem, hR1c⟩ := remainder_piece_graded_on
    (fun e => (section16VertexDirections e).card) (k + 1)
    (fun e he => section16VertexDirections_card_lt he) DomV hvert hC hW
    hθ₂'pos hθ₂'le P0 B1' hP0 (by rw [hP0carrier]; exact Finset.subset_univ _) hB1V
    (by rw [hP0card]; exact hB1'card)
  rw [hP0width] at hR1w
  exact single_piece_lift_core_rem hk hζpos (by linarith) (cR := fun s => s / 2)
    (Qc := fun s => Qb k δ θ' (s / 2)) (wR := coverWidth (Eb k δ θ')) hcR (coverWidth_mono _)
    hc (coverWidth_mono _) eps thr hretile B phi H Y phiPrime x0 hselection hid B1'
    hB1'B1 hθ₂'pos hθ₂'le hB1'card _ (gradedNestC_pos_le hC _ _ _ hθ₂'pos hθ₂'le) _
    ⟨R1, Mrem, hR1, hR1w, hMrem, hR1c⟩ JΔ hcovG hB1G DomS hsl hB1S hL4 m hm1 hm hpar

end LeanProofs.GowersSzemeredi
