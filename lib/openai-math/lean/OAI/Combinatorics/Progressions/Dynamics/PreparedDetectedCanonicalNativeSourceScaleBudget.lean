import OAI.Combinatorics.Progressions.Estimates.PreparedDetectedCanonicalGeometry

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ uG uI uB
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_detected_uniform_early_canonical_native_source_scales (m s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ b, Fintype (B b)] [∀ b, DecidableEq (B b)]
      {P pnum pSlice u Qstride Eextra : ℝ} {nX : ℕ},
      0 < m → s ≤ m → 0 ≤ P → 0 ≤ Eextra → pnum ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) →
      (∀ j, (n j : ℝ) ≤ pnum) →
      (∀ b : LayerSamplerAxis I n,
        (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b)) →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let pModel := allocatedEarlyModelLog P pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      P ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
        (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧
          (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp budget) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
        AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B
          (fun j : Fin m => (Subtype.val :
            boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
          δ η ρ t htone ∧
        ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
          (R : Fin m → ℝ), (∀ j, 0 < R j) →
          ∀ {pRadius : ℝ}, pRadius ∈ Set.Icc 0 P → (∀ j, (R j)⁻¹ ≤ Real.exp pRadius) →
          let Pscale := pRadius + Ptail
          let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
          Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget ∧
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            (∀ j, (R j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp Pscale) ∧
            Real.exp (allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod) ≤ S.value ∧
            (S.value : ℝ) ≤ Real.exp budget ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  obtain ⟨Ci, _, hinput⟩ := exists_canonicalDetectedScaleInput_budget s Cdetect
  obtain ⟨Cs, _, hscales⟩ := exists_uniform_early_canonical_slice_scales.{uJ,uQ,uG,uI,uB} m s Cdetect
  let X : Polynomial ℕ := Polynomial.X
  let inputPoly := (X + Polynomial.C Ci) ^ Ci + X
  let scalePoly := (inputPoly + Polynomial.C Cs) ^ Cs
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (inputPoly + scalePoly)
  refine ⟨C, hC, ?_⟩
  intro G _ _ I _ n B _ _ P pnum pSlice u Qstride Eextra nX hm hs hP hExtra hnum hK hI hn hblocks
    hpSlice hu hQstride hnX pModel pDetect aDetect D gainLog target Pk F Tmod δ E η Prho Ptail K budget
  let Qold := (P + Ci) ^ Ci
  let Q := Qold + Eextra
  let scaleBudget := (Q + Cs) ^ Cs
  let outerInput := (P + Eextra + Ci) ^ Ci + (P + Eextra)
  have hQold0 : 0 ≤ Qold := by dsimp only [Qold]; positivity
  have hQ0 : 0 ≤ Q := add_nonneg hQold0 hExtra
  have hscale0 : 0 ≤ scaleBudget := by dsimp only [scaleBudget]; positivity
  have houter0 : 0 ≤ outerInput := by dsimp only [outerInput]; positivity
  have hQouter : Q ≤ outerInput := by
    apply add_le_add
    · exact pow_le_pow_left₀ (by positivity) (by linarith) _
    · linarith
  have hsum : Q + scaleBudget ≤ budget := by
    calc
      Q + scaleBudget ≤ outerInput + (outerInput + Cs) ^ Cs :=
        add_le_add hQouter (pow_le_pow_left₀ (add_nonneg hQ0 (Nat.cast_nonneg Cs))
          (add_le_add hQouter (le_refl (Cs : ℝ))) Cs)
      _ ≤ budget := by
        simpa [X, inputPoly, scalePoly, outerInput, Polynomial.eval₂_pow] using
          hbound (P + Eextra) (add_nonneg hP hExtra)
  have hQbudget : Q ≤ budget := by linarith only [hsum, hscale0]
  have hscaleBudget : scaleBudget ≤ budget := by linarith only [hsum, hQ0]
  have hKP : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P := hK.trans hnum.2
  obtain ⟨hPQold, hmodelOld, hdetectOld, haOld, hgainOld, htOld⟩ := hinput hP hpSlice hu hKP
  have hOldQ : Qold ≤ Q := le_add_of_nonneg_right hExtra
  have hPQ : P ≤ Q := hPQold.trans hOldQ
  have hextend {x : ℝ} (hx : x ∈ Set.Icc 0 Qold) : x ∈ Set.Icc 0 Q :=
    ⟨hx.1, hx.2.trans hOldQ⟩
  have hmodelQ := hextend hmodelOld
  have hdetectQ := hextend hdetectOld
  have haQ := hextend haOld
  have htQ : target ∈ Set.Icc 0 Q :=
    ⟨add_nonneg htOld.1 hExtra, add_le_add htOld.2 (le_refl Eextra)⟩
  have hlift {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 Q := ⟨hx.1, hx.2.trans hPQ⟩
  have hinputLift {x : ℝ} (hx : x ∈ Set.Icc 0 Q) : x ∈ Set.Icc 0 budget :=
    ⟨hx.1, hx.2.trans hQbudget⟩
  have hscaleLift {x : ℝ} (hx : x ∈ Set.Icc 0 scaleBudget) : x ∈ Set.Icc 0 budget :=
    ⟨hx.1, hx.2.trans hscaleBudget⟩
  obtain ⟨_, hDb, hgainb, hkb, hrhob, htailb, hmodb, ρ, hρ,
      t, ht, htone, htlog, htbudget, hcomparison, hsamplers⟩ :=
    hscales (G := G) B hm hs hQ0 (hlift hnum) hK hI hn hblocks
      htQ hdetectQ hdetectQ haQ (hlift hQstride) (hnX.trans hPQ)
  refine ⟨hPQ.trans hQbudget, hinputLift hmodelQ, hinputLift hdetectQ, hinputLift haQ,
    hinputLift htQ, hscaleLift hDb, hscaleLift hgainb, hscaleLift hkb,
    hscaleLift hrhob, hscaleLift htailb, hscaleLift hmodb, ρ, ?_, t, ht, htone,
    htlog, htbudget.trans (Real.exp_le_exp.mpr hscaleBudget), hcomparison, ?_⟩
  · intro partition
    exact ⟨(hρ partition).1, (hρ partition).2.1, (hρ partition).2.2.1,
      (hρ partition).2.2.2.trans (Real.exp_le_exp.mpr hscaleBudget)⟩
  · intro J _ U basis R hR pRadius hRadius hRi Pscale scaleLog
    obtain ⟨hPscale, hscaleLog, S, hRiP, htP, hlength, hupper, hkernel⟩ :=
      hsamplers U basis R hR (hlift hRadius) hRi
    exact ⟨hscaleLift hPscale, hscaleLift hscaleLog, S, hRiP, htP, hlength,
      hupper.trans (Real.exp_le_exp.mpr hscaleBudget), hkernel⟩

theorem exists_prepared_detected_canonical_native_source_scales (m s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      let pnum : ℝ := preparedCommonSamplerDimension m M
      ∀ {P pSlice u Qstride Eextra : ℝ} {nX : ℕ},
      0 < m → ∀ hs : s ≤ m, 0 ≤ P → 0 ≤ Eextra → pnum ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let G := PreparedCommonKernel m
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := PreparedCommonSamplerBlock L
      let selection := preparedCommonCanonicalSelection m s hs
      let pModel := allocatedEarlyModelLog P pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      ((s + 1) * ((s + 1) + 2) ≤ Fintype.card G) ∧
      (∀ i, (selection i).val = i.val) ∧
      P ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
        (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧
          (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp budget) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
        AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B
          (fun j : Fin m => (Subtype.val :
            boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
          δ η ρ t htone ∧
        ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
          (R : Fin m → ℝ), (∀ j, 0 < R j) →
          ∀ {pRadius : ℝ}, pRadius ∈ Set.Icc 0 P → (∀ j, (R j)⁻¹ ≤ Real.exp pRadius) →
          let Pscale := pRadius + Ptail
          let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
          Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget ∧
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            (∀ j, (R j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp Pscale) ∧
            Real.exp (allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod) ≤ S.value ∧
            (S.value : ℝ) ≤ Real.exp budget ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  obtain ⟨C, hC, hscales⟩ := exists_detected_uniform_early_canonical_native_source_scales.{uJ,uQ,0,0,0} m s Cdetect
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M hM pnum P pSlice u Qstride Eextra nX hm hs hP hExtra hnum
    hpSlice hu hQstride hnX G I n B selection
  obtain ⟨hvars, hI, hn⟩ := preparedCommonSampler_dimensions L hM
  have hblocks : ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b) := by
    intro b
    have hjets := preparedCommonBlockCount_jets m b.1 ⟨s, Nat.lt_succ_of_le hs⟩
    have heq : (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card =
        Fintype.card (BoundedBooleanJet (Fin (s + 1)) (b.1.val + 1)) := by
      exact (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
    rw [heq]
    simpa only [B, PreparedCommonSamplerBlock, Fintype.card_fin] using hjets
  have hactual := hscales (G := G) (I := I) (n := n) B hm hs hP hExtra
    ⟨Nat.cast_nonneg _, hnum⟩ (Nat.cast_le.mpr hvars)
    (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j)) hblocks
    hpSlice hu hQstride hnX
  intro pModel pDetect aDetect D gainLog target Pk F Tmod δ E η Prho Ptail K budget
  exact ⟨preparedCommonCanonicalKernel_capacity m s hs, fun _ => rfl, hactual⟩

end Erdos3.VectorPolynomial

end

end OAI
