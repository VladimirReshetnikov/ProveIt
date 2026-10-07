import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialNumericalPatchEndpoint
import OAI.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixColumns
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchTaggedBufferedScore

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]

theorem PreparedHeights.determiningRecoveryData
    {p qLog : ℝ} {R q n s d₀ d D returned : ℕ}
    (hL : L.PreparedHeights p R)
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
    (c : ∀ j, (L j).space) (e : Fin n ≃ L.PreparedCoordinate)
    (hp : 0 ≤ p) (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m))
    (hq : 0 < q) (hqLog : (q : ℝ) ≤ Real.exp qLog) (hm : m ≤ s)
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) :
    let r := Fintype.card (Σ j, E j)
    let w := sortedLayerCoordinateWeight E
    let P := L.dilatedCenteredDeterminingPolynomial bW c (fun j => (hL j).2.1) q
    let M := L.dilatedSortedDeterminingMatrix bW q e
    let pRow := fun i : Fin n => (e i).1.val + 1
    (∀ a, 1 ≤ w a) ∧
    (∀ a, w a ≤ s) ∧
    Monotone w ∧
    (∀ a, P a ∈ weightedSupportLE (fun _ : X => 1) (w a)) ∧
    (∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e (fun j => (L j).poly) (fun j => (c j).val) x =
        realIntegerMatrix M (fun a => MvPolynomial.aeval (fun i => (x i : ℝ)) (P a))) ∧
    (∀ j a, (standardEuclideanPoint (L j).Coord
        (fun i => M (e.symm ⟨j, i⟩) a)).val ∈ euclideanSubspace (L j).space) ∧
    (∀ i a, (q : ℤ) ∣ M i a) ∧
    (∀ i a, M i a ≠ 0 → w a ≤ pRow i) ∧
    (∀ i, (∑ a, |(M i a : ℝ)|) ≤
      Real.exp (qLog + (p + 2) ^ (preparedIntegralBasisExponent m + 1))) ∧
    r = ∑ j, (L j).rank ∧
    r + returned ≤ d₀ + s * d := by
  dsimp only
  refine ⟨sortedLayerCoordinateWeight_pos E,
    fun a => (sortedLayerCoordinateWeight_le E a).trans hm,
    sortedLayerCoordinateWeight_mono E, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact L.dilatedCenteredDeterminingPolynomial_support bW c
      (fun j => (hL j).2.1) q (fun j => (hL j).1)
  · exact L.fullTaggedBufferedCoordinates_eq_dilatedCenteredDetermining bW c
      (fun j => (hL j).2.1) q hq e
  · exact L.dilatedSortedDeterminingMatrix_column_mem bW q e
  · exact L.dilatedSortedDeterminingMatrix_dvd bW q e
  · exact L.dilatedSortedDeterminingMatrix_weight bW q e
  · intro i
    exact L.dilatedSortedDeterminingMatrix_row_abs_sum_le_exp bW q e i hqLog
      (L.sortedDeterminingMatrix_row_abs_sum_le_exp bW hp hcoord hbW e i)
  · exact L.integral_determining_card bW
  · exact L.sortedDeterminingRecovered_rank bW hprepared hD hreturned hm

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal Matrix

variable {X J₀ : Type} [Fintype X] [DecidableEq X]
variable {m : ℕ} (prep : RankPreparationFamily X J₀ m)
variable {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics setup)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) setup qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)

theorem relativePatchSliceConclusion_of_prepared_determining_score
    {preparationP qLog : ℝ} {Rprep : ℕ}
    (hprep : prep.PreparedHeights preparationP Rprep)
    (hp : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (hqLog : (member.slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp qLog)
    {degree d₀ old removed returned : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : returned ≤ d₀ + degree * (old - removed))
    (Bpatch : WeightedParameterPatch (X ⊕ Fin tagCount)
      (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1)) degree returned)
    (χ : PatchKernel tagCount)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected setup.hBactive o bW hb
        (fun j => (prep j).poly) (fun j => (hprep j).2.1) setup.κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e (fun j => (prep j).poly)
            (fun j => (member.slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : qLog + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp budget)
    (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ)) :
    RelativePatchSliceConclusion degree physicalN f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  let : ∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))) :=
    fun j => hprep.lattice_full prep hp hRprep j
  let q := member.slice.path.referenceRetainedCRTModulus cutoff
  let w := sortedLayerCoordinateWeight Eout
  let Pscalar := prep.dilatedCenteredDeterminingPolynomial bW member.slice.path.center
    (fun j => (hprep j).2.1) q
  let M := prep.dilatedSortedDeterminingMatrix bW q e
  let K : ℝ≥0 := ⟨Real.exp (qLog + (preparationP + 2) ^
    (preparedIntegralBasisExponent m + 1)), Real.exp_nonneg _⟩
  obtain ⟨hw, hws, hmono, hP, hcoords, hcol, hdiv, hweight, hM, _hcard, hrank⟩ :=
    hprep.determiningRecoveryData prep bW member.slice.path.center e hp hcoord hbW
      (member.slice.path.referenceRetainedCRTModulus_pos cutoff) hqLog hm
      hprepared hremoved hreturned
  have hr : (Fintype.card (Σ j, Eout j) : ℝ) ≤ budget :=
    (Nat.cast_le.mpr ((Nat.le_add_right _ returned).trans hrank)).trans hRankBudget
  have hE : (returned : ℝ) ≤ budget :=
    (Nat.cast_le.mpr ((Nat.le_add_left returned _).trans hrank)).trans hRankBudget
  have hqBudget : (q : ℝ) ≤ Real.exp budget := by
    apply hqLog.trans (Real.exp_le_exp.mpr ?_)
    have hnonneg : 0 ≤ (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) := by positivity
    linarith only [hMatrixBudget, hnonneg]
  exact member.relativePatchSliceConclusion_of_numerical_retained_forecast_score
    setup qnum o bW hb e cutoff hcutoff hsmall
    (fun j => (prep j).poly) (fun j => (hprep j).2.1)
    w hw hws hmono Pscalar hP (fun i => (e i).1.val + 1) Bpatch χ M K hM hweight
    hcoords hcol hdiv f hf hlam hδ haccuracy hε hdiscount hscore
    hbudget hr hE hDmodBudget (Real.exp_le_exp.mpr hMatrixBudget)
    hχbudget hBbudget hcapLog hPnative hqBudget hscoreLower hlarge hrank

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

private theorem eight_le_exp_four : (8 : ℝ) ≤ Real.exp 4 := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase 4
  have heq : (Real.exp (1 : ℝ)) ^ 4 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [heq] at hpow
  norm_num at hpow
  linarith only [hpow]

theorem majorPhasePlateauKernel_lip_le_of_prepared_matrix_budget
    {m q : ℕ} {p qLog budget : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (hqLog : (q : ℝ) ≤ Real.exp qLog)
    (hbudget : qLog + (p + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (d : ℕ) : ((majorPhasePlateauKernel d).lip : ℝ) ≤ Real.exp budget := by
  have hqone : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
  have hqLog0 : 0 ≤ qLog := Real.one_le_exp_iff.mp (hqone.trans hqLog)
  have hexponent : 2 ≤ preparedIntegralBasisExponent m + 1 := by
    unfold preparedIntegralBasisExponent
    omega
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith only [hp]
  have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ (preparedIntegralBasisExponent m + 1) :=
    pow_le_pow_right₀ hbase hexponent
  have hfour : (4 : ℝ) ≤ budget := by
    have hsquare : (4 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith only [hp, sq_nonneg p]
    linarith only [hsquare, hpow, hqLog0, hbudget]
  simpa only [majorPhasePlateauKernel_lip, NNReal.coe_ofNat] using
    eight_le_exp_four.trans (Real.exp_le_exp.mpr hfour)

namespace PolynomialPatch

theorem ofTaggedWeightedShearOrbit_kernel_lip_le_exp
    {Y X : Type*} {m n s d : ℕ} {J : Fin m → Type*}
    (patch : PolynomialPatch Y s d) (e : Fin n ≃ Sigma J)
    (ambient : (polynomialShearFiltration patch.weight s patch.weight_le).realification.PolynomialOrbit
      (VectorPolynomial.fullTaggedVariableWeight (X := X) J))
    {cost budget : ℝ} (hcost : relativePatchComplexity patch ≤ cost) (hbudget : cost ≤ budget) :
    ((patch.ofTaggedWeightedShearOrbit e ambient).kernel.lip : ℝ) ≤ Real.exp budget := by
  have h := relativePatchComplexity_kernel_bound patch hcost
  exact (show (patch.kernel.lip : ℝ) ≤ Real.exp cost by linarith only [h]).trans
    (Real.exp_le_exp.mpr hbudget)

end PolynomialPatch
end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal Matrix

variable {X J₀ : Type} [Fintype X] [DecidableEq X]
variable {m : ℕ} (prep : RankPreparationFamily X J₀ m)
variable {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics setup)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) setup qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)

theorem relativePatchSliceConclusion_of_prepared_shear_score
    {preparationP qLog : ℝ} {Rprep : ℕ}
    (hprep : prep.PreparedHeights preparationP Rprep)
    (hp : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (hqLog : (member.slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp qLog)
    {degree d₀ old removed returned : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : returned ≤ d₀ + degree * (old - removed))
    {Y : Type*} (patch : PolynomialPatch Y degree returned)
    (ambient : (polynomialShearFiltration patch.weight degree patch.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) (fun j : Fin m => (prep j).Coord)))
    {patchCost : ℝ} (hPatchCost : relativePatchComplexity patch ≤ patchCost)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected setup.hBactive o bW hb
        (fun j => (prep j).poly) (fun j => (hprep j).2.1) setup.κ x.val).re *
        bufferedScalarScore (majorPhasePlateauKernel tagCount)
          (fullTaggedBufferedCoordinates e (fun j => (prep j).poly)
            (fun j => (member.slice.path.center j).val))
          (fun u β => (patch.ofTaggedWeightedShearOrbit e ambient).value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : qLog + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : patchCost ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ)) :
    RelativePatchSliceConclusion degree physicalN f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  have hχ := majorPhasePlateauKernel_lip_le_of_prepared_matrix_budget hp
    (member.slice.path.referenceRetainedCRTModulus_pos cutoff) hqLog hMatrixBudget tagCount
  have hB := patch.ofTaggedWeightedShearOrbit_kernel_lip_le_exp e ambient
    hPatchCost hPatchCostBudget
  exact member.relativePatchSliceConclusion_of_prepared_determining_score
    prep setup qnum o bW hb e hprep hp hRprep hcoord hbW
    cutoff hcutoff hsmall hqLog hm hprepared hremoved hreturned
    (patch.ofTaggedWeightedShearOrbit e ambient) (majorPhasePlateauKernel tagCount)
    f hf hlam hδ haccuracy hε hdiscount hscore hbudget hRankBudget hDmodBudget
    hMatrixBudget hχ hB hcapLog hPnative hscoreLower hlarge

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI
