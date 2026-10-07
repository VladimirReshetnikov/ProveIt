import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFiniteFreezingDictionaryProducer

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace Refinement
variable {P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

noncomputable def mono {cost' mass' score' : ℝ}
    (hcost : newCost ≤ cost') (hmass : mass' ≤ newMass) (hscore : score' ≤ newScore) :
    P.Refinement cost' mass' score' where
  retained := refinement.retained
  subset := refinement.subset
  mass := hmass.trans refinement.mass
  cost_le := refinement.cost_le.trans hcost
  step := refinement.step
  step_pos := refinement.step_pos
  slice := refinement.slice
  dense z := (refinement.dense z).mono hcost
  inside := refinement.inside
  scoreLower z := hscore.trans (refinement.scoreLower z)

noncomputable def massBudget {initialMass Bcap : ℝ}
    (hmass : 0 ≤ initialMass)
    {Index : Type*} [Fintype Index] [Nonempty Index]
    (hcount : (Fintype.card Index : ℝ) ≤ Bcap ^ 2)
    (hbudget : newMass = initialMass / (Fintype.card Index : ℝ)) :
    P.Refinement newCost (initialMass / Bcap ^ 2) newScore :=
  refinement.mono le_rfl (by
    rw [hbudget]
    exact div_le_div_of_nonneg_left hmass (by exact_mod_cast Fintype.card_pos) hcount) le_rfl

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def budgetRefinement {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) : P.Refinement cost' mass' score' where
  retained := P.productive
  subset := fun _ hz => hz
  mass := hmass.trans P.mass
  cost_le := hcost
  step z := (P.chart z).step
  step_pos z := (P.chart z).step_pos
  slice z := (P.chart z).slice
  dense z := (P.chart z).dense.mono hcost
  inside _ := Finset.Subset.refl _
  scoreLower z := hscore.trans (P.score z)

@[simp] theorem budgetRefinement_productive {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) :
    (P.budgetRefinement hcost hmass hscore).problem.productive = P.productive := rfl

@[simp] theorem budgetRefinement_chartValues {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) (z : P.productive)
    (u : (P.chart z).Variables → ℤ) :
    ((P.budgetRefinement hcost hmass hscore).problem.chart z).chartValues u =
      (P.chart z).chartValues u := rfl

@[simp] theorem budgetRefinement_physical {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) (z : P.productive)
    (u : (P.chart z).Variables → ℤ) :
    ((P.budgetRefinement hcost hmass hscore).problem.chart z).physical u =
      (P.chart z).physical u := rfl

@[simp] theorem budgetRefinement_candidate_orbit {cost' mass' score' : ℝ}
    (hcost : cost ≤ cost') (hmass : mass' ≤ massThreshold)
    (hscore : score' ≤ scoreThreshold) (z : P.productive) :
    ((P.budgetRefinement hcost hmass hscore).problem.candidate z).orbit =
      (P.candidate z).orbit := rfl

namespace Conclusion

variable {P} {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore)

noncomputable def mono {cost' mass' score' : ℝ}
    (hcost : outputCost ≤ cost') (hmass : mass' ≤ outputMass)
    (hscore : score' ≤ outputScore) : P.Conclusion cost' mass' score' where
  ambient := out.ambient
  marked := out.marked
  retained := out.retained
  subset := out.subset
  mass := hmass.trans out.mass
  step := out.step
  step_pos := out.step_pos
  slice := out.slice
  dense z := (out.dense z).mono hcost
  inside := out.inside
  score z := hscore.trans (out.score z)

@[simp] theorem mono_ambient {cost' mass' score' : ℝ}
    (hcost : outputCost ≤ cost') (hmass : mass' ≤ outputMass)
    (hscore : score' ≤ outputScore) :
    (out.mono hcost hmass hscore).ambient = out.ambient := rfl

@[simp] theorem mono_retained {cost' mass' score' : ℝ}
    (hcost : outputCost ≤ cost') (hmass : mass' ≤ outputMass)
    (hscore : score' ≤ outputScore) :
    (out.mono hcost hmass hscore).retained = out.retained := rfl

@[simp] theorem mono_slice {cost' mass' score' : ℝ}
    (hcost : outputCost ≤ cost') (hmass : mass' ≤ outputMass)
    (hscore : score' ≤ outputScore) (z : out.retained) :
    (out.mono hcost hmass hscore).slice z = out.slice z := rfl

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_cost_le_uniform
    {cost densityCost budget θ : ℝ} {modulus Q k : ℕ}
    (hθ : 0 < θ) (hmodulus : 0 < modulus) (hQpos : 0 < Q)
    (hmodulusBound : (modulus : ℝ) ≤ budget) (hQbound : (Q : ℝ) ≤ max 1 budget) :
    max cost (densityCost + Real.log ((4 * modulus * Q * (k + 1 : ℝ)) / θ)) ≤
      max cost (densityCost + Real.log ((4 * budget * max 1 budget * (k + 1 : ℝ)) / θ)) := by
  apply max_le_max le_rfl
  apply add_le_add le_rfl
  apply Real.log_le_log
  · have hm : (0 : ℝ) < modulus := Nat.cast_pos.mpr hmodulus
    have hQ : (0 : ℝ) < Q := Nat.cast_pos.mpr hQpos
    positivity
  · apply div_le_div_of_nonneg_right _ hθ.le
    apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ k + 1)
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hmodulusBound (by norm_num)) hQbound
      (Nat.cast_nonneg _) (mul_nonneg (by norm_num) ((Nat.cast_nonneg _).trans hmodulusBound))

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

namespace Refinement
variable {A Fmark φ P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

theorem refilteredFrozenScore_mono {cost' mass' : ℝ}
    (hcost : newCost ≤ cost') (hmass : mass' ≤ newMass)
    (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : refinement.retained) :
    (refinement.mono hcost hmass le_rfl).problem.refilteredFrozenScore
      A Fmark φ hφ W Dref Fref left right markedMiddle
      ((refinement.mono hcost hmass le_rfl).refilteredMiddle
        hφ W Dref Fref markedMiddle middle) z =
    refinement.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle
      (refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := rfl

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_exp_densityLoss (k : ℕ) {b t : ℝ} (hb : 0 ≤ b) :
    Real.log ((4 * Real.exp b * max 1 (Real.exp b) * (k + 1 : ℝ)) / Real.exp (-t)) =
      Real.log 4 + 2 * b + Real.log (k + 1 : ℝ) + t := by
  rw [max_eq_right (Real.one_le_exp_iff.mpr hb),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity : (4 * Real.exp b * Real.exp b : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by positivity : (4 * Real.exp b : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity),
    Real.log_exp, Real.log_exp]
  ring

theorem finiteFreezing_exp_cost_le (k : ℕ) {cost densityCost p b t : ℝ}
    (hcost : cost ≤ p) (hdensity : densityCost ≤ p) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    max cost (densityCost + Real.log
      ((4 * Real.exp b * max 1 (Real.exp b) * (k + 1 : ℝ)) / Real.exp (-t))) ≤
      p + Real.log 4 + 2 * b + Real.log (k + 1 : ℝ) + t := by
  rw [finiteFreezing_exp_densityLoss k hb]
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hk : 0 ≤ Real.log (k + 1 : ℝ) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg k))
  apply max_le <;> linarith

theorem finiteFreezing_exp_cost_le_of_card_bound (k : ℕ) {cost densityCost p b t κ : ℝ}
    (hcost : cost ≤ p) (hdensity : densityCost ≤ p) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hcard : (k + 1 : ℝ) ≤ Real.exp κ) :
    max cost (densityCost + Real.log
      ((4 * Real.exp b * max 1 (Real.exp b) * (k + 1 : ℝ)) / Real.exp (-t))) ≤
      p + Real.log 4 + 2 * b + κ + t := by
  have hk : Real.log (k + 1 : ℝ) ≤ κ := by
    calc
      _ ≤ Real.log (Real.exp κ) := Real.log_le_log (by positivity) hcard
      _ = κ := Real.log_exp κ
  exact (finiteFreezing_exp_cost_le k hcost hdensity hb ht).trans (by linarith)

theorem finiteFreezing_exp_mass (a b : ℝ) :
    Real.exp (-a) / (Real.exp b) ^ 2 = Real.exp (-(a + 2 * b)) := by
  rw [pow_two, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

theorem finiteFreezing_exp_mass_le {mass a b : ℝ} (hmass : Real.exp (-a) ≤ mass) :
    Real.exp (-(a + 2 * b)) ≤ mass / (Real.exp b) ^ 2 := by
  rw [← finiteFreezing_exp_mass]
  exact div_le_div_of_nonneg_right hmass (by positivity)

theorem finiteFreezing_exp_recursive_mass_le {mass a b pRec : ℝ}
    (hmass : Real.exp (-a) ≤ mass) (hpRec : a + 2 * b ≤ pRec) :
    Real.exp (-pRec) ≤ mass / (Real.exp b) ^ 2 := by
  exact (Real.exp_le_exp.mpr (neg_le_neg hpRec)).trans
    (finiteFreezing_exp_mass_le hmass)

theorem finiteFreezing_exp_recursive_score_le {score q pRec : ℝ}
    (hscore : Real.exp (-q) ≤ score) (hpRec : q ≤ pRec) :
    Real.exp (-pRec) ≤ score := by
  exact (Real.exp_le_exp.mpr (neg_le_neg hpRec)).trans hscore

theorem finiteFreezing_exp_recursive_budget (k : ℕ)
    {cost densityCost mass score p b t a q pRec : ℝ}
    (hcost : cost ≤ p) (hdensity : densityCost ≤ p) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hmass : Real.exp (-a) ≤ mass) (hscore : Real.exp (-q) ≤ score)
    (hcostRec : p + Real.log 4 + 2 * b + Real.log (k + 1 : ℝ) + t ≤ pRec)
    (hmassRec : a + 2 * b ≤ pRec) (hscoreRec : q ≤ pRec) :
    max cost (densityCost + Real.log
      ((4 * Real.exp b * max 1 (Real.exp b) * (k + 1 : ℝ)) / Real.exp (-t))) ≤ pRec ∧
      Real.exp (-pRec) ≤ mass / (Real.exp b) ^ 2 ∧
      Real.exp (-pRec) ≤ score := by
  exact ⟨(finiteFreezing_exp_cost_le k hcost hdensity hb ht).trans hcostRec,
    finiteFreezing_exp_recursive_mass_le hmass hmassRec,
    finiteFreezing_exp_recursive_score_le hscore hscoreRec⟩

end Erdos3.VectorPolynomial

end

end OAI
