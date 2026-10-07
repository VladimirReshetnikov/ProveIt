/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.CandidateCommonFastBudgetMonotonicity
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
import OAI.Combinatorics.Progressions.Estimates.NativeOptionPivotQuotientStrong
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget

namespace OAI

universe u

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_nativeOptionPair_weighted_common_orbit_factors (s : ℕ) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧
    ∀ {J α σ Ω : Type*} [Fintype J] [Fintype α] [Fintype σ] [Fintype Ω]
      {β : J → Type*} [∀ j, Fintype (β j)]
      {L : Type u} {M : J → Type u}
      [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
      {d₀ : ℕ} {d : J → ℕ}
      (D : RationalFilteredNilmanifold L s d₀)
      (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
      (e : Basis α ℚ (∀ i : Option J, optionLieSpace L M i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i}))
      (b : ∀ j, Basis (β j) ℚ (PairAlgebra L (M j))) (ν : ∀ j, β j → ℕ)
      (hG : ∀ j k, (pi (pairModels D (E j))).filtration.layer k =
        Submodule.span ℚ (b j '' {i | k ≤ ν j i}))
      {height : ℕ}, 1 ≤ height →
      (∀ j i k, RationalHeightLE ((b j).repr (optionPairProjection j (e k)) i) height) →
    ∀ {p : ℝ}, 0 ≤ p → (Fintype.card α : ℝ) ≤ p →
      (∀ j, (Fintype.card (β j) : ℝ) ≤ p) →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (height : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ p) →
      let P := p + (p + C) ^ C
      ∀ side : σ → ℝ, (∀ i, Real.exp ((P + 2) ^ A) ≤ side i) →
      ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      ∀ (g : Ω → ∀ i : Option J,
          (optionFactors D E i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (η : J → L →ₗ[ℚ] ℚ) (θ : ∀ j, M j →ₗ[ℚ] ℚ),
        (∀ a ∈ H, ∀ j,
          (pi (pairModels D (E j))).filtration.ControlledSymbolFactorization
            (b j) (ν j) (hG j) (pairFrequency (η j) (θ j)) side
            (pairOrbitSymbol D (E j) (g a none) (g a (some j)) (b j) (ν j) (hG j)) p) →
        let q := (P + 2) ^ A + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
        ∃ (W : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
          (v : Fin (Fintype.card α) → (optionProduct D E).filtration.AssociatedGraded)
          (m : ℕ) (H' : Finset Ω),
          H' ⊆ H ∧ 0 < outer.mass H' ∧
          Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
          Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
          BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e ω hF)
            ω W.toSubmodule ∧
          (∀ i k, rationalLogHeight
            (((optionProduct D E).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
          (∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer W s →
            realifyFunctional ((pairFrequency (η j) (θ j)).comp
              (optionPairProjection j).toLinearMap) x = 0) ∧
          0 < m ∧ (m : ℝ) ≤ Real.exp q ∧
          ∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
            e ω hF side q m W
            ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
              (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩ := by
  obtain ⟨C, hC, hbudget⟩ := exists_controlledProjectionUniformBudget_power s
  obtain ⟨A, hA, hcommon⟩ := exists_weighted_common_refiltered_orbit_factors s
  refine ⟨C, A, hC, hA, ?_⟩
  intro J α σ Ω _ _ _ _ β _ L M _ _ _ _ d₀ d D E e ω hF b ν hG
    height hheight hentries p hp hα hβ hσ hJ hheightp hstructure P side hside
    outer H hH g η θ hfactor
  have hpP : p ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_right (by positivity)
  have hliftP : (p + C) ^ C ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_left hp
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  apply hcommon (optionProduct D E).filtration e ω hF
    (fun j => (pairFrequency (η j) (θ j)).comp (optionPairProjection j).toLinearMap)
    (hp.trans hpP) (hα.trans hpP) (hσ.trans hpP) (hJ.trans hpP)
    (fun i j k => (hstructure i j k).trans hpP) side hside outer H hH
    (fun a => ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
      (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩)
  intro a ha j
  obtain ⟨U, hU⟩ := (hfactor a ha j).exists_fastWitness
    (pi (pairModels D (E j))).filtration (b j) (ν j) (hG j)
  have hpull := (optionProduct D E).filtration.controlledSymbolFactorizationAtFast_projection_of_dimensions
    e ω hF (pi (pairModels D (E j))).filtration (b j) (ν j) (hG j)
    (optionPairProjection j) (optionPairProjection_layers D E j)
    (optionPairProjection_layer_surjective D E j) hheight (hentries j)
    hp hα (hβ j) hσ hheightp side hsidepos
    ((optionProduct D E).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
      ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
        (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩)
    (pairFrequency (η j) (θ j)) U
    (by rw [optionPairProjection_jointOrbitSymbol D E j e ω hF (b j) (ν j) (hG j)]; exact hU)
  obtain ⟨m, E₀, P₀, R₀, v₀, hdata⟩ := hpull.mono
    (optionProduct D E).filtration e ω hF ((hbudget p hp).trans hliftP) hsidepos
  exact ⟨m, E₀, P₀, R₀, _, v₀, hdata⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct Classical

def allocatedFrozenTaggedPairBudget (s C A : ℕ) (pGeo p : ℝ) : ℝ :=
  (fixedAdaptedSymbolTransferInput pGeo
    (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A

def allocatedFrozenTaggedFamilyInputBudget (b t : ℝ) : ℝ :=
  b + t + (b + 3) ^ 4 + 1

theorem exists_allocatedFrozenTaggedFamily_common_factors (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A K T : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {Pivot α Ω : Type*} [Fintype Pivot] [Fintype α] [Fintype Ω]
      {LG : Type u} {MG : Pivot → Type u}
      [LieRing LG] [LieAlgebra ℚ LG] [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
      {d₀ : ℕ} {d : Pivot → ℕ}
      (D : RationalFilteredNilmanifold LG s d₀)
      (E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j))
      {pGeo p bnd : ℝ}, 0 ≤ pGeo → 0 ≤ p → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (E j))).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C A pGeo p
      let r := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := r + (r + K) ^ K
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
      {I Jgeo : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (Jgeo j)]
      {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
      (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := Jgeo) B)
      (Deck : Fin m → Type*) (keep : LayerSamplerVariables G I n B → Prop)
      [Nonempty {i // keep i}], (Fintype.card {i // keep i} : ℝ) ≤ bnd →
      (∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (Γ.sides keep i : ℝ)) →
      (∀ i, Real.exp ((P + 2) ^ T) ≤ (Γ.sides keep i : ℝ)) →
    ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
    ∀ (g : Ω → ∀ i : Option Pivot,
        (optionFactors D E i).filtration.realification.PolynomialOrbit
          (fun _ : {i // keep i} => 1))
      (eta : Pivot → LG →ₗ[ℚ] ℚ) (theta : ∀ j, MG j →ₗ[ℚ] ℚ)
      (input : ∀ _a : {a // a ∈ H}, ∀ j,
        AllocatedFrozenTaggedPairInput Γ Deck keep D (E j) p),
      (∀ a j
        (c : Basis (Fin (finrank ℚ (PairAlgebra LG (MG j)))) ℚ (PairAlgebra LG (MG j)))
        (w : Fin (finrank ℚ (PairAlgebra LG (MG j))) → ℕ)
        (hc : ∀ k, (pi (pairModels D (E j))).filtration.layer k =
          Submodule.span ℚ (c '' {i | k ≤ w i})),
        pairOrbitSymbol D (E j) (input a j).V.orbit (input a j).W.orbit c w hc =
          pairOrbitSymbol D (E j) (g a.val none) (g a.val (some j)) c w hc) →
      (∀ a j, (input a j).η = eta j) →
      (∀ a j, (input a j).θ = theta j) →
      let q := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      ∃ (W : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
        (v : Fin (Fintype.card α) → (optionProduct D E).filtration.AssociatedGraded)
        (den : ℕ) (H' : Finset Ω),
        H' ⊆ H ∧ 0 < outer.mass H' ∧
        Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e ω hF)
          ω W.toSubmodule ∧
        (∀ i k, rationalLogHeight
          (((optionProduct D E).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
        (∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer W s →
          realifyFunctional ((pairFrequency (eta j) (theta j)).comp
            (optionPairProjection j).toLinearMap) x = 0) ∧
        0 < den ∧ (den : ℝ) ≤ Real.exp q ∧
        ∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
          e ω hF (fun i => (Γ.sides keep i : ℝ)) q den W
          ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
            (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩ := by
  obtain ⟨C, A, hC, hA, hstep⟩ := exists_allocatedFrozenTaggedPairInput_fixed_basis_step_drop s hs
  obtain ⟨K, T, hK, hT, hcommon⟩ := exists_nativeOptionPair_weighted_common_orbit_factors s
  refine ⟨C, A, K, T, hC, hA, hK, hT, ?_⟩
  intro Pivot α Ω _ _ _ LG MG _ _ _ _ _ _ _ _ _ _ _ _ d₀ d D E
    pGeo p bnd hpGeo hp hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he
    localCost r P m G X _ _ I Jgeo _ _ n B _ Γ Deck keep _ hkeep hlong hcommonLong
    outer H hH g eta theta input hsymbol heta htheta
  classical
  choose b ν hG _hforward hinverse hlocal using fun j => hstep D (E j) hpGeo (hGeo j)
  have hcost : 0 ≤ localCost := by
    dsimp [localCost, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput]
    positivity
  have hbndR : bnd ≤ r := by
    dsimp [r, allocatedFrozenTaggedFamilyInputBudget]
    linarith [pow_nonneg (show 0 ≤ bnd + 3 by linarith) 4]
  have hcostR : localCost ≤ r := by
    dsimp [r, allocatedFrozenTaggedFamilyInputBudget]
    linarith [pow_nonneg (show 0 ≤ bnd + 3 by linarith) 4]
  have hheightR : (bnd + 3) ^ 4 + 1 ≤ r := by
    dsimp [r, allocatedFrozenTaggedFamilyInputBudget]
    linarith
  have hdim (j) : (Fintype.card (Σ i : Bool, Fin (Bool.rec (d j) d₀ i)) : ℝ) ≤ bnd :=
    (hGeo j).1.trans hpGeoB
  have hβ (j) : (Fintype.card (Fin (finrank ℚ (PairAlgebra LG (MG j)))) : ℝ) ≤ bnd := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis (pi (pairModels D (E j))).basis]
      using hdim j
  have hentries (j i k) : RationalHeightLE
      ((b j).repr (optionPairProjection j (e k)) i) ⌈Real.exp ((bnd + 3) ^ 4)⌉₊ :=
    rationalHeightLE_ceil_exp (optionPairProjection_adapted_logHeight D E j e (b j)
      hbnd (hdim j) he (fun i k => (hinverse j i k).trans hInvB) k i)
  have hheight : (⌈Real.exp ((bnd + 3) ^ 4)⌉₊ : ℝ) ≤ Real.exp r :=
    (ceil_exp_le_exp_add_one (by positivity)).trans (Real.exp_le_exp.mpr hheightR)
  have hsidepos (i) : 0 < (Γ.sides keep i : ℝ) := (Real.exp_pos _).trans_le (hlong i)
  apply hcommon D E e ω hF b ν hG (one_le_ceil_exp _) hentries
    (hbnd.trans hbndR) (hα.trans hbndR) (fun j => (hβ j).trans hbndR)
    (hkeep.trans hbndR) (hPivot.trans hbndR) hheight
    (fun i j k => (hstructure i j k).trans hbndR)
    (fun i => (Γ.sides keep i : ℝ)) hcommonLong outer H hH g eta theta
  intro a ha j
  have hfactor := hlocal j B Γ Deck keep (input ⟨a, ha⟩ j) hlong
  have hfactor' : (pi (pairModels D (E j))).filtration.ControlledSymbolFactorization
      (b j) (ν j) (hG j) (pairFrequency (eta j) (theta j))
      (fun i => (Γ.sides keep i : ℝ))
      (pairOrbitSymbol D (E j) (g a none) (g a (some j)) (b j) (ν j) (hG j)) localCost := by
    simpa only [heta, htheta, hsymbol, allocatedFrozenTaggedPairBudget, localCost]
      using hfactor
  exact hfactor'.mono (pi (pairModels D (E j))).filtration (b j) (ν j) (hG j)
    hcostR hsidepos

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem centralActionBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    centralActionBudget p ≤ centralActionBudget q := by
  unfold centralActionBudget
  gcongr

theorem verticalDecompositionBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    verticalDecompositionBudget p ≤ verticalDecompositionBudget q := by
  have hc0 := centralActionBudget_nonneg hp
  have hc := centralActionBudget_mono hp hpq
  have hcq0 := hc0.trans hc
  dsimp only [verticalDecompositionBudget]
  gcongr

namespace VectorPolynomial

open RationalFilteredNilmanifold

theorem spatialNativeVerticalParameter_le {p pNative pLocal r : ℝ}
    (hp : 0 ≤ p) (hNative : pNative ≤ p) (hLocal : pLocal ≤ p) (hr : r ≤ p) :
    spatialNativeVerticalParameter pNative pLocal r ≤ 3 * p + 1 := by
  have hmax : max pNative 0 ≤ p := max_le hNative hp
  unfold spatialNativeVerticalParameter
  linarith only [hmax, hLocal, hr]

theorem spatialNativeFactorParameter_le {p pFamily pNative pLocal r : ℝ}
    (hp : 0 ≤ p) (hFamily : pFamily ≤ p) (hNative : pNative ≤ p)
    (hLocal0 : 0 ≤ pLocal) (hLocal : pLocal ≤ p) (hr0 : 0 ≤ r) (hr : r ≤ p) :
    spatialNativeFactorParameter pFamily pNative pLocal r ≤
      2 * p + verticalDecompositionBudget (3 * p + 1) + 2 := by
  have hvertical0 := (spatialNativeVerticalFactorBounds pFamily pNative pLocal r
    hLocal0 hr0).1
  have hvertical := spatialNativeVerticalParameter_le hp hNative hLocal hr
  have hdecomp := verticalDecompositionBudget_mono hvertical0 hvertical
  have hdecomp0 := verticalDecompositionBudget_nonneg (by positivity : 0 ≤ 3 * p + 1)
  apply max_le
  · linarith only [hFamily, hp, hdecomp0]
  · linarith only [hdecomp, hr, hp]

theorem fixedAdaptedSymbolTransferInput_mono {p p' q q' : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q') :
    fixedAdaptedSymbolTransferInput p q ≤ fixedAdaptedSymbolTransferInput p' q' := by
  unfold fixedAdaptedSymbolTransferInput
  gcongr

theorem allocatedFrozenTaggedPairBudget_mono (s C A : ℕ)
    {pGeo pGeo' p p' : ℝ} (hGeo0 : 0 ≤ pGeo) (hp0 : 0 ≤ p)
    (hGeo : pGeo ≤ pGeo') (hp : p ≤ p') :
    allocatedFrozenTaggedPairBudget s C A pGeo p ≤
      allocatedFrozenTaggedPairBudget s C A pGeo' p' := by
  unfold allocatedFrozenTaggedPairBudget fixedAdaptedSymbolTransferInput
  gcongr

theorem allocatedFrozenTaggedFamilyInputBudget_mono {b b' t t' : ℝ}
    (hb : 0 ≤ b) (hbb : b ≤ b') (htt : t ≤ t') :
    allocatedFrozenTaggedFamilyInputBudget b t ≤
      allocatedFrozenTaggedFamilyInputBudget b' t' := by
  unfold allocatedFrozenTaggedFamilyInputBudget
  gcongr

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateTaggedPairFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    {H : Finset Ω}

def extendedJointOrbit
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (a : Ω) : ∀ i : Option Pivot,
      (optionFactors D E i).filtration.realification.PolynomialOrbit
        (fun _ : {i // keep i} => 1) :=
  if ha : a ∈ H then F.jointOrbit ⟨a, ha⟩ else fun _ => 1

omit [Fintype Ω] in
@[simp] theorem extendedJointOrbit_mem
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (a : Ω) (ha : a ∈ H) : F.extendedJointOrbit a = F.jointOrbit ⟨a, ha⟩ := by
  simp only [extendedJointOrbit, dite_eq_left ha]

def CommonFactors
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (outer : FiniteProbabilityWeights Ω)
    {α : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D E).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i})) (q : ℝ) : Prop :=
  ∃ (W : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
    (v : Fin (Fintype.card α) → (optionProduct D E).filtration.AssociatedGraded)
    (den : ℕ) (H' : Finset Ω),
    H' ⊆ H ∧ 0 < outer.mass H' ∧
    Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e ω hF)
      ω W.toSubmodule ∧
    (∀ i k, rationalLogHeight
      (((optionProduct D E).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
    (∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional ((pairFrequency (F.η j) (F.θ j)).comp
        (optionPairProjection j).toLinearMap) x = 0) ∧
    0 < den ∧ (den : ℝ) ≤ Real.exp q ∧
    ∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
      e ω hF (fun i : {i // keep i} => (A.sides i.val : ℝ)) q den W
      ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration)
          (F.extendedJointOrbit a)).log,
        (piRealOrbit (fun i => (optionFactors D E i).filtration)
          (F.extendedJointOrbit a)).property⟩⟩

theorem exists_common_factors (hs : 1 ≤ s) :
    ∃ C Cbasis K T : ℕ, 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {α : Type*} [Fintype α] {pGeo bnd : ℝ},
      0 ≤ pGeo → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (E j))).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let r := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := r + (r + K) ^ K
    ∀ (outer : FiniteProbabilityWeights Ω), 0 < outer.mass H →
    ∀ (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
      [Nonempty {i // keep i}], (Fintype.card {i // keep i} : ℝ) ≤ bnd →
      (∀ i : {i // keep i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keep i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let q := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      F.CommonFactors outer e ω hF q := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedFrozenTaggedFamily_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF
    hstructure he localCost r P outer hH F _ hkeep hlong hcommonLong
  have hresult := hcommon D E hpGeo F.hp hbnd hGeo hpGeoB hInvB hα hPivot
    e ω hF hstructure he B F.context Deck keep hkeep
    (by simpa only [F.context_sides] using hlong)
    (by simpa only [F.context_sides] using hcommonLong)
    outer H hH F.extendedJointOrbit F.η F.θ F.input
    (fun a j c w hc => by
      simpa only [F.extendedJointOrbit_mem a.val a.property] using F.pair_symbol a j c w hc)
    (fun a j => F.input_η a j) (fun a j => F.input_θ a j)
  simpa only [CommonFactors, F.context_sides] using hresult

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def candidateFrontFactorScalarConclusion (s : ℕ)
    (p actualGeometry cost terminal commonInput fast longThreshold
      aProjected aCommon aMarkInput common aAdapted aMarkBudget aJointGeo initialShort : ℝ) : Prop :=
  terminal ∈ Set.Icc 0 commonInput ∧
    allocatedCandidateCommonFastBudget s terminal ≤ fast ∧
    max cost initialShort ≤ longThreshold ∧
    (aProjected + 2) ^ 3 + aCommon ≤ commonInput ∧
    aMarkInput ∈ Set.Icc 0 commonInput ∧
    aCommon ∈ Set.Icc 0 common ∧
    p ≤ commonInput ∧ actualGeometry ≤ commonInput ∧
    aAdapted ≤ commonInput ∧ aMarkBudget ≤ commonInput ∧
    aJointGeo ≤ commonInput ∧ (aProjected + 2) ^ 4 ≤ commonInput ∧ cost ≤ commonInput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateTaggedPairFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    {H : Finset Ω}

def longJointOrbit
    {Λ : Type*}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Λ Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop) (a : Λ) :
    ∀ i : Option Pivot, (optionFactors D E i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keepLong i} => 1) :=
  fun i => (optionFactors D E i).filtration.polynomialOrbitRealChart
    (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
    ((F.chart a).axisPolynomial keepLong (fun _ => 0))
    ((F.chart a).axisPolynomial_support keepLong (fun _ => 0)) (F.jointOrbit a i)

def extendedLongJointOrbit
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop) (a : Ω) :
    ∀ i : Option Pivot, (optionFactors D E i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keepLong i} => 1) :=
  if ha : a ∈ H then F.longJointOrbit keepLong ⟨a, ha⟩ else fun _ => 1

omit [Fintype Ω] in
@[simp] theorem extendedLongJointOrbit_mem
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop) (a : Ω) (ha : a ∈ H) :
    F.extendedLongJointOrbit keepLong a = F.longJointOrbit keepLong ⟨a, ha⟩ := by
  simp only [extendedLongJointOrbit, dite_eq_left ha]

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateTaggedPairFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    {H : Finset Ω}

variable
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)

def extendedJointPolynomialOrbit (a : Ω) :
    ((optionProduct D E).filtration.realification.adaptedPolynomialFiltration
      (fun _ : {i // keep i} => 1)).Group :=
  ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration)
      (F.extendedJointOrbit a)).log,
    (piRealOrbit (fun i => (optionFactors D E i).filtration)
      (F.extendedJointOrbit a)).property⟩⟩

variable (outer : FiniteProbabilityWeights Ω) (js : List Pivot)
    {α κ : Type*} [Fintype α] [Fintype κ]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D E).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))

abbrev quotientFiltration := D.filtration.pivotProductQuotientFiltration φ F.η js
  (NilpotentLieFiltration.pi (fun j => (E j).filtration))

variable
    (c : Basis κ ℚ ((LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) × (∀ j, MG j)))
    (ν : κ → ℕ)
    (hQ : ∀ k, (F.quotientFiltration js).layer k = Submodule.span ℚ (c '' {i | k ≤ ν i}))

def QuotientFactors (q pProj : ℝ) : Prop :=
  ∃ (W : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
    (v : Fin (Fintype.card α) → (optionProduct D E).filtration.AssociatedGraded)
    (V : LieSubalgebra ℚ (F.quotientFiltration js).AssociatedGraded) (den denQ : ℕ) (H' : Finset Ω),
    H' ⊆ H ∧ 0 < outer.mass H' ∧
    Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e ω hF)
      ω W.toSubmodule ∧
    (∀ i k, rationalLogHeight
      (((optionProduct D E).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
    0 < den ∧ (den : ℝ) ≤ Real.exp q ∧
    (∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
      e ω hF (fun i : {i // keep i} => (A.sides i.val : ℝ)) q den W
      (F.extendedJointPolynomialOrbit a)) ∧
    V = optionCommonPivotQuotientFast D E φ F.η js W ∧
    0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
    (∀ a ∈ H', ∃ El Pl Rl :
      (F.quotientFiltration js).RealPolynomialSymbolGroup (fun _ : {i // keep i} => 1),
      El * Pl * Rl = (F.quotientFiltration js).realPolynomialSymbolHom c ν hQ (fun _ => 1)
        ((optionProduct D E).filtration.realPolynomialGroupMap (F.quotientFiltration js)
          (optionPivotProductQuotientMap D φ F.η js)
          (optionPivotProductQuotientMap_mem_layer D E φ F.η js)
          (fun _ => 1) (F.extendedJointPolynomialOrbit a)) ∧
      Pl.coord ∈ realificationLieSubalgebra
        ((F.quotientFiltration js).symbolPointwiseSubalgebra c ν hQ (fun _ => 1) V) ∧
      (F.quotientFiltration js).SymbolSlowBound c ν hQ (fun _ => 1)
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) (Real.exp ((pProj + 2) ^ 3 + q)) El ∧
      (F.quotientFiltration js).SymbolRationalGrid c ν hQ (fun _ => 1) denQ Rl) ∧
    BasisGradedSubmodule ((F.quotientFiltration js).associatedGradedBasis c ν hQ) ν V.toSubmodule ∧
    (∀ x ∈ (F.quotientFiltration js).gradedRefiltrationLayer V s,
      D.filtration.pivotProductMarkedMap φ F.η js x = 0 → x = 0) ∧
    (∀ (Gmark : NilpotentLieFiltration (LM × (∀ j, MG j)) s)
      (hmarked : ∀ k, ∀ x ∈ (F.quotientFiltration js).layer k,
        D.filtration.pivotProductMarkedMap φ F.η js x ∈ Gmark.layer k),
      ∀ a ∈ V, basisGradeProjection ((F.quotientFiltration js).associatedGradedBasis c ν hQ) ν s a = a →
        (F.quotientFiltration js).associatedGradedMap Gmark (D.filtration.pivotProductMarkedMap φ F.η js)
          hmarked a = 0 → a = 0)

theorem CommonFactors.toQuotientFactors
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν)]
    {q pProj : ℝ} (hcommon : F.CommonFactors outer e ω hF q)
    {height : ℕ} (hheight : 1 ≤ height)
    (hentries : ∀ i j,
      RationalHeightLE (c.repr (optionPivotProductQuotientMap D φ F.η js (e j)) i) height)
    (hpProj : 0 ≤ pProj) (hqProj : q ≤ pProj)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω) : ℝ) ≤ pProj)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν) : ℝ) ≤ pProj)
    (hheightProj : (height : ℝ) ≤ Real.exp pProj) :
    F.QuotientFactors outer js e ω hF c ν hQ q pProj := by
  dsimp only [QuotientFactors, quotientFiltration]
  obtain ⟨W, v, den, H', hsub, hmass, hmassLower, hspan, hgraded, hheightW,
    hzero, hden, hdenBound, hfactor⟩ := hcommon
  have hside (i : {i // keep i}) : (0 : ℝ) < A.sides i.val :=
    Nat.cast_pos.mpr (A.sides_pos i.val)
  have hdenProj : (den : ℝ) ≤ Real.exp pProj :=
    hdenBound.trans (Real.exp_le_exp.mpr hqProj)
  obtain ⟨denQ, hdenQ, hdenQBound, hdiv, hquotient, hquotientGraded, hkernel, hgradedKernel⟩ :=
    exists_optionCommonPivotQuotient_family_symbol_factors
      D E φ F.η js e ω hF c ν hQ hheight hden hentries hpProj
      hsource htarget hheightProj hdenProj W hgraded F.θ hzero
      H' (fun i : {i // keep i} => (A.sides i.val : ℝ)) hside q
      F.extendedJointPolynomialOrbit hfactor
  refine ⟨W, v, optionCommonPivotQuotientFast D E φ F.η js W, den, denQ, H',
    hsub, hmass, hmassLower, hspan, hgraded, hheightW, hden, hdenBound, hfactor,
    rfl, hdenQ, hdenQBound, hdiv, ?_, hquotientGraded, hkernel, hgradedKernel⟩
  exact hquotient

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_allocatedExternalCandidateTaggedPairFamily_common_factors
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C Cbasis K T : ℕ, 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

    {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    {H : Finset Ω},
    ∀ {α : Type*} [Fintype α] {pGeo bnd : ℝ},
      0 ≤ pGeo → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (E j))).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let r := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := r + (r + K) ^ K
    ∀ (outer : FiniteProbabilityWeights Ω), 0 < outer.mass H →
    ∀ (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
      [Nonempty {i // keep i}], (Fintype.card {i // keep i} : ℝ) ≤ bnd →
      (∀ i : {i // keep i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keep i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let q := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      F.CommonFactors outer e ω hF q := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedFrozenTaggedFamily_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Ω Pivot _ _ LG LM MG _ _ _ _ _ _ _ _ _ _ _ _ _ _ d₀ t d D E Fmark φ marked
    keep cost p periodCap coverCap Lip H
    α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF
    hstructure he localCost r P outer hH F _ hkeep hlong hcommonLong
  have hresult := hcommon D E hpGeo F.hp hbnd hGeo hpGeoB hInvB hα hPivot
    e ω hF hstructure he B F.context Deck keep hkeep
    (by simpa only [F.context_sides] using hlong)
    (by simpa only [F.context_sides] using hcommonLong)
    outer H hH F.extendedJointOrbit F.η F.θ F.input
    (fun a j c w hc => by
      simpa only [F.extendedJointOrbit_mem a.val a.property] using F.pair_symbol a j c w hc)
    (fun a j => F.input_η a j) (fun a j => F.input_θ a j)
  simpa only [AllocatedExternalCandidateTaggedPairFamily.CommonFactors, F.context_sides] using hresult

end Erdos3.VectorPolynomial

end

end OAI
