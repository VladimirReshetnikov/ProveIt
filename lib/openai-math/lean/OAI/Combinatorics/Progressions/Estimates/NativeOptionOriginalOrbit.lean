import OAI.Combinatorics.Progressions.Polynomial.OptionMarkedPolynomialProjection
import OAI.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection

namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

instance optionRealificationTopology
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] (i : Option ι) :
    TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L i))

instance optionRealificationTopologicalAddGroup
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L i))

instance optionRealificationContinuousSMul
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L i))

instance optionRealificationT2Space
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [T2Space (ℝ ⊗[ℚ] L₀)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L i))

end Erdos3

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration
open scoped TensorProduct BigOperators

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionOriginalSpaceProjection : (optionProduct D₀ D).Space → D₀.Space :=
  productProjection (optionFactors D₀ D) none

@[simp] theorem optionOriginalSpaceProjection_mk (z : (optionProduct D₀ D).RealGroup) :
    optionOriginalSpaceProjection D₀ D (QuotientGroup.mk z) =
      QuotientGroup.mk (productProjectionHom (optionFactors D₀ D) none z) := rfl

@[simp] theorem optionOriginalSpaceProjection_piRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w)
    (x : σ → ℤ) :
    optionOriginalSpaceProjection D₀ D
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x
        (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g))) =
      QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w x (g none)) :=
  congrArg (fun z : D₀.RealGroup => (QuotientGroup.mk z : D₀.Space))
    (piRealOrbit_eval (fun i => (optionFactors D₀ D i).filtration) g x none)

noncomputable def optionOriginalObservable {P : Type*} (observable : P → D₀.Space → ℂ) :
    P → (optionProduct D₀ D).Space → ℂ :=
  fun a z => observable a (optionOriginalSpaceProjection D₀ D z)

@[simp] theorem optionOriginalObservable_apply {P : Type*}
    (observable : P → D₀.Space → ℂ) (a : P) (z : (optionProduct D₀ D).Space) :
    optionOriginalObservable D₀ D observable a z =
      observable a (optionOriginalSpaceProjection D₀ D z) := rfl

@[simp] theorem optionOriginalObservable_piRealOrbit {P σ : Type*} {w : σ → ℕ}
    (observable : P → D₀.Space → ℂ)
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w)
    (a : P) (x : σ → ℤ) :
    optionOriginalObservable D₀ D observable a
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x
        (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g))) =
      observable a (QuotientGroup.mk
        (D₀.filtration.realification.polynomialOrbitEval w x (g none))) := by
  rw [optionOriginalObservable_apply, optionOriginalSpaceProjection_piRealOrbit]

theorem optionOriginalObservable_score {P σ T : Type*} {w : σ → ℕ}
    (observable : P → D₀.Space → ℂ)
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w)
    (sites : Finset T) (physical : T → P) (point : T → σ → ℤ) (weight : T → ℂ) :
    (𝔼 t ∈ sites, weight t * optionOriginalObservable D₀ D observable (physical t)
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w (point t)
        (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g)))) =
    𝔼 t ∈ sites, weight t * observable (physical t)
      (QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w (point t) (g none))) := by
  simp only [optionOriginalObservable_piRealOrbit]

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [T2Space (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]

theorem optionOriginalSpaceProjection_lipschitz :
    letI := (optionProduct D₀ D).metricSpace
    letI := D₀.metricSpace
    LipschitzWith (coordinateLipschitzBound d₀
      (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1)
      (optionOriginalSpaceProjection D₀ D) := by
  exact productProjection_lipschitz (optionFactors D₀ D) none

end Metric

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem optionOriginalProjection_layers (k : ℕ)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i)
    (hx : x ∈ (optionProduct D₀ D).filtration.layer k) :
    liePiEval (R := ℚ) none x ∈ D₀.filtration.layer k :=
  (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k x).mp hx none

noncomputable def optionOriginalOrbit {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) :
    D₀.filtration.realification.PolynomialOrbit w :=
  (D₀.filtration.realification.polynomialOrbitCoordinates w).symm
    ((optionProduct D₀ D).filtration.realPolynomialGroupMap D₀.filtration
      (liePiEval none) (optionOriginalProjection_layers D₀ D) w
      ((optionProduct D₀ D).filtration.realification.polynomialOrbitCoordinates w g))

attribute [local irreducible] realPolynomialGroupMap

@[simp] theorem optionOriginalOrbit_log {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) :
    (optionOriginalOrbit D₀ D g).log =
      VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
        (M := optionLieSpace L₀ L) none)).toLinearMap.restrictScalars ℚ) g.log := by
  unfold optionOriginalOrbit
  rw [polynomialOrbitCoordinates_symm_log]
  exact (optionProduct D₀ D).filtration.realPolynomialGroupMap_log D₀.filtration
    (liePiEval none) (optionOriginalProjection_layers D₀ D) w
    ((optionProduct D₀ D).filtration.realification.polynomialOrbitCoordinates w g)

@[simp] theorem optionOriginalOrbit_eval {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D₀.filtration.realification.polynomialOrbitEval w x (optionOriginalOrbit D₀ D g) =
      productProjectionHom (optionFactors D₀ D) none
        ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ)) (optionOriginalOrbit D₀ D g).log =
    realificationLieHom (liePiEval none) (VectorPolynomial.eval (fun i => (x i : ℚ)) g.log)
  rw [optionOriginalOrbit_log]
  exact VectorPolynomial.eval_map _ _ _

@[simp] theorem optionOriginalOrbit_value {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    optionOriginalSpaceProjection D₀ D
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x g)) =
    QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w x
      (optionOriginalOrbit D₀ D g)) :=
  congrArg (fun z : D₀.RealGroup => (QuotientGroup.mk z : D₀.Space))
    (optionOriginalOrbit_eval D₀ D g x).symm

@[simp] theorem optionOriginalOrbit_piRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w) :
    optionOriginalOrbit D₀ D (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g) =
      g none := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (optionOriginalOrbit D₀ D (piRealOrbit
    (fun i => (optionFactors D₀ D i).filtration) g)).log = (g none).log
  exact (optionOriginalOrbit_log D₀ D
    (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g)).trans
      (piRealOrbit_project_log (fun i => (optionFactors D₀ D i).filtration) g none)

theorem optionOriginalOrbit_score {P σ T : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w)
    (observable : P → D₀.Space → ℂ)
    (sites : Finset T) (physical : T → P) (point : T → σ → ℤ) (weight : T → ℂ) :
    (𝔼 t ∈ sites, weight t * optionOriginalObservable D₀ D observable (physical t)
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w (point t) g))) =
    𝔼 t ∈ sites, weight t * observable (physical t)
      (QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w (point t)
        (optionOriginalOrbit D₀ D g))) := by
  simp only [optionOriginalObservable_apply, optionOriginalOrbit_value]

theorem optionOriginalOrbit_mark_eval {M₀ : Type u} [LieRing M₀] [LieAlgebra ℚ M₀]
    (Fmark : NilpotentLieFiltration M₀ s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    {σ τ : Type*} {w : σ → ℕ} {v : τ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w)
    (marked : ∀ i, (optionFiltrations Fmark (fun j => (D j).filtration) i).realification.PolynomialOrbit v)
    (x : σ → ℤ) (y : τ → ℤ)
    (hmark : realificationMap (hnil := (optionProduct D₀ D).filtration.lowerCentralSeries_eq_bot)
      (hM := (NilpotentLieFiltration.pi
        (optionFiltrations Fmark (fun j => (D j).filtration))).lowerCentralSeries_eq_bot)
      (optionMarkedLieMap (L := L) φ)
      ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x g) =
        (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => (D j).filtration))).realification.polynomialOrbitEval
          v y (piRealOrbit (optionFiltrations Fmark (fun j => (D j).filtration)) marked)) :
    realificationMap (hnil := D₀.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.lowerCentralSeries_eq_bot) φ
      (D₀.filtration.realification.polynomialOrbitEval w x (optionOriginalOrbit D₀ D g)) =
        Fmark.realification.polynomialOrbitEval v y (marked none) := by
  rw [optionOriginalOrbit_eval]
  apply NilpotentLieBCHGroup.ext
  have hc := congrArg (fun z : (NilpotentLieFiltration.pi
      (optionFiltrations Fmark (fun j => (D j).filtration))).realification.Group =>
        realificationLieHom (liePiEval none) z.coord) hmark
  have hp := congrArg NilpotentLieBCHGroup.coord
    (piRealOrbit_eval (optionFiltrations Fmark (fun j => (D j).filtration)) marked y none)
  exact (realification_optionMarkedLieMap_none φ
    ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x g).coord).symm.trans
      (hc.trans hp)

theorem optionOriginalOrbit_mark_log {M₀ : Type u} [LieRing M₀] [LieAlgebra ℚ M₀]
    (Fmark : NilpotentLieFiltration M₀ s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w)
    (marked : ∀ i, (optionFiltrations Fmark (fun j => (D j).filtration) i).realification.PolynomialOrbit w)
    (hmark : VectorPolynomial.map
      ((realificationLieHom (optionMarkedLieMap (L := L) φ)).toLinearMap.restrictScalars ℚ) g.log =
        (piRealOrbit (optionFiltrations Fmark (fun j => (D j).filtration)) marked).log) :
    VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
      (optionOriginalOrbit D₀ D g).log = (marked none).log :=
  (congrArg (VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ))
    (optionOriginalOrbit_log D₀ D g)).trans
      (optionMarkedPolynomialProjection_none g.log φ Fmark (fun j => (D j).filtration) marked hmark)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
