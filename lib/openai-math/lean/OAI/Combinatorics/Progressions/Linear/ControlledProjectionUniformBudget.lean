/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.JoinedPairQuotientRefiltration
import OAI.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning
import OAI.Combinatorics.Progressions.Polynomial.ProductPolynomialMaps

namespace OAI

universe u

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realificationLieSubalgebra_comap {L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (U : LieSubalgebra ℚ M) (φ : L →ₗ⁅ℚ⁆ M) :
    realificationLieSubalgebra (U.comap φ) =
      (realificationLieSubalgebra U).comap (realificationLieHom φ) := by
  apply LieSubalgebra.toSubmodule_injective
  exact realification_comap U.toSubmodule φ.toLinearMap

namespace NilpotentLieFiltration

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def realSymbolProjection (w : σ → ℕ) :
    F.RealPolynomialSymbolGroup w →* G.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.filteredPolynomialSymbolMap G φ hφ w)

theorem exists_symbolFactorizationIn_projection_pullback
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hfactor : G.SymbolFactorizationIn f ν hG T
      (F.realSymbolProjection G φ hφ (fun _ => 1) X) p l U) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((p + 2) ^ 10 + 2) ^ 36) ∧ l ∣ m ∧
      F.SymbolFactorizationIn e ω hF T X (((p + 2) ^ 10 + 2) ^ 18 + p) m
        (U.comap (F.associatedGradedMap G φ hφ)) := by
  classical
  let w : σ → ℕ := fun _ => 1
  let B := F.polynomialSymbolBasis e ω hF w
  let C := G.polynomialSymbolBasis f ν hG w
  let ψ := F.filteredPolynomialSymbolMap G φ hφ w
  have hψ : Function.Surjective ψ :=
    F.filteredPolynomialSymbolMap_surjective G φ hφ w hsurj
  have himage : (⊤ : LieSubalgebra ℚ (F.PolynomialSymbol w)).map ψ = ⊤ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨x, rfl⟩ := hψ y
      exact ⟨x, trivial, rfl⟩
  have hb : ∀ j i, RationalHeightLE (B.repr (B j) i) H := by
    intro j i
    simp only [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact rationalHeightLE_one hH
    · exact rationalHeightLE_zero hH
  obtain ⟨S, m, hm, hmp, hlm, hsolve, hslow, hgrid⟩ :=
    NilpotentLieBCHGroup.exists_controlled_fast_lift
      (F.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (G.polynomialSymbol_lowerCentralSeries_eq_bot w) B C
      (fun z => z.val.1) (fun z => z.val.1) ⊤ B B.span_eq
      (fun _ _ _ => trivial) ψ
      (fun i j hij => F.filteredPolynomialSymbolMap_monomial_blocks
        G e ω hF f ν hG φ hφ w j i hij)
      hH hl hb
      (fun i j => F.filteredPolynomialSymbolMap_basis_height
        G e ω hF f ν hG φ hφ w hH hentries j i)
      hp hrows hcols hHp hlp
  simp only [Basis.equivFun_apply] at hslow hgrid
  let lift := NilpotentLieBCHGroup.realLinearCoordinateLift
    (hL := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w) S
  have hright (g : G.RealPolynomialSymbolGroup w) :
      F.realSymbolProjection G φ hφ w (lift g) = g := by
    apply (hsolve g ?_).2
    change g.coord ∈ ((⊤ : LieSubalgebra ℚ (F.PolynomialSymbol w)).map ψ).toSubmodule.baseChange ℝ
    rw [himage]
    simp
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := hfactor
  dsimp only [SymbolSlowBound, SymbolRationalGrid] at hE hR
  let middle := (lift E)⁻¹ * X * (lift R)⁻¹
  have hmiddle : F.realSymbolProjection G φ hφ w middle = P := by
    dsimp only [middle]
    rw [map_mul, map_mul, map_inv, map_inv, hright, hright, ← hprod]
    group
  refine ⟨m, hm, hmp, hlm, lift E, middle, lift R, ?_, ?_, ?_, ?_⟩
  · dsimp only [middle]; group
  · have h := hslow (monomialScale T) (monomialScale_pos T hT)
      (Real.exp p) (Real.exp_pos p).le E (by with_reducible exact hE)
    simp only [← Real.exp_add] at h
    dsimp only [SymbolSlowBound]
    with_reducible exact h
  · apply hgrid R
    with_reducible exact hR
  · rw [← F.symbolPointwiseSubalgebra_comap G e ω hF f ν hG φ hφ w U,
      realificationLieSubalgebra_comap]
    change (F.realSymbolProjection G φ hφ w middle).coord ∈
      realificationLieSubalgebra (G.symbolPointwiseSubalgebra f ν hG w U)
    rw [hmiddle]
    with_reducible exact hP

end NilpotentLieFiltration
end Erdos3

end

section

universe v

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

def optionPairProjection (j : ι) :
    (∀ i : Option ι, optionLieSpace L₀ L i) →ₗ⁅ℚ⁆ PairAlgebra L₀ (L j) :=
  liePiMap (fun b => by
    cases b
    · exact liePiEval (some j)
    · exact liePiEval none)

@[simp] theorem optionPairProjection_true (j : ι)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    optionPairProjection j x true = x none := rfl

@[simp] theorem optionPairProjection_false (j : ι)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    optionPairProjection j x false = x (some j) := rfl

@[simp] theorem pairFrequency_optionPairProjection (j : ι)
    (η : L₀ →ₗ[ℚ] ℚ) (θ : L j →ₗ[ℚ] ℚ)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    pairFrequency η θ (optionPairProjection j x) = η (x none) + θ (x (some j)) := by
  rw [pairFrequency_apply, optionPairProjection_true, optionPairProjection_false]

@[simp] theorem realification_optionPairProjection_true (j : ι)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) :
    realificationLieHom (liePiEval true) (realificationLieHom (optionPairProjection j) x) =
      realificationLieHom (liePiEval none) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

@[simp] theorem realification_optionPairProjection_false (j : ι)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) :
    realificationLieHom (liePiEval false) (realificationLieHom (optionPairProjection j) x) =
      realificationLieHom (liePiEval (some j)) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

variable [Fintype ι] {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (j : ι)

theorem optionPairProjection_layers (k : ℕ)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i)
    (hx : x ∈ (optionProduct D₀ D).filtration.layer k) :
    optionPairProjection j x ∈ (pi (pairModels D₀ (D j))).filtration.layer k := by
  apply (mem_pi_layer (fun b => (pairModels D₀ (D j) b).filtration) k _).mpr
  intro b
  cases b
  · exact (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k x).mp hx (some j)
  · exact (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k x).mp hx none

theorem optionPairProjection_layer_surjective (k : ℕ) (x : PairAlgebra L₀ (L j))
    (hx : x ∈ (pi (pairModels D₀ (D j))).filtration.layer k) :
    ∃ y ∈ (optionProduct D₀ D).filtration.layer k, optionPairProjection j y = x := by
  classical
  let y : ∀ i : Option ι, optionLieSpace L₀ L i
    | none => x true
    | some i => Pi.single (M := L) j (x false) i
  refine ⟨y, ?_, ?_⟩
  · apply (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k y).mpr
    intro i
    cases i with
    | none =>
      exact (mem_pi_layer (fun b => (pairModels D₀ (D j) b).filtration) k x).mp hx true
    | some i =>
      by_cases hij : i = j
      · subst i
        change Pi.single (M := L) j (x false) j ∈ (D j).filtration.layer k
        erw [Pi.single_eq_same]
        exact (mem_pi_layer (fun b => (pairModels D₀ (D j) b).filtration) k x).mp hx false
      · change Pi.single (M := L) j (x false) i ∈ (D i).filtration.layer k
        erw [Pi.single_eq_of_ne hij]
        exact Submodule.zero_mem _
  · funext b
    cases b
    · exact Pi.single_eq_same (M := L) j (x false)
    · rfl

theorem optionPairProjection_piRealOrbit_log {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w) :
    VectorPolynomial.map
      ((realificationLieHom (optionPairProjection j)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log =
        (pairOrbit D₀ (D j) (g none) (g (some j))).log := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  apply ((Pi.basis (fun b => (pairModels D₀ (D j) b).basis)).baseChange ℝ).repr.injective
  ext ⟨b, k⟩
  rw [realification_pi_basis_repr, realification_pi_basis_repr]
  change ((pairModels D₀ (D j) b).basis.baseChange ℝ).repr
    (realificationLieHom (liePiEval b) (realificationLieHom (optionPairProjection j)
      (coefficients (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log α))) k =
    ((pairModels D₀ (D j) b).basis.baseChange ℝ).repr
      (realificationLieHom (liePiEval b)
        (coefficients (pairOrbit D₀ (D j) (g none) (g (some j))).log α)) k
  have hpair := piRealOrbit_coefficient (fun b => (pairModels D₀ (D j) b).filtration)
    (fun b => by cases b; exact g (some j); exact g none) α b
  change realificationLieHom (liePiEval b)
    (coefficients (pairOrbit D₀ (D j) (g none) (g (some j))).log α) = _ at hpair
  rw [hpair]
  cases b
  · rw [realification_optionPairProjection_false]
    exact congrArg (fun x => ((D j).basis.baseChange ℝ).repr x k)
      (piRealOrbit_coefficient (fun i => (optionFactors D₀ D i).filtration) g α (some j))
  · rw [realification_optionPairProjection_true]
    exact congrArg (fun x => (D₀.basis.baseChange ℝ).repr x k)
      (piRealOrbit_coefficient (fun i => (optionFactors D₀ D i).filtration) g α none)

variable {α β σ : Type*}
  (e : Basis α ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) (ω : α → ℕ)
  (hF : ∀ k, (optionProduct D₀ D).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ ω i}))
  (b : Basis β ℚ (PairAlgebra L₀ (L j))) (ν : β → ℕ)
  (hG : ∀ k, (pi (pairModels D₀ (D j))).filtration.layer k =
    Submodule.span ℚ (b '' {i | k ≤ ν i}))

theorem optionPairProjection_jointOrbitSymbol {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w) :
    (optionProduct D₀ D).filtration.realSymbolProjection
      (pi (pairModels D₀ (D j))).filtration
      (optionPairProjection j) (optionPairProjection_layers D₀ D j) w
      ((optionProduct D₀ D).filtration.realPolynomialSymbolHom e ω hF w
        ⟨⟨(piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log,
          (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).property⟩⟩) =
      pairOrbitSymbol D₀ (D j) (g none) (g (some j)) b ν hG := by
  apply NilpotentLieBCHGroup.ext
  have h := (optionProduct D₀ D).filtration.realFilteredPolynomialSymbolMap_polynomial
    (pi (pairModels D₀ (D j))).filtration
    (optionPairProjection j) (optionPairProjection_layers D₀ D j)
    e ω hF b ν hG w
    ⟨(piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log,
      (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).property⟩
  change _ = (pi (pairModels D₀ (D j))).filtration.realSymbolOfPolynomial b ν hG w
    (pairOrbit D₀ (D j) (g none) (g (some j))).log
  exact h.trans (congrArg
    ((pi (pairModels D₀ (D j))).filtration.realSymbolOfPolynomial b ν hG w)
    (optionPairProjection_piRealOrbit_log D₀ D j g))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {J : Type*} [Fintype J] {L : Type u} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))

theorem optionPairProjection_native_logHeight (j : J)
    (x : ∀ i : Option J, optionLieSpace L M i) {p : ℝ}
    (hx : ∀ k, rationalLogHeight ((optionProduct D E).basis.repr x k) ≤ p) :
    ∀ k, rationalLogHeight ((pi (pairModels D (E j))).basis.repr
      (optionPairProjection j x) k) ≤ p := by
  intro k
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ b : Bool, Fin (Bool.rec (d j) d₀ b))).symm k = z
  rcases z with ⟨b, i⟩
  cases b
  · change rationalLogHeight ((E j).basis.repr (x (some j)) i) ≤ p
    exact (congrArg rationalLogHeight
      (productFinBasis_repr_component (optionFactors D E) x (some j) i)).le.trans (hx _)
  · change rationalLogHeight (D.basis.repr (x none) i) ≤ p
    exact (congrArg rationalLogHeight
      (productFinBasis_repr_component (optionFactors D E) x none i)).le.trans (hx _)

theorem optionPairProjection_adapted_logHeight {α β : Type*}
    (j : J) (e : Basis α ℚ (∀ i : Option J, optionLieSpace L M i))
    (b : Basis β ℚ (PairAlgebra L (M j))) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ i : Bool, Fin (Bool.rec (d j) d₀ i)) : ℝ) ≤ p)
    (he : ∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ p)
    (hb : ∀ i k, rationalLogHeight (b.repr ((pi (pairModels D (E j))).basis i) k) ≤ p) :
    ∀ i k, rationalLogHeight (b.repr (optionPairProjection j (e i)) k) ≤ (p + 3) ^ 4 := by
  intro i k
  have hp' : 0 ≤ p + 1 := by linarith
  have hcoord := rational_basis_coordinates_logHeight (pi (pairModels D (E j))).basis b
    hp' (by simpa only [Fintype.card_fin] using hdim.trans (show p ≤ p + 1 by linarith))
    (ceil_exp_le_exp_add_one hp)
    (fun i k => rationalHeightLE_ceil_exp (hb i k)) (optionPairProjection j (e i))
    (fun k => (optionPairProjection_native_logHeight D E j (e i) (he i) k).trans
      (by linarith)) k
  convert hcoord using 1
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

noncomputable def controlledProjectionBudget (p : ℝ) : ℝ :=
  (((p + 2) ^ 10 + 2) ^ 36) + (((p + 2) ^ 10 + 2) ^ 18 + p) +
    (preimageBasisBudget p + 1)

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem controlledSymbolFactorizationAtFast_projection_pullback
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (η : M →ₗ[ℚ] ℚ) (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hfactor : G.ControlledSymbolFactorizationAtFast f ν hG η T
      (F.realSymbolProjection G φ hφ (fun _ => 1) X) p U) :
    F.ControlledSymbolFactorizationAtFast e ω hF (η.comp φ.toLinearMap) T X
      (controlledProjectionBudget p) (U.comap (F.associatedGradedMap G φ hφ)) := by
  obtain ⟨l, E, P, R, v, hl, hlp, hprod, hE, hR, hv, hgraded, hvH, hzero, hP⟩ := hfactor
  obtain ⟨m, hm, hmp, _, hsplit⟩ :=
    F.exists_symbolFactorizationIn_projection_pullback G e ω hF f ν hG φ hφ
      hsurj hH hl hentries hp hrows hcols hHp hlp T hT X U
      ⟨E, P, R, hprod, hE, hR, hP⟩
  obtain ⟨u, hu, huH⟩ := F.exists_associatedGradedMap_comap_bounded_spanning
    G e ω hF f ν hG φ hφ U v hv hp hι hκ hvH
    (fun i j => rationalLogHeight_le_of_height (hentries j i) hHp)
  have hbase : 0 ≤ preimageBasisBudget p := preimageBasisBudget_nonneg hp
  have hq : 0 ≤ ((p + 2) ^ 10 + 2) := by positivity
  have hden : ((p + 2) ^ 10 + 2) ^ 36 ≤ controlledProjectionBudget p := by
    unfold controlledProjectionBudget
    exact (le_add_of_nonneg_right (by positivity)).trans
      (le_add_of_nonneg_right (by positivity))
  have hslow : ((p + 2) ^ 10 + 2) ^ 18 + p ≤ controlledProjectionBudget p := by
    unfold controlledProjectionBudget
    have := pow_nonneg hq 36
    linarith
  have hheight : preimageBasisBudget p + 1 ≤ controlledProjectionBudget p := by
    unfold controlledProjectionBudget
    have := pow_nonneg hq 36
    have := pow_nonneg hq 18
    linarith
  obtain ⟨A, B, C, hABC, hA, hC, hB⟩ := hsplit.mono F e ω hF hslow hT
  exact ⟨m, A, B, C, u, hm, hmp.trans (Real.exp_le_exp.mpr hden),
    hABC, hA, hC, hu,
    F.associatedGradedMap_comap_graded G e ω hF f ν hG φ hφ U hgraded,
    fun i j => (huH i j).trans hheight,
    F.gradedFrequency_comap_top_zero G e ω hF f ν hG φ hφ η U hzero, hB⟩

theorem controlledSymbolFactorization_projection_pullback
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (η : M →ₗ[ℚ] ℚ)
    (hfactor : G.ControlledSymbolFactorization f ν hG η T
      (F.realSymbolProjection G φ hφ (fun _ => 1) X) p) :
    F.ControlledSymbolFactorization e ω hF (η.comp φ.toLinearMap) T X
      (controlledProjectionBudget p) := by
  obtain ⟨U, hU⟩ := hfactor.exists_fastWitness G f ν hG
  obtain ⟨m, E, P, R, v, hdata⟩ :=
    F.controlledSymbolFactorizationAtFast_projection_pullback G e ω hF f ν hG φ hφ
      hsurj hH hentries hp hι hκ hrows hcols hHp T hT X η U hU
  exact ⟨m, E, P, R, _, v, hdata⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

theorem controlledProjectionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ controlledProjectionBudget p := by
  have := preimageBasisBudget_nonneg hp
  unfold controlledProjectionBudget
  positivity

theorem le_controlledProjectionBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ controlledProjectionBudget p := by
  have hpre := preimageBasisBudget_nonneg hp
  have hq : 0 ≤ ((p + 2) ^ 10 + 2) := by positivity
  have h36 := pow_nonneg hq 36
  have h18 := pow_nonneg hq 18
  unfold controlledProjectionBudget
  linarith

theorem exists_controlledProjectionBudget_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → controlledProjectionBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ :=
    Polynomial.X + (Polynomial.X + (Polynomial.X + 3) ^ 7 + 2) ^ 4 + 1
  let P : Polynomial ℕ :=
    ((Polynomial.X + 2) ^ 10 + 2) ^ 36 +
      (((Polynomial.X + 2) ^ 10 + 2) ^ 18 + Polynomial.X) +
      ((Q + Q * ((Q + 2) ^ 7 + Q)) + 1)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Q, controlledProjectionBudget, preimageBasisBudget, sparseGeneratorBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def controlledProjectionDimensionInput (s : ℕ) (p : ℝ) : ℝ :=
  2 * ((p + (s + 2)) ^ (s + 2)) ^ 2 + p + 1

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem ControlledSymbolFactorizationAtFast.mono {η : L →ₗ[ℚ] ℚ}
    {T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)}
    {p q : ℝ} {U : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.ControlledSymbolFactorizationAtFast e ω hF η T X p U)
    (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.ControlledSymbolFactorizationAtFast e ω hF η T X q U := by
  obtain ⟨m, E, P, R, v, hm, hmp, hprod, hE, hR, hv, hgraded, hheight, hzero, hP⟩ := h
  exact ⟨m, E, P, R, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    F.symbolSlowBound_mono e ω hF _ T hT (Real.exp_le_exp.mpr hpq) E hE,
    hR, hv, hgraded, fun i j => (hheight i j).trans hpq, hzero, hP⟩

variable {κ M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (G : NilpotentLieFiltration M s)
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem controlledSymbolFactorizationAtFast_projection_of_dimensions
    [Fintype σ] [Fintype ι] [Fintype κ]
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (η : M →ₗ[ℚ] ℚ) (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hfactor : G.ControlledSymbolFactorizationAtFast f ν hG η T
      (F.realSymbolProjection G φ hφ (fun _ => 1) X) p U) :
    F.ControlledSymbolFactorizationAtFast e ω hF (η.comp φ.toLinearMap) T X
      (controlledProjectionBudget (controlledProjectionDimensionInput s p))
      (U.comap (F.associatedGradedMap G φ hφ)) := by
  let :=  symbolBasisIndexFintype (fun _ : σ => 1) ω s (fun _ => Nat.zero_lt_one)
    (F.adaptedBasis_weight_le_step e ω hF)
  let :=  symbolBasisIndexFintype (fun _ : σ => 1) ν s (fun _ => Nat.zero_lt_one)
    (G.adaptedBasis_weight_le_step f ν hG)
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  let r : ℝ := controlledProjectionDimensionInput s p
  have hpR : p ≤ r := by
    change p ≤ 2 * q ^ 2 + p + 1
    nlinarith [sq_nonneg q]
  have hR : 0 ≤ r := hp.trans hpR
  have hq : 1 ≤ q := by
    apply one_le_pow₀
    have := Nat.cast_nonneg (α := ℝ) s
    linarith
  have hsource : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le _ _ s (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step e ω hF))).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have htarget : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le _ _ s (fun _ => Nat.zero_lt_one)
      (G.adaptedBasis_weight_le_step f ν hG))).trans
      (symbol_dimension_bound_le_power s (Fintype.card κ) (Fintype.card σ) hp hκ hσ)
  have hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ r := by
    simp only [Fintype.card_sum, Nat.cast_add]
    change _ ≤ 2 * q ^ 2 + p + 1
    nlinarith
  have hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ r := by
    rw [Nat.cast_mul]
    have hnonneg := Nat.cast_nonneg (α := ℝ)
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω))
    have hsquare := mul_self_le_mul_self hnonneg hsource
    change _ ≤ 2 * q ^ 2 + p + 1
    nlinarith
  exact F.controlledSymbolFactorizationAtFast_projection_pullback G e ω hF f ν hG φ hφ
    hsurj hH hentries hR (hι.trans hpR) (hκ.trans hpR) hrows hcols
    (hHp.trans (Real.exp_le_exp.mpr hpR)) T hT X η U
    (hfactor.mono G f ν hG hpR hT)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

theorem le_controlledProjectionDimensionInput (s : ℕ) (p : ℝ) :
    p ≤ controlledProjectionDimensionInput s p := by
  unfold controlledProjectionDimensionInput
  nlinarith [sq_nonneg ((p + (s + 2)) ^ (s + 2))]

theorem controlledProjectionDimensionInput_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ controlledProjectionDimensionInput s p :=
  hp.trans (le_controlledProjectionDimensionInput s p)

theorem exists_controlledProjectionUniformBudget_power (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      controlledProjectionBudget (controlledProjectionDimensionInput s p) ≤ (p + C) ^ C := by
  obtain ⟨a, _, ha⟩ := exists_controlledProjectionBudget_power
  let P : Polynomial ℕ :=
    (2 * ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)) ^ 2 +
      Polynomial.X + 1 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  apply (ha _ (controlledProjectionDimensionInput_nonneg s hp)).trans
  simpa [P, controlledProjectionDimensionInput, Polynomial.eval₂_pow] using hbound p hp

end Erdos3.NilpotentLieFiltration

end

end OAI
