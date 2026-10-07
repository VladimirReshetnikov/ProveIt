/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Build the representative map by composition of its existing linear maps
and close reflexive coordinate conversion goals on Lean 4.32.
Mathematical statements and underlying coordinate function are unchanged. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import OAI.Combinatorics.Progressions.Linear.DualAdjointFiltration
import OAI.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial

set_option maxRecDepth 2048

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_smul_real (g : NilpotentLieBCHGroup L s hnil) (r : ℝ) (x : L) :
    dualAdjoint g (r • x) = r • dualAdjoint g x := by
  let T : L →ₗ[ℚ] L := r • LinearMap.id
  have hT : ∀ a b : L, b ∈ (⊤ : LieIdeal ℚ L) →
      T ⁅a, b⁆ = ⁅(LieHom.id : L →ₗ⁅ℚ⁆ L) a, T b⁆ := by
    intro a b _
    change r • ⁅a, b⁆ = ⁅a, r • b⁆
    exact (lie_smul r a b).symm
  exact (dualLinearLift_adjoint_eq hnil ⊤ LieHom.id T hT g x
    (by trivial) g (r • x) rfl rfl).symm

noncomputable def dualAdjointRealLinearEquiv (g : NilpotentLieBCHGroup L s hnil) :
    L ≃ₗ[ℝ] L :=
  { dualAdjointAddEquiv g with map_smul' := dualAdjoint_smul_real g }

@[simp] theorem dualAdjointRealLinearEquiv_apply
    (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjointRealLinearEquiv g x = dualAdjoint g x := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_real_mem_of_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℝ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : L) (hx : x ∈ V) :
    dualAdjoint g x ∈ V :=
  dualAdjoint_mem_of_invariant U (V.restrictScalars ℚ) hUV g hg x hx

noncomputable def invariantRealAdjoint (U : LieSubalgebra ℚ L) (W : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) : W ≃ₗ[ℝ] W where
  toFun x := ⟨dualAdjoint g x.val, dualAdjoint_real_mem_of_invariant U W hUW g hg x.val x.property⟩
  invFun x := ⟨dualAdjoint g⁻¹ x.val,
    dualAdjoint_real_mem_of_invariant U W hUW g⁻¹ (U.neg_mem hg) x.val x.property⟩
  left_inv x := Subtype.ext (dualAdjoint_inv_cancel g x.val)
  right_inv x := Subtype.ext (dualAdjoint_cancel_inv g x.val)
  map_add' x y := Subtype.ext (dualAdjoint_add g x.val y.val)
  map_smul' r x := Subtype.ext (dualAdjoint_smul_real g r x.val)

@[simp] theorem invariantRealAdjoint_coe (U : LieSubalgebra ℚ L) (W : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : W) :
    (invariantRealAdjoint U W hUW g hg x : L) = dualAdjoint g x.val := rfl

theorem invariantRealAdjoint_map_submodule (U : LieSubalgebra ℚ L) (W V : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) :
    (V.comap W.subtype).map (invariantRealAdjoint U W hUW g hg).toLinearMap = V.comap W.subtype := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact dualAdjoint_real_mem_of_invariant U V hUV g hg x.val hx
  · intro y hy
    refine ⟨(invariantRealAdjoint U W hUW g hg).symm y, ?_, ?_⟩
    · exact dualAdjoint_real_mem_of_invariant U V hUV g⁻¹ (U.neg_mem hg) y.val hy
    · exact (invariantRealAdjoint U W hUW g hg).apply_symm_apply y

noncomputable def invariantRealAdjointQuotient (U : LieSubalgebra ℚ L) (W V : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) :
    (W ⧸ V.comap W.subtype) ≃ₗ[ℝ] (W ⧸ V.comap W.subtype) :=
  Submodule.Quotient.equiv _ _ (invariantRealAdjoint U W hUW g hg)
    (invariantRealAdjoint_map_submodule U W V hUW hUV g hg)

@[simp] theorem invariantRealAdjointQuotient_mk (U : LieSubalgebra ℚ L) (W V : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : W) :
    invariantRealAdjointQuotient U W V hUW hUV g hg ((V.comap W.subtype).mkQ x) =
      (V.comap W.subtype).mkQ (invariantRealAdjoint U W hUW g hg x) := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped TensorProduct
open NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  (I : LieIdeal ℚ L)

theorem realification_ideal_intertwining (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
    (hT : ∀ a b, b ∈ I → T ⁅a, b⁆ = ⁅B a, T b⁆)
    (x y : ℝ ⊗[ℚ] L) (hy : y ∈ I.toSubmodule.baseChange ℝ) :
    T.baseChange ℝ ⁅x, y⁆ = ⁅realificationLieHom B x, T.baseChange ℝ y⁆ := by
  obtain ⟨v, rfl⟩ := hy
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    induction v using TensorProduct.inductionOn with
    | tmul q b =>
      change (r * q) ⊗ₜ[ℚ] T ⁅a, b.val⁆ = (r * q) ⊗ₜ[ℚ] ⁅B a, T b.val⁆
      rw [hT a b.val b.property]
    | add v z hv hz => simp only [map_add, lie_add, hv, hz]
  | add x z hx hz => simp only [map_add, add_lie, hx, hz]

variable {s t : ℕ} (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (hM : LieModule.lowerCentralSeries ℚ M M t = ⊥)

noncomputable def realIdealAdjoint
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL)) :
    (ℝ ⊗[ℚ] I.toSubmodule) ≃ₗ[ℝ] (ℝ ⊗[ℚ] I.toSubmodule) :=
  (realificationSubmoduleEquiv I.toSubmodule).trans
    ((invariantRealAdjoint ⊤ (I.toSubmodule.baseChange ℝ)
      (fun _ _ _ hy => (I.baseChange ℝ).lie_mem hy) g (by trivial)).trans
        (realificationSubmoduleEquiv I.toSubmodule).symm)

theorem realIdealAdjoint_inclusion
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL))
    (x : ℝ ⊗[ℚ] I.toSubmodule) :
    I.toSubmodule.subtype.baseChange ℝ (realIdealAdjoint I hL g x) =
      dualAdjoint g (I.toSubmodule.subtype.baseChange ℝ x) := by
  change (realificationSubmoduleEquiv I.toSubmodule
    ((realificationSubmoduleEquiv I.toSubmodule).symm
      ((invariantRealAdjoint ⊤ (I.toSubmodule.baseChange ℝ)
        (fun _ _ _ hy => (I.baseChange ℝ).lie_mem hy) g (by trivial))
          (realificationSubmoduleEquiv I.toSubmodule x))) : ℝ ⊗[ℚ] L) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem realIdealMap_adjoint (B : L →ₗ⁅ℚ⁆ M) (f : I.toSubmodule →ₗ[ℚ] M)
    (hf : ∀ a (p : I.toSubmodule),
      f ⟨⁅a, p.val⁆, I.lie_mem p.property⟩ = ⁅B a, f p⁆)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL))
    (x : ℝ ⊗[ℚ] I.toSubmodule) :
    f.baseChange ℝ (realIdealAdjoint I hL g x) =
      dualAdjoint (realificationMap (hnil := hL) (hM := hM) B g) (f.baseChange ℝ x) := by
  obtain ⟨T, hTf⟩ := f.exists_extend
  have he (p : I.toSubmodule) : T p.val = f p := DFunLike.congr_fun hTf p
  have hT (a b : L) (hb : b ∈ I) : T ⁅a, b⁆ = ⁅B a, T b⁆ := by
    rw [he ⟨⁅a, b⁆, I.lie_mem hb⟩, he ⟨b, hb⟩]
    exact hf a ⟨b, hb⟩
  have hr (y : ℝ ⊗[ℚ] I.toSubmodule) :
      T.baseChange ℝ (I.toSubmodule.subtype.baseChange ℝ y) = f.baseChange ℝ y := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hTf]
  have hx : I.toSubmodule.subtype.baseChange ℝ x ∈ I.toSubmodule.baseChange ℝ := ⟨x, rfl⟩
  let J : LieIdeal ℚ (ℝ ⊗[ℚ] L) :=
    { (I.toSubmodule.baseChange ℝ).restrictScalars ℚ with
      lie_mem := fun {a b} hb => (I.baseChange ℝ).lie_mem hb }
  calc
    _ = T.baseChange ℝ (I.toSubmodule.subtype.baseChange ℝ (realIdealAdjoint I hL g x)) := (hr _).symm
    _ = T.baseChange ℝ (dualAdjoint g (I.toSubmodule.subtype.baseChange ℝ x)) := by
      rw [realIdealAdjoint_inclusion]
    _ = dualAdjoint (realificationMap (hnil := hL) (hM := hM) B g)
        (T.baseChange ℝ (I.toSubmodule.subtype.baseChange ℝ x)) := by
      exact dualLinearLift_adjoint_of_steps (realification_lowerCentralSeries_eq_bot hL)
        (realification_lowerCentralSeries_eq_bot hM) J
        (realLieHomToRat (realificationLieHom B)) ((T.baseChange ℝ).restrictScalars ℚ)
        (realification_ideal_intertwining I B T hT) g _ hx
    _ = _ := by rw [hr]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realSymbolRepresentative :
    F.RealPolynomialSymbol w →ₗ[ℚ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  (ofSupportedCoordinates (R := ℚ) (b.baseChange ℝ)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}).comp
      (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.restrictScalars ℚ).toLinearMap

noncomputable def realSymbolOfPolynomial :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) →ₗ[ℚ] F.RealPolynomialSymbol w :=
  (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.symm.restrictScalars ℚ).toLinearMap.comp
    (supportedCoordinates (b.baseChange ℝ)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2})

@[simp] theorem realSymbolRepresentative_coefficient
    (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w x) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z := by
  convert ofSupportedCoordinates_apply (R := ℚ) (b.baseChange ℝ)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
    (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x) z using 1 <;> rfl

theorem realSymbolRepresentative_coefficient_of_ne
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) (i : ι)
    (h : Finsupp.weight w α ≠ ω i) :
    (b.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hlayers w x) α) i = 0 := by
  convert ofSupportedCoordinates_apply_of_not_mem (R := ℚ) (b.baseChange ℝ)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
    (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x) α i h using 1 <;> rfl

@[simp] theorem realSymbolOfPolynomial_coordinate
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
      (F.realSymbolOfPolynomial b ω hlayers w p) z =
      (b.baseChange ℝ).repr (coefficients p z.val.1) z.val.2 := by
  change (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
    (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.symm _)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem realSymbolOfPolynomial_representative (x : F.RealPolynomialSymbol w) :
    F.realSymbolOfPolynomial b ω hlayers w (F.realSymbolRepresentative b ω hlayers w x) = x := by
  apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfPolynomial_coordinate, F.realSymbolRepresentative_coefficient]

include hlayers

theorem real_mem_layer_iff_basis_coordinates (j : ℕ) (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realification.layer j ↔ ∀ i, ¬ j ≤ ω i → (b.baseChange ℝ).repr v i = 0 := by
  change v ∈ (F.realLayer j).toSubmodule ↔ _
  rw [F.realLayer_eq_span_basis b j {i | j ≤ ω i} (hlayers j), basis_mem_span_image_iff]
  rfl

theorem realSymbolRepresentative_adapted (x : F.RealPolynomialSymbol w) :
    F.realification.Adapted w (F.realSymbolRepresentative b ω hlayers w x) := by
  rw [F.realification.adapted_iff_coefficients]
  intro α
  apply (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mpr
  intro i hi
  exact F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w x α i
    (fun h => hi h.le)

theorem realSymbolRepresentative_constant (x : F.RealPolynomialSymbol w) :
    coefficients (F.realSymbolRepresentative b ω hlayers w x) 0 = 0 := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  change (b.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hlayers w x) 0) i = 0
  apply F.realSymbolRepresentative_coefficient_of_ne
  rw [map_zero]
  exact (F.adaptedBasis_weight_pos b ω hlayers i).ne

noncomputable def realAdaptedSymbolRepresentative (x : F.RealPolynomialSymbol w) :
    F.realification.adaptedLieSubalgebra w :=
  ⟨F.realSymbolRepresentative b ω hlayers w x,
    (F.realification.mem_adaptedSubmodule w _).mpr
      (F.realSymbolRepresentative_adapted b ω hlayers w x)⟩

@[simp] theorem realAdaptedSymbolRepresentative_coe (x : F.RealPolynomialSymbol w) :
    (F.realAdaptedSymbolRepresentative b ω hlayers w x : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      F.realSymbolRepresentative b ω hlayers w x := rfl

theorem realSymbolOfPolynomial_eq_zero_iff
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w p = 0 ↔
      ∀ α, coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
        F.realification.layer (Finsupp.weight w α + 1) := by
  constructor
  · intro hp α
    apply (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mpr
    intro i hi
    by_cases he : Finsupp.weight w α = ω i
    · have hc := F.realSymbolOfPolynomial_coordinate b ω hlayers w p ⟨(α, i), he⟩
      rw [hp, map_zero, Finsupp.zero_apply] at hc
      exact hc.symm
    · exact (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
        (p.property α) i (by omega)
  · intro hp
    apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
    ext z
    rw [map_zero, Finsupp.zero_apply, F.realSymbolOfPolynomial_coordinate]
    exact (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
      (hp z.val.1) z.val.2 (by have hz := z.property; omega)

theorem realSymbolOfPolynomial_eq_iff_symbolMap_eq
    (p q : F.realification.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w p = F.realSymbolOfPolynomial b ω hlayers w q ↔
      F.realification.polynomialSymbolMap w p = F.realification.polynomialSymbolMap w q := by
  rw [← sub_eq_zero, ← map_sub]
  change F.realSymbolOfPolynomial b ω hlayers w
    ((p - q : F.realification.adaptedLieSubalgebra w) : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = 0 ↔ _
  rw [F.realSymbolOfPolynomial_eq_zero_iff b ω hlayers w (p - q),
    F.realification.polynomialSymbolMap_eq_iff]
  rfl

theorem realAdaptedSymbolRepresentative_symbolMap
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realification.polynomialSymbolMap w
      (F.realAdaptedSymbolRepresentative b ω hlayers w
        (F.realSymbolOfPolynomial b ω hlayers w p)) = F.realification.polynomialSymbolMap w p := by
  apply (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hlayers w _ p).mp
  rw [F.realAdaptedSymbolRepresentative_coe]
  exact F.realSymbolOfPolynomial_representative b ω hlayers w _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF

theorem realBasis_mem_layer (i : ι) : (b.baseChange ℝ) i ∈ F.realification.layer (ω i) := by
  apply (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mpr
  intro k hk
  have hki : k ≠ i := by rintro rfl; exact hk le_rfl
  rw [Basis.repr_self]
  exact Finsupp.single_eq_of_ne hki

theorem dualAdjoint_realBasis_coordinate (g : F.realification.Group) (i k : ι)
    (hki : ω k ≤ ω i) :
    (b.baseChange ℝ).repr (dualAdjoint g ((b.baseChange ℝ) i)) k =
      (b.baseChange ℝ).repr ((b.baseChange ℝ) i) k := by
  have hd := F.realification.dualAdjoint_sub_mem_next_layer (ω i) g ((b.baseChange ℝ) i)
    (F.realBasis_mem_layer b ω hF i)
  have hz := (F.real_mem_layer_iff_basis_coordinates b ω hF (ω i + 1) _).mp hd k
    (by omega)
  simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using hz

theorem dualAdjoint_realMatrix_entry [Fintype ι] [DecidableEq ι]
    (g : F.realification.Group) (i k : ι) (hki : ω k ≤ ω i) :
    LinearMap.toMatrix (b.baseChange ℝ) (b.baseChange ℝ)
      (dualAdjointRealLinearEquiv g).toLinearMap k i = if i = k then 1 else 0 := by
  rw [LinearMap.toMatrix_apply]
  change (b.baseChange ℝ).repr (dualAdjoint g ((b.baseChange ℝ) i)) k = _
  rw [F.dualAdjoint_realBasis_coordinate b ω hF g i k hki]
  exact (b.baseChange ℝ).equivFun_self i k

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realSymbolRepresentative_slow_coefficients (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hlayers w T M g)
    (α : σ →₀ ℕ) (i : ι) :
    |(b.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) α) i| ≤
      M / monomialScale T α := by
  by_cases h : Finsupp.weight w α = ω i
  · have hc := F.realSymbolRepresentative_coefficient b ω hlayers w g.coord ⟨(α, i), h⟩
    exact (congrArg abs hc).le.trans (hg ⟨(α, i), h⟩)
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w g.coord α i h, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realSymbolRepresentative_rational_coefficients (l : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hlayers w l g) :
    (fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) z.1) z.2)
        ∈ realDenominatorGrid l := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => if h : Finsupp.weight w z.1 = ω z.2 then a ⟨z, h⟩ else 0, ?_⟩
  funext z
  change ((if h : Finsupp.weight w z.1 = ω z.2 then a ⟨z, h⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) z.1) z.2
  by_cases h : Finsupp.weight w z.1 = ω z.2
  · rw [dite_eq_left h]
    have hc := F.realSymbolRepresentative_coefficient b ω hlayers w g.coord ⟨z, h⟩
    change (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) z.1) z.2 = _ at hc
    rw [hc]
    exact congrFun ha ⟨z, h⟩
  · rw [dite_eq_right h, Int.cast_zero,
      F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w g.coord z.1 z.2 h, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedBasisSplitting : F.AssociatedGraded ≃ₗ[ℚ] L :=
  (F.associatedGradedBasis b ω hlayers).repr.trans b.repr.symm

@[simp] theorem gradedBasisSplitting_coordinate (x : F.AssociatedGraded) (i : ι) :
    b.repr (F.gradedBasisSplitting b ω hlayers x) i =
      (F.associatedGradedBasis b ω hlayers).repr x i := by
  simp [gradedBasisSplitting]

theorem gradedBasisSplitting_real_coordinate (x : ℝ ⊗[ℚ] F.AssociatedGraded) (i : ι) :
    (b.baseChange ℝ).repr
      ((F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ x) i =
      ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr x i := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul]
    exact congrArg (fun q : ℚ => q • a) (F.gradedBasisSplitting_coordinate b ω hlayers x i)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable (w : σ → ℕ)

theorem realSymbolRepresentative_coefficient_splitting (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) :
    coefficients (F.realSymbolRepresentative b ω hlayers w x) α =
      (F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ
        (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  rw [F.gradedBasisSplitting_real_coordinate]
  by_cases h : Finsupp.weight w α = ω i
  · exact (F.realSymbolRepresentative_coefficient b ω hlayers w x ⟨(α, i), h⟩).trans
      (F.realGradedSymbolPolynomial_coordinate b ω hlayers w x ⟨(α, i), h⟩).symm
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w x α i h,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w x α i h]

theorem realSymbolRepresentative_eq_map (x : F.RealPolynomialSymbol w) :
    F.realSymbolRepresentative b ω hlayers w x =
      VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ).restrictScalars ℚ)
        (F.realGradedSymbolPolynomial b ω hlayers w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact F.realSymbolRepresentative_coefficient_splitting b ω hlayers w x α

theorem realSymbolRepresentative_eval₂ (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realSymbolRepresentative b ω hlayers w x) =
      (F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ
        (eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) := by
  rw [F.realSymbolRepresentative_eq_map, VectorPolynomial.eval₂_map]

end Erdos3.NilpotentLieFiltration

end

end OAI
