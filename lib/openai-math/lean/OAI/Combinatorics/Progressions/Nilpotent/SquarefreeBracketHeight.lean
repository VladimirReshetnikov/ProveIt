/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Linear.SquarefreeBasisPermutation

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realification_inf {V : Type*} [AddCommGroup V] [Module ℚ V]
    (P Q : Submodule ℚ V) :
    (P ⊓ Q).baseChange ℝ = P.baseChange ℝ ⊓ Q.baseChange ℝ := by
  have hker : LinearMap.ker (P.mkQ.prod Q.mkQ) = P ⊓ Q := by
    ext v
    change (P.mkQ v, Q.mkQ v) = (0, 0) ↔ v ∈ P ∧ v ∈ Q
    rw [Prod.mk.injEq]
    exact and_congr (Submodule.Quotient.mk_eq_zero P) (Submodule.Quotient.mk_eq_zero Q)
  rw [← hker, realification_ker]
  ext v
  rw [LinearMap.mem_ker, realification_prod_eq_zero_iff,
    realification_mkQ_eq_zero_iff, realification_mkQ_eq_zero_iff, Submodule.mem_inf]

theorem lie_mem_real_baseChange {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (P Q W : Submodule ℚ L)
    (h : ∀ a ∈ P, ∀ b ∈ Q, ⁅a, b⁆ ∈ W)
    {a b : ℝ ⊗[ℚ] L} (ha : a ∈ P.baseChange ℝ) (hb : b ∈ Q.baseChange ℝ) :
    ⁅a, b⁆ ∈ W.baseChange ℝ := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | tmul t y =>
      change (r * t) ⊗ₜ[ℚ] ⁅(x : L), (y : L)⁆ ∈ W.baseChange ℝ
      exact Submodule.tmul_mem_baseChange_of_mem _ (h x x.property y y.property)
    | add y z hy hz =>
      simpa only [map_add, lie_add] using (W.baseChange ℝ).add_mem hy hz
  | add x z hx hz =>
    simpa only [map_add, add_lie] using (W.baseChange ℝ).add_mem hx hz

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

noncomputable def bracketSystemMatrix (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    (k : κ → L) : Matrix (κ × ι) ν ℚ :=
  fun bi n => f.repr (V.mkQ ⁅(e n : L), k bi.1⁆) bi.2

noncomputable def realBracketSystem (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (κ × ι → ℝ) :=
  LinearMap.pi (fun bi => ((f.baseChange ℝ).coord bi.2).comp
    ((V.mkQ.baseChange ℝ).comp
      ({
        toFun := fun x => ⁅x, (1 : ℝ) ⊗ₜ[ℚ] k bi.1⁆
        map_add' := fun x y => add_lie x y _
        map_smul' := fun r x => smul_lie r x _ } :
          (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] L))))

@[simp] theorem realBracketSystem_apply (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (x : ℝ ⊗[ℚ] L) (bi : κ × ι) :
    realBracketSystem f k x bi =
      (f.baseChange ℝ).repr (V.mkQ.baseChange ℝ ⁅x, (1 : ℝ) ⊗ₜ[ℚ] k bi.1⁆) bi.2 := rfl

noncomputable def bracketSystemLift [Fintype ν] (e : Basis ν ℚ E) :
    (ν → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] L) :=
  (E.subtype.baseChange ℝ).comp (e.baseChange ℝ).equivFun.symm.toLinearMap

theorem bracketSystemLift_mem [Fintype ν] (e : Basis ν ℚ E) (x : ν → ℝ) :
    bracketSystemLift e x ∈ E.baseChange ℝ := ⟨(e.baseChange ℝ).equivFun.symm x, rfl⟩

theorem bracketSystemLift_single [Fintype ν] [DecidableEq ν] (e : Basis ν ℚ E) (n : ν) :
    bracketSystemLift e (Pi.single n 1) = (1 : ℝ) ⊗ₜ[ℚ] (e n : L) := by
  simp [bracketSystemLift, Basis.equivFun_symm_apply]

theorem bracketSystemMatrix_real_apply [Fintype ν] (e : Basis ν ℚ E)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (x : ν → ℝ) :
    (fun bi n => (bracketSystemMatrix e f k bi n : ℝ)) *ᵥ x =
      realBracketSystem f k (bracketSystemLift e x) := by
  classical
  have h : Matrix.mulVecLin (fun bi n => (bracketSystemMatrix e f k bi n : ℝ)) =
      (realBracketSystem f k).comp (bracketSystemLift e) := by
    apply (Pi.basisFun ℝ ν).ext
    intro n
    change (fun bi t => (bracketSystemMatrix e f k bi t : ℝ)) *ᵥ Pi.single n 1 =
      realBracketSystem f k (bracketSystemLift e (Pi.single n 1))
    rw [bracketSystemLift_single]
    change Matrix.of (fun bi t => (bracketSystemMatrix e f k bi t : ℝ)) *ᵥ Pi.single n 1 = _
    rw [Matrix.mulVec_single_one]
    funext bi
    rw [realBracketSystem_apply, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
      LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
    change (f.repr (V.mkQ ⁅(e n : L), k bi.1⁆) bi.2 : ℝ) =
      (f.repr (V.mkQ ⁅(e n : L), k bi.1⁆) bi.2) • (1 : ℝ)
    simp [Algebra.smul_def]
  exact DFunLike.congr_fun h x

theorem realBracketSystem_eq_zero_iff (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (x : ℝ ⊗[ℚ] L) :
    realBracketSystem f k x = 0 ↔ ∀ b, ⁅x, (1 : ℝ) ⊗ₜ[ℚ] k b⁆ ∈ V.baseChange ℝ := by
  constructor
  · intro h b
    apply (realification_mkQ_eq_zero_iff V _).mp
    apply (f.baseChange ℝ).repr.injective
    ext i
    simpa only [realBracketSystem_apply, map_zero, Finsupp.zero_apply, Pi.zero_apply]
      using congrFun h (b, i)
  · intro h
    funext bi
    rw [realBracketSystem_apply, (realification_mkQ_eq_zero_iff V _).mpr (h bi.1)]
    rfl

theorem lie_bracket_coordinate_height {α : Type*} [Fintype α] (b : Basis α ℚ L)
    {H A B : ℕ} (hbr : ∀ i j n, RationalHeightLE (lieStructureConstants b i j n) H)
    (x y : L) (hx : ∀ i, RationalHeightLE (b.repr x i) A)
    (hy : ∀ i, RationalHeightLE (b.repr y i) B) (n : α) :
    RationalHeightLE (b.repr ⁅x, y⁆ n)
      ((Fintype.card α ^ 2 + 1) * (H * A * B) ^ (Fintype.card α ^ 2)) := by
  classical
  rw [lie_coordinate_formula]
  have h := rationalHeightLE_sum
    (fun ij : α × α => lieStructureConstants b ij.1 ij.2 n * b.repr x ij.1 * b.repr y ij.2)
    (fun ij => ((hbr ij.1 ij.2 n).mul (hx ij.1)).mul (hy ij.2))
  simpa only [Fintype.card_prod, ← pow_two] using h

theorem bracketSystemMatrix_height {α : Type*} [Fintype α]
    (b : Basis α ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H A B C : ℕ}
    (hbr : ∀ i j n, RationalHeightLE (lieStructureConstants b i j n) H)
    (he : ∀ n i, RationalHeightLE (b.repr (e n : L) i) A)
    (hk : ∀ t i, RationalHeightLE (b.repr (k t) i) B)
    (hq : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b i)) n) C) (bi : κ × ι) (n : ν) :
    RationalHeightLE (bracketSystemMatrix e f k bi n)
      ((Fintype.card α + 1) *
        (((Fintype.card α ^ 2 + 1) * (H * A * B) ^ (Fintype.card α ^ 2)) * C) ^
          Fintype.card α) :=
  linearMap_coordinate_height b f V.mkQ hq _
    (lie_bracket_coordinate_height b hbr (e n : L) (k bi.1) (he n) (hk bi.1)) bi.2

end Erdos3

end

section

namespace Erdos3

open Module

def squarefreeBracketHeight (n H : ℕ) : ℕ := (n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)

theorem squarefreeBracketHeight_pos (n : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < squarefreeBracketHeight n H := by
  have hHpos : 0 < H := by omega
  unfold squarefreeBracketHeight
  positivity

namespace MultidegreeLieFiltration

variable {ι σ ν L : Type*} [Fintype ι] [Fintype σ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))
  (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
  (hb : ∀ a j k, RationalHeightLE (e.repr (b a j).val k) H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

include hH hb hc

theorem squarefreeBasis_bracket_coefficient_height (x y : Σ a, κ a) (a : SquarefreeIndex ι) (k : ν) :
    RationalHeightLE (e.repr
      (F.squarefreeAlgebraEquiv π ⁅F.squarefreeBasis π b x, F.squarefreeBasis π b y⁆ a).val k)
      (squarefreeBracketHeight (Fintype.card ν) H) := by
  rw [F.squarefreeAlgebraEquiv_apply]
  change RationalHeightLE (e.repr (squarefreePolynomialEquiv
    ⁅(F.squarefreeBasis π b x).val, (F.squarefreeBasis π b y).val⁆ a) k) _
  rw [F.squarefreeBasis_monomial, F.squarefreeBasis_monomial]
  by_cases hxy : Disjoint x.1.val.support y.1.val.support
  · rw [squarefreeMonomial_lie_disjoint x.1 y.1 hxy]
    by_cases ha : x.1.disjointAdd y.1 hxy = a
    · subst a
      rw [squarefreePolynomialEquiv_monomial_self]
      exact lie_bracket_coordinate_height e hc _ _ (hb x.1 x.2) (hb y.1 y.2) k
    · rw [squarefreePolynomialEquiv_monomial_ne _ _ ha, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero (squarefreeBracketHeight_pos _ hH)
  · rw [squarefreeMonomial_lie_overlap _ _ hxy, map_zero, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (squarefreeBracketHeight_pos _ hH)

end MultidegreeLieFiltration

end Erdos3

end

end OAI
