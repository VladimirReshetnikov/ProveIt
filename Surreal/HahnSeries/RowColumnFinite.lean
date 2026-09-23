import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Star.BigOperators

/-!
# Row- and column-finite matrices and their Hahn series

This file formalizes `ihs:rf:lem:rcf` and `ihs:rf:prop:algebra` of
`docs/surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex` (Part II).

`ihs:rf:lem:rcf` is proved over an arbitrary commutative semiring `k`, with a `StarRing`
structure for the involution and the inner product, and an arbitrary index type `I`; the
source's `k = ℂ` and the nonemptiness of `I` are not used. The algebra `R_I = RCF_I(k)` is the
subalgebra `rcf k I` of row-finite endomorphisms of `V_I = k^(I) = I →₀ k`; every endomorphism
of `k^(I)` has finite columns (`colFinite_entry`). The matrix of an endomorphism is `entry`, and
`rcfEquiv` is a bijection between `rcf k I` and the set `rcfMatrices k I` of row- and
column-finite matrices under which the product of `rcf k I` is the usual finite row-by-column
product `finMul` (`coe_rcfEquiv_mul`), its unit is the identity matrix, and addition and scalar
multiplication are entrywise. Directly on matrices, `finMul_mem_rcfMatrices`, `finMul_assoc`,
`one_finMul` and `finMul_one` give closure, associativity and the unit laws (the last three for
all column-finite matrices). Conjugate transpose is a `StarRing` and `StarModule` structure on
`rcf k I` (`entry_star`, `coe_rcfEquiv_star`, `conjTranspose_mem_rcfMatrices`). Elements act
on `V_I` by the finite matrix-vector product (`rcf_smul_apply`), the action is faithful
(`faithfulSMul_rcf`, `eq_zero_of_smul_single`), and `⟨Mx, y⟩ = ⟨x, M*y⟩` for the finite-support
inner product `finInner` (`finInner_smul_left`). Every diagonal matrix is row- and
column-finite (`diagonal_mem_rcfMatrices`), as remarked before the lemma.

The algebra and action clauses of `ihs:rf:prop:algebra` are proved for exponents in any
partially ordered cancellative commutative
monoid `Γ`; divisibility is never used, and `Γ` is linearly ordered only for the order inequalities.
`𝒜_rf = (rcf k I)⟦Γ⟧` is an associative unital semiring by Mathlib (a ring when `k` is a
commutative ring, e.g. `k = ℂ`). It is a `K`-algebra, `K = k⟦Γ⟧`, through the coefficientwise
algebra map (`hahnAlgebra`, stated for any possibly noncommutative algebra and registered as an
instance only for `rcf k I`). The coefficientwise conjugate transpose
`(∑ M_γ t^γ)* = ∑ M_γ* t^γ` is a `StarRing` structure (`hahnStarRing`, `coeff_star_hahn`) that
is conjugate-linear over `K` (`star_smul_hahn`). `𝒜_rf` acts on `ℋ_rf = V_I((t^Γ))`, the
`HahnModule Γ (rcf k I) (I →₀ k)`, by convolution; scalar series act through scalar matrices
exactly as in the `K`-vector space `V_I((t^Γ))` (`algebraMap_smul_eq`), every element of
`𝒜_rf` acts `K`-linearly (`smul_algebraMap_smul_comm`, `smul_hahnModule_comm`), the action is
faithful (`hahn_faithfulSMul`), and `v(XY) ≥ v(X) + v(Y)` and `v(Xx) ≥ v(X) + v(x)` hold for
`v = orderTop` (`orderTop_add_le_orderTop_mul`, `orderTop_add_le_orderTop_smul`). The closing
remark that `𝒜_rf` has zero divisors holds as soon as `I` has two distinct indices and `k` is
nontrivial (`exists_ne_zero_mul_eq_zero`). It needs that hypothesis: for a singleton `I` the
algebra `𝒜_rf` is isomorphic to `K`, which has no zero divisors when `k` is a field and `Γ` is
linearly ordered (as in the source).

The mapped algebra, action, involution and order clauses are proved, including the zero-divisor
remark with `|I| ≥ 2`, now required by the revised source. The source's singleton identification
is not yet formalized as an equivalence. The inner product on `ℋ_rf` (`ihs:rf:prop:inner`) and strong-sum
compatibility (`ihs:rf:lem:strongaction`) are not formalized here.
-/

namespace Surreal.RowColumnFinite

open Finsupp
open scoped Matrix HahnSeries

noncomputable section

section Matrices

variable {k I : Type*}

/-- Every row of `M` has finite support. -/
def RowFinite [Zero k] (M : Matrix I I k) : Prop :=
  ∀ i, (Function.support (M i)).Finite

/-- Every column of `M` has finite support. -/
def ColFinite [Zero k] (M : Matrix I I k) : Prop :=
  ∀ j, (Function.support fun i => M i j).Finite

variable (k I) in
/-- The set `RCF_I(k)` of row- and column-finite matrices. -/
def rcfMatrices [Zero k] : Set (Matrix I I k) :=
  {M | RowFinite M ∧ ColFinite M}

/-- The usual row-by-column product `(MN)ᵢⱼ = ∑ₗ MᵢₗNₗⱼ`, as a finite sum (`finsum`). -/
def finMul [NonUnitalNonAssocSemiring k] (M N : Matrix I I k) : Matrix I I k :=
  fun i j => ∑ᶠ l, M i l * N l j

/-- The usual matrix-vector product `(Mx)ᵢ = ∑ⱼ Mᵢⱼxⱼ`, as a finite sum (`finsum`). -/
def finMulVec [NonUnitalNonAssocSemiring k] (M : Matrix I I k) (x : I → k) : I → k :=
  fun i => ∑ᶠ j, M i j * x j

theorem colFinite_conjTranspose [AddMonoid k] [StarAddMonoid k] {M : Matrix I I k}
    (hM : RowFinite M) : ColFinite Mᴴ := by
  intro j
  refine (hM j).subset fun i hi => ?_
  simpa only [Function.mem_support, Matrix.conjTranspose_apply, ne_eq, star_eq_zero] using hi

theorem rowFinite_conjTranspose [AddMonoid k] [StarAddMonoid k] {M : Matrix I I k}
    (hM : ColFinite M) : RowFinite Mᴴ := by
  intro i
  refine (hM i).subset fun j hj => ?_
  simpa only [Function.mem_support, Matrix.conjTranspose_apply, ne_eq, star_eq_zero] using hj

/-- Every diagonal matrix is row- and column-finite, however large its entries are. -/
theorem diagonal_mem_rcfMatrices [Zero k] [DecidableEq I] (d : I → k) :
    Matrix.diagonal d ∈ rcfMatrices k I := by
  refine ⟨fun i => (Set.finite_singleton i).subset fun j hj => ?_,
    fun j => (Set.finite_singleton j).subset fun i hi => ?_⟩
  · by_contra h
    exact hj (Matrix.diagonal_apply_ne d (Ne.symm h))
  · by_contra h
    exact hi (Matrix.diagonal_apply_ne d h)

/-- Conjugate transpose interchanges the two finiteness conditions. -/
theorem conjTranspose_mem_rcfMatrices [AddMonoid k] [StarAddMonoid k] {M : Matrix I I k}
    (hM : M ∈ rcfMatrices k I) : Mᴴ ∈ rcfMatrices k I :=
  ⟨rowFinite_conjTranspose hM.2, colFinite_conjTranspose hM.1⟩

/-- Conjugating an entry of a finite row-by-column product reverses the factors. -/
theorem star_finMul_apply [NonUnitalSemiring k] [StarRing k] (M N : Matrix I I k)
    (hN : ColFinite N) (i j : I) : star (finMul M N i j) = finMul Nᴴ Mᴴ j i := by
  have hs : (Function.support fun l => M i l * N l j) ⊆ ((hN j).toFinset : Set I) := by
    intro l hl
    rw [Set.Finite.coe_toFinset]
    exact right_ne_zero_of_mul hl
  have hs' : (Function.support fun l => Nᴴ j l * Mᴴ l i) ⊆ ((hN j).toFinset : Set I) := by
    intro l hl
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    have := left_ne_zero_of_mul hl
    rwa [Matrix.conjTranspose_apply, ne_eq, star_eq_zero] at this
  show star (∑ᶠ l, M i l * N l j) = ∑ᶠ l, Nᴴ j l * Mᴴ l i
  rw [finsum_eq_sum_of_support_subset _ hs, finsum_eq_sum_of_support_subset _ hs', star_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [star_mul, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]

end Matrices

section Endomorphisms

variable (k I : Type*) [CommSemiring k]

/-- The matrix of an endomorphism of `k^(I)`: its `(i, j)` entry is coordinate `i` of the image
of the standard vector `e_j`. -/
def entry (F : Module.End k (I →₀ k)) : Matrix I I k :=
  fun i j => F (single j 1) i

variable {k I}

theorem entry_apply (F : Module.End k (I →₀ k)) (i j : I) :
    entry k I F i j = F (single j 1) i := rfl

/-- Every endomorphism of `k^(I)` has finite columns. -/
theorem colFinite_entry (F : Module.End k (I →₀ k)) : ColFinite (entry k I F) :=
  fun j => (F (single j 1)).hasFiniteSupport

theorem apply_single_apply (F : Module.End k (I →₀ k)) (j : I) (a : k) (i : I) :
    F (single j a) i = entry k I F i j * a := by
  rw [← smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

/-- An endomorphism acts on a finitely supported vector by the finite matrix-vector product. -/
theorem apply_apply_eq_sum (F : Module.End k (I →₀ k)) (x : I →₀ k) (i : I) :
    F x i = x.sum fun j a => entry k I F i j * a := by
  conv_lhs => rw [← sum_single x]
  rw [map_finsuppSum, Finsupp.sum_apply]
  exact Finsupp.sum_congr fun j _ => apply_single_apply F j _ i

theorem apply_apply_eq_finMulVec (F : Module.End k (I →₀ k)) (x : I →₀ k) (i : I) :
    F x i = finMulVec (entry k I F) x i := by
  rw [apply_apply_eq_sum, Finsupp.sum]
  refine (finsum_eq_sum_of_support_subset _ fun j hj => ?_).symm
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h
  exact hj (by simp only [h, mul_zero])

/-- The matrix of a composite is the finite row-by-column product of the matrices. -/
theorem entry_mul (F G : Module.End k (I →₀ k)) :
    entry k I (F * G) = finMul (entry k I F) (entry k I G) := by
  ext i j
  rw [entry_apply, Module.End.mul_apply, apply_apply_eq_finMulVec]
  rfl

theorem entry_one [DecidableEq I] : entry k I 1 = 1 := by
  ext i j
  rw [entry_apply, Module.End.one_apply, single_apply, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

@[simp] theorem entry_add (F G : Module.End k (I →₀ k)) :
    entry k I (F + G) = entry k I F + entry k I G := rfl

@[simp] theorem entry_smul (c : k) (F : Module.End k (I →₀ k)) :
    entry k I (c • F) = c • entry k I F := rfl

@[simp] theorem entry_zero : entry k I 0 = 0 := rfl

/-- An endomorphism of `k^(I)` is determined by its matrix. -/
theorem entry_injective : Function.Injective (entry k I) := by
  intro F G h
  refine LinearMap.ext fun x => Finsupp.ext fun i => ?_
  rw [apply_apply_eq_sum, apply_apply_eq_sum, h]

/-- Column `j` of a column-finite matrix, as a finitely supported vector. -/
def column (M : Matrix I I k) (hM : ColFinite M) (j : I) : I →₀ k :=
  Finsupp.ofSupportFinite (fun i => M i j) (hM j)

/-- The endomorphism of `k^(I)` whose columns are those of a column-finite matrix. -/
def ofMatrix (M : Matrix I I k) (hM : ColFinite M) : Module.End k (I →₀ k) :=
  Finsupp.linearCombination k (column M hM)

@[simp] theorem entry_ofMatrix (M : Matrix I I k) (hM : ColFinite M) :
    entry k I (ofMatrix M hM) = M := by
  ext i j
  rw [entry_apply, ofMatrix, linearCombination_single, one_smul, column, ofSupportFinite_coe]

/-- A column-finite matrix sends finitely supported vectors to finitely supported vectors, by the
finite matrix-vector product. -/
theorem finMulVec_eq_ofMatrix_apply (M : Matrix I I k) (hM : ColFinite M) (x : I →₀ k) :
    finMulVec M x = ⇑(ofMatrix M hM x) := by
  funext i
  rw [apply_apply_eq_finMulVec, entry_ofMatrix]

/-- On column-finite matrices the finite row-by-column product is associative. -/
theorem finMul_assoc {M N P : Matrix I I k} (hM : ColFinite M) (hN : ColFinite N)
    (hP : ColFinite P) : finMul (finMul M N) P = finMul M (finMul N P) := by
  have h := congrArg (entry k I) (mul_assoc (ofMatrix M hM) (ofMatrix N hN) (ofMatrix P hP))
  simpa only [entry_mul, entry_ofMatrix] using h

/-- The identity matrix is a left unit for the finite product of column-finite matrices. -/
theorem one_finMul [DecidableEq I] {M : Matrix I I k} (hM : ColFinite M) :
    finMul 1 M = M := by
  have h := congrArg (entry k I) (one_mul (ofMatrix M hM))
  rwa [entry_mul, entry_one, entry_ofMatrix] at h

/-- The identity matrix is a right unit for the finite product of column-finite matrices. -/
theorem finMul_one [DecidableEq I] {M : Matrix I I k} (hM : ColFinite M) :
    finMul M 1 = M := by
  have h := congrArg (entry k I) (mul_one (ofMatrix M hM))
  rwa [entry_mul, entry_one, entry_ofMatrix] at h

variable (k I) in
/-- `ihs:rf:lem:rcf`, algebra structure: `R_I = RCF_I(k)`, realized as the unital subalgebra of
row-finite endomorphisms of `V_I = k^(I)`; every endomorphism of `k^(I)` has finite columns
(`colFinite_entry`), and `rcfEquiv` identifies `rcf k I` with the row- and column-finite
matrices under the finite row-by-column product. -/
def rcf : Subalgebra k (Module.End k (I →₀ k)) where
  carrier := {F | RowFinite (entry k I F)}
  mul_mem' {F G} hF hG i := by
    refine ((hF i).biUnion fun l _ => hG l).subset fun j hj => ?_
    have hj' : (G (single j 1)).sum (fun l a => entry k I F i l * a) ≠ 0 := by
      rw [← apply_apply_eq_sum]
      exact hj
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj'
    exact Set.mem_biUnion (left_ne_zero_of_mul hl) (right_ne_zero_of_mul hl)
  add_mem' {F G} hF hG i := ((hF i).union (hG i)).subset (Function.support_add _ _)
  algebraMap_mem' c i := (Set.finite_singleton i).subset fun j hj => by
    by_contra hji
    apply hj
    rw [entry_apply, Module.algebraMap_end_apply, Finsupp.smul_apply,
      single_eq_of_ne (Ne.symm hji), smul_zero]

theorem mem_rcf_iff (F : Module.End k (I →₀ k)) :
    F ∈ rcf k I ↔ entry k I F ∈ rcfMatrices k I :=
  ⟨fun h => ⟨h, colFinite_entry F⟩, fun h => h.1⟩

theorem rowFinite_entry (F : rcf k I) : RowFinite (entry k I F) := F.2

theorem rcf_ext {F G : rcf k I} (h : entry k I F = entry k I G) : F = G :=
  Subtype.ext (entry_injective h)

theorem ofMatrix_mem_rcf {M : Matrix I I k} (hM : M ∈ rcfMatrices k I) :
    ofMatrix M hM.2 ∈ rcf k I := by
  rw [mem_rcf_iff, entry_ofMatrix]
  exact hM

/-- The bijection between `R_I` and the set of row- and column-finite matrices. -/
def rcfEquiv : rcf k I ≃ rcfMatrices k I where
  toFun F := ⟨entry k I F, (mem_rcf_iff _).1 F.2⟩
  invFun M := ⟨ofMatrix M.1 M.2.2, ofMatrix_mem_rcf M.2⟩
  left_inv _ := Subtype.ext (entry_injective (entry_ofMatrix _ _))
  right_inv _ := Subtype.ext (entry_ofMatrix _ _)

@[simp] theorem coe_rcfEquiv (F : rcf k I) : (rcfEquiv F : Matrix I I k) = entry k I F := rfl

/-- Under `rcfEquiv`, the product of `R_I` is the finite row-by-column product. -/
theorem coe_rcfEquiv_mul (F G : rcf k I) :
    (rcfEquiv (F * G) : Matrix I I k) = finMul (rcfEquiv F : Matrix I I k) (rcfEquiv G) :=
  entry_mul _ _

/-- Under `rcfEquiv`, the unit of `R_I` is the identity matrix. -/
theorem coe_rcfEquiv_one [DecidableEq I] : (rcfEquiv (1 : rcf k I) : Matrix I I k) = 1 :=
  entry_one

theorem coe_rcfEquiv_add (F G : rcf k I) :
    (rcfEquiv (F + G) : Matrix I I k) = (rcfEquiv F : Matrix I I k) + rcfEquiv G := rfl

theorem coe_rcfEquiv_smul (c : k) (F : rcf k I) :
    (rcfEquiv (c • F) : Matrix I I k) = c • (rcfEquiv F : Matrix I I k) := rfl

/-- `RCF_I(k)` is closed under the finite row-by-column product. -/
theorem finMul_mem_rcfMatrices {M N : Matrix I I k} (hM : M ∈ rcfMatrices k I)
    (hN : N ∈ rcfMatrices k I) : finMul M N ∈ rcfMatrices k I := by
  have h := (mem_rcf_iff _).1 (mul_mem (ofMatrix_mem_rcf hM) (ofMatrix_mem_rcf hN))
  rwa [entry_mul, entry_ofMatrix, entry_ofMatrix] at h

/-- `R_I` acts on `V_I` by evaluating the endomorphism. -/
theorem rcf_smul_def (F : rcf k I) (x : I →₀ k) : F • x = (F : Module.End k (I →₀ k)) x := rfl

/-- Every element of `R_I` acts on `V_I` by the finite matrix-vector product. -/
theorem rcf_smul_apply (F : rcf k I) (x : I →₀ k) (i : I) :
    (F • x) i = finMulVec (entry k I F) x i :=
  apply_apply_eq_finMulVec _ _ _

/-- `ihs:rf:lem:rcf`, faithfulness: `R_I` acts faithfully on `V_I`. -/
theorem faithfulSMul_rcf : FaithfulSMul (rcf k I) (I →₀ k) :=
  ⟨fun h => Subtype.ext (LinearMap.ext h)⟩

/-- An element of `R_I` acting as zero on every standard vector is zero. -/
theorem eq_zero_of_smul_single (F : rcf k I) (h : ∀ j : I, F • single j (1 : k) = 0) :
    F = 0 :=
  rcf_ext (by
    ext i j
    rw [entry_apply, ← rcf_smul_def, h]
    rfl)

/-- The coordinate projection `x ↦ xᵢ eᵢ`, the matrix unit `E_{ii}`. -/
def coordProj (i : I) : rcf k I :=
  ⟨Finsupp.lsingle i ∘ₗ Finsupp.lapply i, fun a =>
    (Set.finite_singleton i).subset fun b hb => by
      by_contra h
      apply hb
      rw [entry_apply, LinearMap.comp_apply, Finsupp.lapply_apply, Finsupp.lsingle_apply,
        single_eq_of_ne (Ne.symm h), single_zero, Finsupp.zero_apply]⟩

theorem coordProj_smul (i : I) (x : I →₀ k) : (coordProj i : rcf k I) • x = single i (x i) :=
  rfl

theorem coordProj_mul_coordProj {i j : I} (hij : i ≠ j) : coordProj (k := k) i * coordProj j = 0 :=
  Subtype.ext (LinearMap.ext fun x => by
    change single i (single j (x j) i) = 0
    rw [single_eq_of_ne hij, single_zero])

theorem coordProj_ne_zero [Nontrivial k] (i : I) : coordProj (k := k) i ≠ 0 := by
  intro h
  have := congrArg (fun F : rcf k I => (F • single i (1 : k)) i) h
  simp only [coordProj_smul, single_eq_same, zero_smul, Finsupp.zero_apply] at this
  exact one_ne_zero this

section Star

variable [StarRing k]

/-- Conjugate transpose on `R_I`. -/
instance : Star (rcf k I) where
  star F := ⟨ofMatrix (entry k I F)ᴴ (colFinite_conjTranspose (rowFinite_entry F)), by
    rw [mem_rcf_iff, entry_ofMatrix]
    exact ⟨rowFinite_conjTranspose (colFinite_entry _),
      colFinite_conjTranspose (rowFinite_entry F)⟩⟩

/-- The involution of `R_I` is the conjugate transpose. -/
theorem entry_star (F : rcf k I) : entry k I (star F : rcf k I) = (entry k I F)ᴴ :=
  entry_ofMatrix _ _

theorem coe_rcfEquiv_star (F : rcf k I) :
    (rcfEquiv (star F) : Matrix I I k) = (rcfEquiv F : Matrix I I k)ᴴ :=
  entry_star F

/-- `ihs:rf:lem:rcf`, involution: conjugate transpose makes `R_I` a `*`-ring. -/
instance : StarRing (rcf k I) where
  star_involutive F := rcf_ext (by
    rw [entry_star, entry_star, Matrix.conjTranspose_conjTranspose])
  star_mul F G := rcf_ext (by
    rw [entry_star, Subalgebra.coe_mul, Subalgebra.coe_mul, entry_mul, entry_mul, entry_star,
      entry_star]
    ext i j
    rw [Matrix.conjTranspose_apply, star_finMul_apply _ _ (colFinite_entry _)])
  star_add F G := rcf_ext (by
    rw [entry_star, Subalgebra.coe_add, Subalgebra.coe_add, entry_add, entry_add, entry_star,
      entry_star, Matrix.conjTranspose_add])

/-- The conjugate transpose is conjugate-linear. -/
instance : StarModule k (rcf k I) where
  star_smul c F := rcf_ext (by
    rw [entry_star, Subalgebra.coe_smul, Subalgebra.coe_smul, entry_smul, entry_smul, entry_star,
      Matrix.conjTranspose_smul])

/-- The ordinary finite-support inner product `⟨x, y⟩ = ∑ᵢ star xᵢ * yᵢ` on `V_I = k^(I)`,
conjugate-linear in `x` and linear in `y`. -/
def finInner (x y : I →₀ k) : k :=
  x.sum fun i a => star a * y i

theorem finInner_eq_finsum (x y : I →₀ k) : finInner x y = ∑ᶠ i, star (x i) * y i := by
  rw [finInner, Finsupp.sum]
  refine (finsum_eq_sum_of_support_subset _ fun i hi => ?_).symm
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h
  exact hi (by simp only [h, star_zero, zero_mul])

@[simp] theorem finInner_zero_left (y : I →₀ k) : finInner 0 y = 0 :=
  Finsupp.sum_zero_index

@[simp] theorem finInner_zero_right (x : I →₀ k) : finInner x 0 = 0 := by
  simp [finInner]

theorem finInner_add_left (x x' y : I →₀ k) :
    finInner (x + x') y = finInner x y + finInner x' y :=
  Finsupp.sum_add_index' (fun _ => by rw [star_zero, zero_mul])
    fun _ _ _ => by rw [star_add, add_mul]

theorem finInner_add_right (x y y' : I →₀ k) :
    finInner x (y + y') = finInner x y + finInner x y' := by
  simp only [finInner, Finsupp.add_apply, mul_add, Finsupp.sum_add]

theorem finInner_single_left (j : I) (a : k) (y : I →₀ k) :
    finInner (single j a) y = star a * y j :=
  Finsupp.sum_single_index (by rw [star_zero, zero_mul])

theorem finInner_single_right (x : I →₀ k) (i : I) (b : k) :
    finInner x (single i b) = star (x i) * b := by
  rw [finInner, Finsupp.sum, Finset.sum_eq_single i]
  · rw [single_eq_same]
  · intro j _ hji
    rw [single_eq_of_ne hji, mul_zero]
  · intro hi
    rw [Finsupp.notMem_support_iff.1 hi, star_zero, zero_mul]

/-- `ihs:rf:lem:rcf`, adjoint identity: `⟨Mx, y⟩ = ⟨x, M*y⟩` for the finite-support inner
product. -/
theorem finInner_smul_left (F : rcf k I) (x y : I →₀ k) :
    finInner (F • x) y = finInner x (star F • y) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [smul_zero, finInner_zero_left, finInner_zero_left]
  | add x x' hx hx' => rw [smul_add, finInner_add_left, finInner_add_left, hx, hx']
  | single j a =>
    induction y using Finsupp.induction_linear with
    | zero => rw [smul_zero, finInner_zero_right, finInner_zero_right]
    | add y y' hy hy' => rw [smul_add, finInner_add_right, finInner_add_right, hy, hy']
    | single i b =>
      rw [finInner_single_right, finInner_single_left, rcf_smul_def, rcf_smul_def,
        apply_single_apply, apply_single_apply, entry_star, Matrix.conjTranspose_apply, star_mul,
        mul_assoc]

end Star

end Endomorphisms

section HahnStar

variable {Γ A : Type*} [PartialOrder Γ]

/-- The coefficientwise involution `(∑ M_γ t^γ)* = ∑ M_γ* t^γ`. -/
def hahnStar [AddMonoid A] [StarAddMonoid A] (X : A⟦Γ⟧) : A⟦Γ⟧ where
  coeff g := star (X.coeff g)
  isPWO_support' := X.isPWO_support.mono fun g hg => by
    simpa only [Function.mem_support, ne_eq, star_eq_zero, HahnSeries.mem_support] using hg

variable [AddMonoid A] [StarAddMonoid A]

@[simp] theorem coeff_hahnStar (X : A⟦Γ⟧) (g : Γ) : (hahnStar X).coeff g = star (X.coeff g) :=
  rfl

@[simp] theorem support_hahnStar (X : A⟦Γ⟧) : (hahnStar X).support = X.support := by
  ext g
  simp only [HahnSeries.mem_support, coeff_hahnStar, ne_eq, star_eq_zero]

theorem hahnStar_hahnStar (X : A⟦Γ⟧) : hahnStar (hahnStar X) = X := by
  ext g
  rw [coeff_hahnStar, coeff_hahnStar, star_star]

theorem hahnStar_add (X Y : A⟦Γ⟧) : hahnStar (X + Y) = hahnStar X + hahnStar Y := by
  ext g
  rw [coeff_hahnStar, HahnSeries.coeff_add, HahnSeries.coeff_add, coeff_hahnStar, coeff_hahnStar,
    star_add]

end HahnStar

section Hahn

variable {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

section AlgebraStructure

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/-- Coefficientwise `algebraMap R A`, as a ring homomorphism `R⟦Γ⟧ →+* A⟦Γ⟧`. -/
def hahnMap : R⟦Γ⟧ →+* A⟦Γ⟧ where
  toFun x := x.map (algebraMap R A)
  map_zero' := HahnSeries.map_zero (algebraMap R A).toZeroHom
  map_one' := HahnSeries.map_one (algebraMap R A).toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add (algebraMap R A).toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul (algebraMap R A).toNonUnitalRingHom

variable {R A}

@[simp] theorem coeff_hahnMap (c : R⟦Γ⟧) (g : Γ) :
    (hahnMap R A c).coeff g = algebraMap R A (c.coeff g) := rfl

/-- Scalar series are central: `A` need not be commutative, but `Γ` is. -/
theorem hahnMap_mul_comm (c : R⟦Γ⟧) (X : A⟦Γ⟧) : hahnMap R A c * X = X * hahnMap R A c := by
  ext g
  rw [HahnSeries.coeff_mul, HahnSeries.coeff_mul]
  exact Finset.sum_equiv (Equiv.prodComm _ _) (fun _ => Finset.swap_mem_antidiagonal.symm)
    fun ij _ => Algebra.commutes (c.coeff ij.1) (X.coeff ij.2)

variable (R A) in
/-- For a possibly noncommutative `R`-algebra `A`, the Hahn series `A⟦Γ⟧` form an
`R⟦Γ⟧`-algebra through the coefficientwise algebra map. This is not a global instance: for
`A = R` it would differ (propositionally only) from `Algebra.id`. -/
abbrev hahnAlgebra : Algebra (HahnSeries Γ R) (HahnSeries Γ A) :=
  RingHom.toAlgebra' (hahnMap R A) fun c X => hahnMap_mul_comm c X

end AlgebraStructure

/-- The coefficientwise involution reverses products (`Γ` is commutative). -/
theorem hahnStar_mul {A : Type*} [Semiring A] [StarRing A] (X Y : A⟦Γ⟧) :
    hahnStar (X * Y) = hahnStar Y * hahnStar X := by
  ext g
  rw [coeff_hahnStar, HahnSeries.coeff_mul, HahnSeries.coeff_mul, star_sum]
  refine Finset.sum_equiv (Equiv.prodComm _ _) (fun ij => ?_) fun ij _ => ?_
  · simp only [Finset.mem_antidiagonal, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
      support_hahnStar, add_comm ij.2 ij.1]
    tauto
  · rw [star_mul]
    rfl

/-- The coefficientwise involution makes `A⟦Γ⟧` a `*`-ring. -/
abbrev hahnStarRing (A : Type*) [Semiring A] [StarRing A] : StarRing A⟦Γ⟧ where
  star := hahnStar
  star_involutive := hahnStar_hahnStar
  star_mul := hahnStar_mul
  star_add := hahnStar_add

theorem hahnStar_hahnMap {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
    [Algebra R A] [StarModule R A] (c : R⟦Γ⟧) :
    hahnStar (hahnMap R A c) = hahnMap R A (hahnStar c) := by
  ext g
  rw [coeff_hahnStar, coeff_hahnMap, coeff_hahnMap, coeff_hahnStar, algebraMap_star_comm]

/-- Evaluating a Hahn-series operator on a constant vector reads off its coefficients. -/
theorem coeff_smul_single_zero {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (X : R⟦Γ⟧) (v : V) (g : Γ) :
    ((HahnModule.of R).symm (X • HahnModule.of R (HahnSeries.single (0 : Γ) v))).coeff g =
      X.coeff g • v := by
  rw [HahnModule.coeff_smul_right (y := HahnModule.of R (HahnSeries.single (0 : Γ) v))
    (Set.isPWO_singleton 0) HahnSeries.support_single_subset, Finset.sum_eq_single (g, 0)]
  · rw [Equiv.symm_apply_apply, HahnSeries.coeff_single_same]
  · intro ij hij hne
    rw [Finset.mem_vaddAntidiagonal, Set.mem_singleton_iff] at hij
    obtain ⟨-, h2, h3⟩ := hij
    rw [h2, vadd_eq_add, add_zero] at h3
    exact absurd (Prod.ext h3 h2) hne
  · intro hg
    rw [Equiv.symm_apply_apply, HahnSeries.coeff_single_same]
    by_contra hne
    apply hg
    rw [Finset.mem_vaddAntidiagonal, Set.mem_singleton_iff, vadd_eq_add, add_zero]
    exact ⟨left_ne_zero_of_smul hne, rfl, rfl⟩

variable {k I : Type*} [CommSemiring k]

/-- `ihs:rf:prop:algebra`, algebra structure: `𝒜_rf = R_I((t^Γ))` is a `K`-algebra,
`K = k((t^Γ))`, with `K` acting through scalar matrices. -/
instance : Algebra k⟦Γ⟧ (rcf k I)⟦Γ⟧ :=
  hahnAlgebra k (rcf k I)

theorem algebraMap_hahn_apply (c : k⟦Γ⟧) :
    algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ c = hahnMap k (rcf k I) c := rfl

theorem support_algebraMap_hahn_subset (c : k⟦Γ⟧) :
    (algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ c).support ⊆ c.support := by
  intro g hg
  rw [HahnSeries.mem_support] at hg ⊢
  contrapose hg
  rw [algebraMap_hahn_apply, coeff_hahnMap, hg, map_zero]

/-- Scalar Hahn series act on `ℋ_rf = V_I((t^Γ))` through scalar matrices: the action of
`algebraMap c` is the `K`-vector-space action of `c` on `V_I((t^Γ))`. -/
theorem algebraMap_smul_eq (c : k⟦Γ⟧) (v : (I →₀ k)⟦Γ⟧) :
    (HahnModule.of (rcf k I)).symm
        (algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ c • HahnModule.of (rcf k I) v) =
      (HahnModule.of k).symm (c • HahnModule.of k v) := by
  refine HahnSeries.ext (funext fun g => ?_)
  rw [HahnModule.coeff_smul_left (x := algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ c) c.isPWO_support
    (support_algebraMap_hahn_subset c), HahnModule.coeff_smul]
  rfl

/-- `ihs:rf:prop:algebra`, `K`-linearity in operator form: scalar series `algebraMap c` commute
with every `X ∈ 𝒜_rf` acting on `ℋ_rf`. -/
theorem smul_algebraMap_smul_comm (X : (rcf k I)⟦Γ⟧) (c : k⟦Γ⟧)
    (x : HahnModule Γ (rcf k I) (I →₀ k)) :
    X • (algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ c • x) = algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ c • (X • x) := by
  refine (mul_smul X _ x).symm.trans (Eq.trans ?_ (mul_smul _ X x))
  rw [algebraMap_hahn_apply, hahnMap_mul_comm]

/-- `ihs:rf:prop:algebra`, `K`-linearity: every `X ∈ 𝒜_rf` acts `K`-linearly on the
`K`-vector space `ℋ_rf = V_I((t^Γ))`, `X(cv) = c(Xv)`, where `c • v` is the `HahnModule Γ k`
action of `K = k⟦Γ⟧`. -/
theorem smul_hahnModule_comm (X : (rcf k I)⟦Γ⟧) (c : k⟦Γ⟧) (v : (I →₀ k)⟦Γ⟧) :
    X • HahnModule.of (rcf k I) ((HahnModule.of k).symm (c • HahnModule.of k v)) =
      HahnModule.of (rcf k I) ((HahnModule.of k).symm (c • HahnModule.of k
        ((HahnModule.of (rcf k I)).symm (X • HahnModule.of (rcf k I) v)))) := by
  rw [← algebraMap_smul_eq, ← algebraMap_smul_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, smul_algebraMap_smul_comm]

/-- `ihs:rf:prop:algebra`, faithfulness: `𝒜_rf` acts faithfully on `ℋ_rf` by convolution. -/
theorem hahn_faithfulSMul :
    FaithfulSMul (rcf k I)⟦Γ⟧ (HahnModule Γ (rcf k I) (I →₀ k)) := by
  refine ⟨fun {X Y} h => HahnSeries.ext (funext fun g => ?_)⟩
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  have := congrArg (fun x => ((HahnModule.of (rcf k I)).symm x).coeff g)
    (h (HahnModule.of (rcf k I) (HahnSeries.single 0 v)))
  exact (coeff_smul_single_zero X v g).symm.trans (this.trans (coeff_smul_single_zero Y v g))

/-- `ihs:rf:prop:algebra`, zero divisors with the revised source's hypothesis `|I| ≥ 2`:
`𝒜_rf` has zero divisors once `I` has two distinct indices and `k` is nontrivial, so its order
function is not a field valuation. The constant series `E_{ii}` and `E_{jj}` are nonzero with
product zero. -/
theorem exists_ne_zero_mul_eq_zero [Nontrivial k] {i j : I} (hij : i ≠ j) :
    ∃ X Y : (rcf k I)⟦Γ⟧, X ≠ 0 ∧ Y ≠ 0 ∧ X * Y = 0 :=
  ⟨HahnSeries.C (coordProj i), HahnSeries.C (coordProj j),
    HahnSeries.C_ne_zero (coordProj_ne_zero i), HahnSeries.C_ne_zero (coordProj_ne_zero j),
    by rw [← map_mul, coordProj_mul_coordProj hij, map_zero]⟩

section Star

variable [StarRing k]

/-- `ihs:rf:prop:algebra`, involution: `(∑ M_γ t^γ)* = ∑ M_γ* t^γ`. -/
instance : StarRing (rcf k I)⟦Γ⟧ :=
  hahnStarRing (rcf k I)

theorem coeff_star_hahn (X : (rcf k I)⟦Γ⟧) (g : Γ) : (star X).coeff g = star (X.coeff g) := rfl

/-- The involution of `𝒜_rf` is conjugate-linear over `K`, with the coefficientwise conjugation
of `K`. -/
theorem star_smul_hahn (c : k⟦Γ⟧) (X : (rcf k I)⟦Γ⟧) :
    star (c • X) = hahnStar c • star X := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, algebraMap_hahn_apply, algebraMap_hahn_apply]
  change star X * hahnStar (hahnMap k (rcf k I) c) = _
  rw [hahnStar_hahnMap, hahnMap_mul_comm]

end Star

end Hahn

section Order

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  {k I : Type*} [CommSemiring k]

/-- `ihs:rf:prop:algebra`, `v(XY) ≥ v(X) + v(Y)`. -/
theorem orderTop_add_le_orderTop_mul (X Y : (rcf k I)⟦Γ⟧) :
    X.orderTop + Y.orderTop ≤ (X * Y).orderTop :=
  HahnSeries.orderTop_add_le_mul

/-- `ihs:rf:prop:algebra`, `v(Xx) ≥ v(X) + v(x)`. -/
theorem orderTop_add_le_orderTop_smul (X : (rcf k I)⟦Γ⟧)
    (x : HahnModule Γ (rcf k I) (I →₀ k)) :
    X.orderTop + ((HahnModule.of (rcf k I)).symm x).orderTop ≤
      ((HahnModule.of (rcf k I)).symm (X • x)).orderTop :=
  HahnModule.orderTop_vAdd_le_orderTop_smul fun _ _ => rfl

end Order

end

end Surreal.RowColumnFinite
