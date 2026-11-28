import Lib.General.LinearAlgebra.GramDeterminant
import New.Reduction.Lattices.Colength
import New.Reduction.Lattices.Heights

/-!
# Twisted lattices

A twisted lattice on a complex vector space `V` is a family of linear maps `Θ_ξ` from `V` to inner
product spaces, one for each twist `ξ`, with a module of integral vectors at every `ι ∣ l` in each
of these spaces, and coordinates on the space for the trivial twist in which the inner product
has a rational matrix. A twist is a member of an index type `T`, the trivial twist is `1`, and for
each prime `l` some twists are called allowed at `l` (`IsAllowed`). A vector of `V` is integral at
`ι ∣ l` if its images for all twists allowed at `l` are (`integralVectors`), while the covolume
refers to the trivial twist alone. An inner product on `V` and its finite dimension are assumed only
from the definition of the number `Z(ξ)` on.

* `New.TwistedLattice.IndexLe`, `New.TwistedLattice.CovolumeLe`, `New.TwistedLattice.volume`: index
  and covolume of a family in `V`, and the number `Z(ξ) = det (Θ_ξ* Θ_ξ)`.
* `New.TwistedLattice.CovolumeLe.norm_map_det_gram_le`, `New.TwistedLattice.CovolumeLe.sumElim`,
  `New.TwistedLattice.norm_det_mul_det_gram_le_one`: conjugates of Gram determinants, adjoining
  vectors, and valuations of Gram determinants.
* `New.TwistedLattice.covolume_add_index_nonneg`: given an allowed twist `ξ_ι` for each `ι`, a
  lower bound for the covolume of a family in terms of its index, the height of `Z(1) / Z(ξ_ι)`,
  and the sizes and denominators of vectors that complete the family to a basis.

Notions from other files:
* `New.PrimePadicIso`: pairs `ι` of a prime `l = ι.prime` and an isomorphism `ι.iso : ℂ ≃ ℚ̄_l`,
  written `ι ∣ l`. A number `x` is integral at `ι` if `‖ι.iso x‖ ≤ 1`.
* `New.HeightLe c y`: the family `y`, with one complex number for each `ι`, has height at most `c`:
  for some `H ≠ 0`, bounds for all `log |σ H|` and for `log ‖ι (H y_ι)‖` at each prime add up to at
  most `c`.
* `New.formGram G v`: the matrix of the products `v_i* G v_k`.

## Relation to the literature

Size-versus-divisibility bounds for a determinant are known in the literature. Related work: Bost,
Algebraic leaves of algebraic foliations over number fields, 2001; Laurent, Linear forms in two
logarithms and interpolation determinants, 1994.
-/

noncomputable section

namespace New

open Finset Matrix Module Real Submodule InnerProductSpace ComplexOrder

namespace PrimePadicIso

variable (ι : PrimePadicIso)

/-- The isomorphism `ῑ`, with `ῑ z = ι z̄`. -/
abbrev conj : PrimePadicIso := ⟨ι.prime, starRingAut.trans ι.iso⟩

/-- The embedding `ℂ → ℂ_l` given by `ι ∣ l`. -/
abbrev place : PadicPlace ι.prime := ⟨complexToCp ι.iso⟩

/-- The valuation ring `𝒪_ι` of the valuation that `ι` induces on `ℂ`. -/
abbrev integers : ValuationSubring ℂ := (NormedField.valuation.comap ι.place.ιₚ).valuationSubring

lemma conj_snd_apply (z : ℂ) : ι.conj.iso z = ι.iso (starRingEnd ℂ z) := rfl

/-- The embedding `ℂ → ℂ_l` given by `ι ∣ l` induces the same absolute value on `ℂ` as `ι`. -/
lemma norm_place (x : ℂ) : ‖ι.place.ιₚ x‖ = ‖ι.iso x‖ := norm_algebraMap' ℂ_[ι.prime] (ι.iso x)

/-- Let `ι` consist of the prime `l = ι.prime` and the isomorphism `ι.iso : ℂ ≃ ℚ̄_l`. If `x`
divides `l ^ j` in the valuation ring `𝒪_ι`, then `‖ι x‖ ≥ l ^ (-j)`. -/
lemma inv_pow_le_norm_of_dvd {x : ι.integers} {j : ℕ} (hx : x ∣ ((ι.prime : ℕ) : ι.integers) ^ j) :
    (((ι.prime : ℕ) : ℝ) ^ j)⁻¹ ≤ ‖ι.iso (x : ℂ)‖ := by
  rw [← norm_place]
  simpa [norm_p_eq_inv, ← NNReal.coe_le_coe] using
    (Valuation.valuationSubring.integers _).le_of_dvd hx

/-- The square matrix `u` over `𝒪_ι` carries the family `y` into `M` with loss `a`: the combinations
`∑ u_ik y_k` lie in `M`, and the valuation of `det u` at `ι` is at most `a`. -/
structure Carries {S W : Type} [Fintype S] [DecidableEq S] [AddCommGroup W] [Module ι.integers W]
    (u : Matrix S S ι.integers) (y : S → W) (M : Submodule ι.integers W) (a : ℝ) : Prop where
  /-- `‖ι (det u)‖ ≥ l ^ (-a)`: the valuation of `det u` at `ι ∣ l` is at most `a`. -/
  le_norm_det : ((ι.prime : ℕ) : ℝ) ^ (-a) ≤ ‖ι.iso (u.det : ℂ)‖
  /-- The combinations `∑ u_ik y_k` lie in `M`. -/
  sum_smul_mem (i : S) : ∑ k : S, u i k • y k ∈ M

/-- Let `ι` consist of a prime `l` and an isomorphism `ℂ ≃ ℚ̄_l`, and let `𝒪_ι = ι.integers` be the
ring of complex numbers `x` with `‖ι x‖ ≤ 1`. If `u` carries `y` into `M` with loss `a` and `u'`
carries `y'` into `M` with loss `a'`, then the block diagonal matrix with blocks `u` and `u'`
carries the union of the two families into `M` with loss `a + a'`. -/
lemma Carries.fromBlocks {ι : PrimePadicIso} {S S' W : Type} [Fintype S] [Fintype S']
    [DecidableEq S] [DecidableEq S'] [AddCommGroup W] [Module ι.integers W]
    {M : Submodule ι.integers W} {u : Matrix S S ι.integers} {u' : Matrix S' S' ι.integers}
    {y : S → W} {y' : S' → W} {a a' : ℝ}
    (hu : ι.Carries u y M a) (hu' : ι.Carries u' y' M a') :
    ι.Carries (fromBlocks u 0 0 u') (Sum.elim y y') M (a + a') := by
  constructor
  · rw [det_fromBlocks_zero₂₁, neg_add, rpow_add (mod_cast ι.prime.prop.pos), MulMemClass.coe_mul,
      map_mul, norm_mul]
    exact mul_le_mul hu.le_norm_det hu'.le_norm_det (by positivity) (norm_nonneg _)
  · rintro (i | i)
    · simpa using hu.sum_smul_mem i
    · simpa using hu'.sum_smul_mem i

end PrimePadicIso

/-- The automorphism `σ'` of `ℂ`, with `σ' z = conj (σ (conj z))`. -/
abbrev conjAut (σ : ℂ ≃+* ℂ) : ℂ ≃+* ℂ := (starRingAut.trans σ).trans starRingAut

/-- A twisted lattice on `V`, with twists `ξ : T` and trivial twist `1`: linear maps `Θ_ξ` to inner
product spaces, in each of them a module of vectors integral at `ι`, such that, if `ξ` is allowed at
the prime of `ι`, products of vectors integral at `ῑ` with vectors integral at `ι` are integral at
`ι`, and coordinates for the trivial twist in which the inner product has a rational matrix. -/
structure TwistedLattice (V T : Type) [AddCommGroup V] [Module ℂ V] [One T] where
  /-- The inner product space for the twist `ξ`. -/
  Space : T → Type
  [normedAddCommGroup (ξ : T) : NormedAddCommGroup (Space ξ)]
  [innerProductSpace (ξ : T) : InnerProductSpace ℂ (Space ξ)]
  /-- The map `Θ_ξ`. -/
  lift (ξ : T) : V →ₗ[ℂ] Space ξ
  /-- The twist `ξ` is allowed at the prime `l`. -/
  IsAllowed : ℕ → T → Prop
  /-- The vectors for the twist `ξ` that are integral at `ι`. -/
  lattice (ξ : T) (ι : PrimePadicIso) : Submodule ι.integers (Space ξ)
  /-- For `ξ` allowed at the prime of `ι`, the product of a vector integral at `ῑ` and a vector
  integral at `ι` is integral at `ι`. -/
  norm_inner_le_one {ξ : T} (ι : PrimePadicIso) (hξ : IsAllowed ι.prime ξ) :
    ∀ φ ∈ lattice ξ ι.conj, ∀ φ' ∈ lattice ξ ι, ‖ι.iso ⟪φ, φ'⟫_ℂ‖ ≤ 1
  /-- The set of coordinates on the space for the trivial twist. -/
  Coord : Type
  [fintypeCoord : Fintype Coord]
  /-- The coordinates of a vector. -/
  coord : Space 1 →ₗ[ℂ] Coord → ℂ
  /-- The rational matrix of the inner product in these coordinates. -/
  gramMatrix : Matrix Coord Coord ℚ
  /-- The matrix defines an inner product on all coordinate vectors. -/
  posDef_gramMatrix : (gramMatrix.map (↑) : Matrix Coord Coord ℂ).PosDef
  /-- The inner product is the one induced from coordinate vectors. -/
  inner_eq (φ φ' : Space 1) : ⟪φ, φ'⟫_ℂ = star (coord φ) ⬝ᵥ gramMatrix.map (↑) *ᵥ coord φ'

namespace TwistedLattice

attribute [instance] normedAddCommGroup innerProductSpace fintypeCoord

section Index

variable {V T : Type} [AddCommGroup V] [Module ℂ V] [One T] (L : TwistedLattice V T)

/-- The vectors of `V` that are integral at `ι ∣ l`: those `y` for which `Θ_ξ y` is integral at `ι`
for every twist `ξ` allowed at `l`. -/
def integralVectors (ι : PrimePadicIso) : Submodule ι.integers V :=
  ⨅ (ξ : T) (_ : L.IsAllowed ι.prime ξ),
    (L.lattice ξ ι).comap ((L.lift ξ).restrictScalars ι.integers)

lemma mem_integralVectors {L : TwistedLattice V T} {ι : PrimePadicIso} {y : V} :
    y ∈ L.integralVectors ι ↔ ∀ ξ : T, L.IsAllowed ι.prime ξ → L.lift ξ y ∈ L.lattice ξ ι := by
  simp [integralVectors]

variable {S S' : Type} [Fintype S] [Fintype S'] [DecidableEq S] [DecidableEq S']

/-- The family `y` has index at most `δ`: there are numbers `δ_l = e l ≥ 0` with `∑ δ_l log l ≤ δ`,
the sum taken over primes, such that for every `ι ∣ l` some matrix over `𝒪_ι` carries the family
into the vectors integral at `ι` with loss `δ_l`. The matrix does not depend on the twist. -/
def IndexLe (y : S → V) (δ : ℝ) : Prop :=
  ∃ e : ℕ → ℝ,
    (∀ l : ℕ, 0 ≤ e l) ∧
    (∀ U : Finset ℕ, (∀ l ∈ U, l.Prime) → ∑ l ∈ U, e l * log l ≤ δ) ∧
    ∀ ι : PrimePadicIso, ∃ u : Matrix S S ι.integers,
      ι.Carries u y (L.integralVectors ι) (e ι.prime)

variable {L}

lemma IndexLe.mono {y : S → V} {δ δ' : ℝ} (hy : L.IndexLe y δ) (hδ : δ ≤ δ') : L.IndexLe y δ' := by
  obtain ⟨e, he_nonneg, he_sum, hu⟩ := hy
  exact ⟨e, he_nonneg, fun U hU ↦ (he_sum U hU).trans hδ, hu⟩

/-- Let `L` be a twisted lattice on `V`. The index does not depend on the numbering of the family:
if `y ∘ f` has index at most `δ` for a bijection `f`, then so has `y`. -/
lemma IndexLe.of_comp_equiv {y : S → V} {δ : ℝ} (f : S' ≃ S) (hy : L.IndexLe (y ∘ f) δ) :
    L.IndexLe y δ := by
  obtain ⟨e, he_nonneg, he_sum, h_carries⟩ := hy
  refine ⟨e, he_nonneg, he_sum, fun ι ↦ ?_⟩
  obtain ⟨u, hu⟩ := h_carries ι
  refine ⟨u.submatrix f.symm f.symm, by simpa using hu.le_norm_det, fun i ↦ ?_⟩
  simpa [← f.sum_comp] using hu.sum_smul_mem (f.symm i)

/-- Let `L` be a twisted lattice on `V`, and let `e l ≥ 0` with `∑ e l log l ≤ δ` over every finite
set of primes. Suppose that for every prime `l` and every `ι ∣ l` (so `l = ι.prime`) the family `y`
lies in an `𝒪_ι`-module `M` all of whose finite families are taken into the vectors integral at `ι`
by matrices with determinant dividing `l ^ j` (`New.ColengthDvd`), where `j ≤ e l`. Then `y` has
index at most `δ` (`IndexLe`): for some `δ_l ≥ 0` with `∑ δ_l log l ≤ δ` and each `ι ∣ l`, a matrix
`u` over `𝒪_ι` with `‖ι (det u)‖ ≥ l ^ (-δ_l)` takes `y` into the vectors integral at `ι`. -/
lemma indexLe_of_colengthDvd {n : ℕ} {y : Fin n → V} {δ : ℝ} {e : ℕ → ℝ}
    (he_nonneg : ∀ l : ℕ, 0 ≤ e l)
    (he_sum : ∀ U : Finset ℕ, (∀ l ∈ U, l.Prime) → ∑ l ∈ U, e l * log l ≤ δ)
    (h_local : ∀ ι : PrimePadicIso, ∃ (j : ℕ) (M : Submodule ι.integers V),
      j ≤ e ι.prime ∧ (∀ i : Fin n, y i ∈ M) ∧ ColengthDvd M (L.integralVectors ι)
        ((ι.prime : ℕ) ^ j)) :
    L.IndexLe y δ := by
  refine ⟨e, he_nonneg, he_sum, fun ι ↦ ?_⟩
  obtain ⟨j, M, hj, hy, h_colength⟩ := h_local ι
  obtain ⟨u, hu_dvd, hu_mem⟩ := h_colength n y hy
  set l : ℕ := (ι.prime : ℕ)
  refine ⟨u, ?_, hu_mem⟩
  calc (l : ℝ) ^ (-e l) ≤ (l : ℝ) ^ (-(j : ℝ)) :=
        rpow_le_rpow_of_exponent_le (mod_cast ι.prime.prop.one_le) (neg_le_neg hj)
    _ = ((l : ℝ) ^ j)⁻¹ := by rw [rpow_neg l.cast_nonneg, rpow_natCast]
    _ ≤ ‖ι.iso (u.det : ℂ)‖ := ι.inv_pow_le_norm_of_dvd hu_dvd

/-- Let `L` be a twisted lattice on `V`. If two families have index at most `δ` and `δ'`, then their
union `Sum.elim y y'` has index at most `δ + δ'`. -/
lemma IndexLe.sumElim {y : S → V} {y' : S' → V} {δ δ' : ℝ} (hy : L.IndexLe y δ)
    (hy' : L.IndexLe y' δ') : L.IndexLe (Sum.elim y y') (δ + δ') := by
  -- Add the numbers `δ_l` and put the two matrices in diagonal blocks.
  obtain ⟨e, he_nonneg, he_sum, h_carries⟩ := hy
  obtain ⟨e', he'_nonneg, he'_sum, h_carries'⟩ := hy'
  refine ⟨e + e', fun l ↦ add_nonneg (he_nonneg l) (he'_nonneg l), fun U hU ↦ ?_, fun ι ↦ ?_⟩
  · simpa [add_mul, sum_add_distrib] using add_le_add (he_sum U hU) (he'_sum U hU)
  · obtain ⟨⟨u, hu⟩, ⟨u', hu'⟩⟩ := h_carries ι, h_carries' ι
    exact ⟨fromBlocks u 0 0 u', hu.fromBlocks hu'⟩

/-- Let `t` be a finite set of indices, and suppose that for each `s ∈ t` every finite family in the
set `A s ⊆ V` has index at most `δ`. Then a finite family `y` with all its members in the union of
these sets has index at most `#t δ`. -/
lemma indexLe_card_mul {y : S → V} {δ : ℝ} {κ : Type} {A : κ → Set V} (t : Finset κ)
    (hA : ∀ s ∈ t, ∀ (n : ℕ) (z : Fin n → V), (∀ i : Fin n, z i ∈ A s) → L.IndexLe z δ)
    (hy : ∀ i : S, ∃ s ∈ t, y i ∈ A s) :
    L.IndexLe y (#t * δ) := by
  induction t using Finset.cons_induction generalizing S with
  | empty =>
    have : IsEmpty S := ⟨fun i ↦ by simpa using hy i⟩
    exact ⟨0, fun _ ↦ le_rfl, by simp, fun ι ↦ ⟨1, by simp, isEmptyElim⟩⟩
  | cons s t hs ih =>
    -- Split the family into the members of `A s` and the rest.
    classical
    let p (i : S) : Prop := y i ∈ A s
    let f : Fin (Fintype.card {i : S // p i}) ≃ {i : S // p i} := (Fintype.equivFin _).symm
    have h_mem : L.IndexLe (fun i : {i : S // p i} ↦ y i) δ :=
      .of_comp_equiv f (hA s (mem_cons_self s t) _ _ fun i ↦ (f i).prop)
    have h_rest : L.IndexLe (fun i : {i : S // ¬p i} ↦ y i) (#t * δ) := by
      refine ih (fun s' hs' ↦ hA s' (mem_cons_of_mem hs')) fun i ↦ ?_
      simpa [i.prop, p] using hy i
    refine .of_comp_equiv (Equiv.sumCompl p) ?_
    rw [card_cons, Nat.cast_succ, add_one_mul, add_comm,
      ← Sum.elim_comp_inl_inr (y ∘ Equiv.sumCompl p)]
    exact h_mem.sumElim h_rest

end Index

section FormGram

variable {I S S' : Type} [Fintype I] (G : Matrix I I ℂ) (v : S → I → ℂ) (w : S' → I → ℂ)

/-- The upper left block of the Gram matrix of the union of `v` and `w` is the Gram matrix
of `v`. -/
lemma toBlocks₁₁_formGram_sumElim : (formGram G (Sum.elim v w)).toBlocks₁₁ = formGram G v := rfl

/-- The lower right block of the Gram matrix of the union of `v` and `w` is the Gram matrix
of `w`. -/
lemma toBlocks₂₂_formGram_sumElim : (formGram G (Sum.elim v w)).toBlocks₂₂ = formGram G w := rfl

end FormGram

section Covolume

variable {V T S : Type} [AddCommGroup V] [Module ℂ V] [One T] (L : TwistedLattice V T)
  [Fintype S] [DecidableEq S]

/-- The coordinates of `σ Θ₁ y`: those of `Θ₁ y`, with `σ` applied to each of them. -/
def conjCoord (σ : ℂ ≃+* ℂ) (y : V) : L.Coord → ℂ := σ ∘ L.coord (L.lift 1 y)

/-- The number `‖Θ₁ y‖_σ² = ⟨σ Θ₁ y, σ Θ₁ y⟩`, with the product given by the rational matrix
`L.gramMatrix` on coordinate vectors. -/
def normSqAt (y : V) (σ : ℂ ≃+* ℂ) : ℝ :=
  (star (L.conjCoord σ y) ⬝ᵥ L.gramMatrix.map (↑) *ᵥ L.conjCoord σ y).re

/-- The family `y` has covolume at most `c`: for every automorphism `σ` of `ℂ` the determinant of
the products `⟨σ Θ₁ y_i, σ Θ₁ y_k⟩`, taken by the rational Gram matrix on the coordinate vectors
`L.conjCoord σ (y i)`, has absolute value at most `exp c`. -/
def CovolumeLe (y : S → V) (c : ℝ) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, ‖(formGram (L.gramMatrix.map (↑)) (L.conjCoord σ ∘ y)).det‖ ≤ exp c

variable {L}

/-- Since the Gram matrix `L.gramMatrix` is rational, `σ ⟪Θ₁ v, Θ₁ w⟫ = ⟨σ' Θ₁ v, σ Θ₁ w⟩`, where
`Θ₁ = L.lift 1` and `σ' = conjAut σ`, with `σ' z = conj (σ (conj z))`; the right side pairs the
coordinate vectors `L.conjCoord` by the Gram matrix. -/
lemma map_inner_lift_one (σ : ℂ ≃+* ℂ) (v w : V) :
    σ ⟪L.lift 1 v, L.lift 1 w⟫_ℂ =
      star (L.conjCoord (conjAut σ) v) ⬝ᵥ L.gramMatrix.map (↑) *ᵥ L.conjCoord σ w := by
  simp [conjCoord, inner_eq, dotProduct, mulVec]

/-- **Gram determinants, conjugates.** Let `L` be a twisted lattice on `V`, with map `Θ₁ = L.lift 1`
for the trivial twist. For an automorphism `τ` of `ℂ`, write `τ Θ₁ v` for the coordinate vector of
`Θ₁ v` with `τ` applied to each coordinate (`conjCoord`); such vectors are paired by the rational
matrix `L.gramMatrix` of the inner product. If `y` has covolume at most `c`, that is,
`|det ⟨τ Θ₁ y_i, τ Θ₁ y_k⟩| ≤ exp c` for all `τ`, then `|σ Gram(1)| ≤ exp c` for every automorphism
`σ`, where `Gram(1) = det ⟨Θ₁ y_i, Θ₁ y_k⟩`. -/
lemma CovolumeLe.norm_map_det_gram_le {y : S → V} {c : ℝ} (hy : L.CovolumeLe y c) (σ : ℂ ≃+* ℂ) :
    ‖σ (gram ℂ (L.lift 1 ∘ y)).det‖ ≤ exp c := by
  -- `σ Gram(1)` is the product of `σ' Θ₁ y₁ ∧ ⋯` and `σ Θ₁ y₁ ∧ ⋯` in the exterior power.
  let G : Matrix L.Coord L.Coord ℂ := L.gramMatrix.map (↑)
  let v : S → L.Coord → ℂ := L.conjCoord (conjAut σ) ∘ y
  let w : S → L.Coord → ℂ := L.conjCoord σ ∘ y
  have h_pair :
      σ (gram ℂ (L.lift 1 ∘ y)).det = (of fun i k : S ↦ star (v i) ⬝ᵥ G *ᵥ w k).det := by
    rw [σ.map_det]
    exact congrArg det (Matrix.ext fun i k ↦ map_inner_lift_one σ (y i) (y k))
  refine le_of_sq_le_sq ?_ (exp_nonneg c)
  rw [h_pair]
  calc _ ≤ ‖(formGram G v).det‖ * ‖(formGram G w).det‖ :=
        norm_det_pairing_sq_le L.posDef_gramMatrix.posSemidef v w
    _ ≤ exp c * exp c := mul_le_mul (hy (conjAut σ)) (hy σ) (norm_nonneg _) (exp_nonneg c)
    _ = exp c ^ 2 := (sq _).symm

/-- Let `L` be a twisted lattice on `V`, with map `Θ₁ = L.lift 1` for the trivial twist. For an
automorphism `σ` of `ℂ`, apply `σ` to the coordinates of `Θ₁ v` and pair the results by the rational
Gram matrix: `L.normSqAt v σ = ‖Θ₁ v‖_σ²` is the product of such a vector with itself, and a family
has covolume at most `c` (`CovolumeLe`) if for every `σ` the determinant of these products of its
members has absolute value at most `exp c`. If `‖Θ₁ z_i‖_σ² ≤ exp h` for all `i` and `σ`, then
`z_1, …, z_n` has covolume at most `n h`. This is Hadamard's inequality. -/
lemma covolumeLe_of_normSqAt_le {n : ℕ} {z : Fin n → V} {h : ℝ}
    (hz : ∀ (i : Fin n) (σ : ℂ ≃+* ℂ), L.normSqAt (z i) σ ≤ exp h) :
    L.CovolumeLe z (n * h) :=
  fun σ ↦ norm_det_formGram_le L.posDef_gramMatrix.posSemidef fun i ↦ hz i σ

/-- **Gram determinants, adjoining vectors.** Let `L` be a twisted lattice on `V`, with map
`Θ₁ = L.lift 1` for the trivial twist. For an automorphism `σ` of `ℂ`, write `σ Θ₁ v` for the
coordinate vector of `Θ₁ v` with `σ` applied to each coordinate (`conjCoord`); such vectors are
paired by the rational matrix `L.gramMatrix` of the inner product. If `y` has covolume at most `c`,
that is, `|det ⟨σ Θ₁ y_i, σ Θ₁ y_k⟩| ≤ exp c` for all `σ`, and
`L.normSqAt (z i) σ = ⟨σ Θ₁ z_i, σ Θ₁ z_i⟩ ≤ exp h` for all `i` and `σ`, then the family `y`
together with `z_1, …, z_n` has covolume at most `c + n h`. This is Fischer's inequality together
with Hadamard's. -/
lemma CovolumeLe.sumElim {y : S → V} {n : ℕ} {z : Fin n → V} {c h : ℝ} (hy : L.CovolumeLe y c)
    (hz : ∀ (i : Fin n) (σ : ℂ ≃+* ℂ), L.normSqAt (z i) σ ≤ exp h) :
    L.CovolumeLe (Sum.elim y z) (c + n * h) := by
  -- Apply Fischer's inequality to the Gram matrix `M` of the union at `σ`.
  intro σ
  rw [Sum.comp_elim]
  set M : Matrix (S ⊕ Fin n) (S ⊕ Fin n) ℂ :=
    formGram (L.gramMatrix.map (↑)) (Sum.elim (L.conjCoord σ ∘ y) (L.conjCoord σ ∘ z))
  calc ‖M.det‖ ≤ ‖M.toBlocks₁₁.det‖ * ‖M.toBlocks₂₂.det‖ :=
        fischer_det_inequality (posSemidef_formGram L.posDef_gramMatrix.posSemidef _)
    _ ≤ exp c * exp (n * h) :=
        mul_le_mul (hy σ) (covolumeLe_of_normSqAt_le hz σ) (norm_nonneg _) (exp_nonneg c)
    _ = exp (c + n * h) := (Real.exp_add _ _).symm

end Covolume

section Twist

variable {V T : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Module.Finite ℂ V] [One T]
  (L : TwistedLattice V T)

/-- The number `Z(ξ) = det (Θ_ξ* Θ_ξ)`, the Gram determinant of the images of an orthonormal basis
of `V`. -/
def volume (ξ : T) : ℂ := (L.lift ξ).normDet ^ 2

variable {L}

/-- If the space `L.Space ξ` for `ξ` has finite dimension, the volume `Z(ξ) = L.volume ξ` is the
determinant of `Θ_ξ* Θ_ξ` on `V`, where `Θ_ξ = L.lift ξ`. -/
lemma volume_eq_det_adjoint_comp (ξ : T) [Module.Finite ℂ (L.Space ξ)] :
    L.volume ξ = ((L.lift ξ).adjoint ∘ₗ L.lift ξ).det := by
  simp [volume, ← LinearMap.normDet_sq]

lemma volume_ne_zero {ξ : T} (h_inj : Function.Injective (L.lift ξ)) : L.volume ξ ≠ 0 := by
  simp [volume, LinearMap.normDet_eq_zero_iff_ker_ne_bot, LinearMap.ker_eq_bot.2 h_inj]

section

omit [Module.Finite ℂ V]

/-- **Gram determinants, valuations.** Let `L` be a twisted lattice on `V` with maps
`Θ_ξ = L.lift ξ`. Let `ι` consist of a prime `l` and an isomorphism `ι.iso : ℂ ≃ ℚ̄_l`, and let
`ῑ z = ι z̄`. Let `ξ` be allowed at `l`. If `u` takes the vectors `Θ_ξ w_i` to vectors integral at
`ι` and `u'` takes them to vectors integral at `ῑ`, then
`‖ι (conj (det u') · Gram(ξ) · det u)‖ ≤ 1`, where `Gram(ξ) = det ⟨Θ_ξ w_i, Θ_ξ w_k⟩`. -/
lemma norm_det_mul_det_gram_le_one {ι : PrimePadicIso} {ξ : T} (hξ : L.IsAllowed ι.prime ξ)
    {S : Type} [Fintype S] [DecidableEq S] {w : S → V} {u u' : Matrix S S ℂ}
    (hu : ∀ i : S, ∑ k : S, u i k • L.lift ξ (w k) ∈ L.lattice ξ ι)
    (hu' : ∀ i : S, ∑ k : S, u' i k • L.lift ξ (w k) ∈ L.lattice ξ ι.conj) :
    ‖ι.conj.iso u'.det‖ * ‖ι.iso (gram ℂ (L.lift ξ ∘ w)).det‖ * ‖ι.iso u.det‖ ≤ 1 := by
  rw [ι.conj_snd_apply]
  exact norm_det_mul_det_gram_mul_det_le_one ι.iso.toRingHom fun i k ↦
    L.norm_inner_le_one ι hξ _ (hu' i) _ (hu k)

/-- Let `L` be a twisted lattice with maps `Θ_ξ = L.lift ξ`, let `ι ∣ l`, and let the twist `ξ` be
allowed at `l`. Let `u` take `y` into `L.integralVectors ι`, and let the vectors `γ Θ_ξ z_i` be
integral at `ι`. Then a matrix `v` with `det v = det u · γ ^ n'` takes
`Θ_ξ y_1, …, Θ_ξ y_n, Θ_ξ z_1, …, Θ_ξ z_n'` to vectors integral at `ι`. -/
lemma exists_matrix_elim_mem_lattice {n n' : ℕ} {y : Fin n → V} {z : Fin n' → V}
    {ι : PrimePadicIso} {ξ : T} (hξ : L.IsAllowed ι.prime ξ) {u : Matrix (Fin n) (Fin n) ι.integers}
    (hu : ∀ i : Fin n, ∑ k : Fin n, u i k • y k ∈ L.integralVectors ι) {γ : ℂ}
    (hz : ∀ i : Fin n', γ • L.lift ξ (z i) ∈ L.lattice ξ ι) :
    ∃ v : Matrix (Fin n ⊕ Fin n') (Fin n ⊕ Fin n') ℂ,
      v.det = u.det * γ ^ n' ∧
      ∀ i : Fin n ⊕ Fin n',
        ∑ k : Fin n ⊕ Fin n', v i k • L.lift ξ (Sum.elim y z k) ∈ L.lattice ξ ι := by
  -- Take the block diagonal matrix with blocks `u` and `γ`.
  have hu_coe : (u.map (↑) : Matrix (Fin n) (Fin n) ℂ).det = u.det :=
    (ι.integers.subtype.map_det u).symm
  refine ⟨fromBlocks (u.map (↑)) 0 0 (γ • 1), by simp [hu_coe], ?_⟩
  rintro (i | i)
  · have h_lift : L.lift ξ (∑ k : Fin n, u i k • y k) ∈ L.lattice ξ ι :=
      mem_integralVectors.1 (hu i) ξ hξ
    simpa [← ValuationSubring.algebraMap_apply] using h_lift
  · simpa [one_apply] using hz i

/-- Let `L` be a twisted lattice with maps `Θ_ξ = L.lift ξ`. Let `l = ι.prime`, so that
`‖ι x‖ = ‖ι.iso x‖` is the `l`-adic absolute value of `x` under `ι.iso : ℂ ≃ ℚ̄_l`, and let
`ῑ z = ι z̄`. Let `ξ` be allowed at `l`, let `u` carry `y` into the vectors integral at `ι` and `u'`
carry `y` into those integral at `ῑ`, both with loss `a`, and let the vectors `γ Θ_ξ z_i` be
integral both at `ι` and at `ῑ`. Then `‖ι (|γ| ^ (2 n') Gram(ξ))‖ ≤ l ^ (2 a)`, where `Gram(ξ)` is
the Gram determinant of the images of `y_1, …, y_n, z_1, …, z_n'` under `Θ_ξ`. -/
lemma norm_pow_mul_det_gram_le {n n' : ℕ} {y : Fin n → V}
    {z : Fin n' → V} {ι : PrimePadicIso} {ξ : T} (hξ : L.IsAllowed ι.prime ξ) {a : ℝ}
    {u : Matrix (Fin n) (Fin n) ι.integers} {u' : Matrix (Fin n) (Fin n) ι.conj.integers}
    (hu : ι.Carries u y (L.integralVectors ι) a)
    (hu' : ι.conj.Carries u' y (L.integralVectors ι.conj) a) {γ : ℂ}
    (hz : ∀ i : Fin n', γ • L.lift ξ (z i) ∈ L.lattice ξ ι)
    (hz' : ∀ i : Fin n', γ • L.lift ξ (z i) ∈ L.lattice ξ ι.conj) :
    ‖ι.iso (((‖γ‖ : ℂ) ^ 2) ^ n' * (gram ℂ (L.lift ξ ∘ Sum.elim y z)).det)‖ ≤
      exp (2 * (a * log ι.prime)) := by
  obtain ⟨v, hv_det, hv_mem⟩ := exists_matrix_elim_mem_lattice hξ hu.sum_smul_mem hz
  obtain ⟨v', hv'_det, hv'_mem⟩ :=
    exists_matrix_elim_mem_lattice (ι := ι.conj) hξ hu'.sum_smul_mem hz'
  set Gram : ℂ := (gram ℂ (L.lift ξ ∘ Sum.elim y z)).det
  have h_int : ‖ι.conj.iso v'.det‖ * ‖ι.iso Gram‖ * ‖ι.iso v.det‖ ≤ 1 :=
    norm_det_mul_det_gram_le_one hξ hv_mem hv'_mem
  set β : ℝ := a * log ι.prime with hβ
  have h_exp : exp (-β) = ((ι.prime : ℕ) : ℝ) ^ (-a) := by
    rw [rpow_def_of_pos (mod_cast ι.prime.prop.pos), mul_neg, mul_comm, hβ]
  have hu_det : exp (-β) ≤ ‖ι.iso (u.det : ℂ)‖ := h_exp.trans_le hu.le_norm_det
  have hu'_det : exp (-β) ≤ ‖ι.conj.iso (u'.det : ℂ)‖ := h_exp.trans_le hu'.le_norm_det
  calc ‖ι.iso (((‖γ‖ : ℂ) ^ 2) ^ n' * Gram)‖
      = ‖ι.conj.iso γ‖ ^ n' * ‖ι.iso Gram‖ * ‖ι.iso γ‖ ^ n' := by
        simp [← Complex.conj_mul', mul_pow, mul_right_comm]
    _ = exp (2 * β) *
          (exp (-β) * ‖ι.conj.iso γ‖ ^ n' * ‖ι.iso Gram‖ * (exp (-β) * ‖ι.iso γ‖ ^ n')) := by
        rw [two_mul, Real.exp_add, Real.exp_neg]
        field_simp
    _ ≤ exp (2 * β) * (‖ι.conj.iso v'.det‖ * ‖ι.iso Gram‖ * ‖ι.iso v.det‖) := by
        simp only [hv_det, hv'_det, map_mul, map_pow, norm_mul, norm_pow]
        gcongr
    _ ≤ exp (2 * β) := mul_le_of_le_one_right (exp_nonneg _) h_int

/-- Let `L` be a twisted lattice with maps `Θ_ξ = L.lift ξ`. Let `y` have index at most `δ`, let
`ξ_ι = θ ι` be allowed at the prime of `ι`, and let the vectors `γ_ι Θ_{ξ_ι} z_i` be integral both
at `ι` and at `ῑ`, where `ῑ z = ι z̄`. Let `Gram(ξ)` be the Gram determinant of the images of
`y_1, …, y_n, z_1, …, z_n'` under `Θ_ξ`. Then the family `x_ι = |γ_ι| ^ (2 n') Gram(ξ_ι)` has height
at most `2 δ` (`New.HeightLe`): for some common `H ≠ 0`, the bounds for `log |σ H|` over
automorphisms `σ` of `ℂ` and for `log ‖ι (H x_ι)‖` at the primes add up to at most `2 δ`. -/
lemma heightLe_pow_mul_det_gram {n n' : ℕ} {y : Fin n → V} {z : Fin n' → V} {δ : ℝ}
    (hδ : L.IndexLe y δ) {θ : PrimePadicIso → T}
    (hθ : ∀ ι : PrimePadicIso, L.IsAllowed ι.prime (θ ι)) {γ : PrimePadicIso → ℂ}
    (hz : ∀ (ι : PrimePadicIso) (i : Fin n'), γ ι • L.lift (θ ι) (z i) ∈ L.lattice (θ ι) ι)
    (hz' : ∀ (ι : PrimePadicIso) (i : Fin n'), γ ι • L.lift (θ ι) (z i) ∈ L.lattice (θ ι) ι.conj) :
    HeightLe (2 * δ) fun ι : PrimePadicIso ↦
      ((‖γ ι‖ : ℂ) ^ 2) ^ n' * (gram ℂ (L.lift (θ ι) ∘ Sum.elim y z)).det := by
  obtain ⟨e, -, he_sum, h_carries⟩ := hδ
  refine .of_le (e := fun l ↦ 2 * (e l * log l)) (fun U hU ↦ ?_) fun ι ↦ ?_
  · simpa [← mul_sum] using he_sum U hU
  · -- Take the matrices of the index at `ι` and at `ῑ`. Both serve for the twist `ξ_ι`, as `ι` and
    -- `ῑ` have the same prime and the matrices do not depend on the twist.
    obtain ⟨⟨u, hu⟩, ⟨u', hu'⟩⟩ := h_carries ι, h_carries ι.conj
    exact norm_pow_mul_det_gram_le (hθ ι) hu hu' (hz ι) (hz' ι)

end

/-- **A twist for each prime.** Let `L` be a twisted lattice on `V` with maps `Θ_ξ = L.lift ξ`, all
injective. Let `y_1, …, y_n, z_1, …, z_n'` be a basis of `V`, and let `ξ_ι = θ ι` be allowed at the
prime of `ι`. Suppose that
* `y` has covolume at most `c` and index at most `δ`;
* `γ(ξ) ≠ 0`, and `γ(ξ) Θ_ξ z_i` is integral at all `ι ∣ l` for `ξ` allowed at `l`;
* `⟨σ Θ₁ z_i, σ Θ₁ z_i⟩ ≤ exp b_short` for all automorphisms `σ` of `ℂ`;
* the families `|γ(ξ_ι)| ^ (-2)` and `Z(1) / Z(ξ_ι)` have height at most `b_denom` and `b_volume`
  respectively.

Then `c + 2 δ + n' (b_short + b_denom) + b_volume ≥ 0`. -/
theorem covolume_add_index_nonneg {n n' : ℕ} {y : Fin n → V} {z : Fin n' → V}
    (h_inj : ∀ ξ : T, Function.Injective (L.lift ξ))
    (h_indep : LinearIndependent ℂ (Sum.elim y z)) (h_card : finrank ℂ V = n + n')
    {θ : PrimePadicIso → T} (hθ : ∀ ι : PrimePadicIso, L.IsAllowed ι.prime (θ ι))
    {c δ b_volume b_short b_denom : ℝ} (hc : L.CovolumeLe y c) (hδ : L.IndexLe y δ)
    {γ : T → ℂ} (hγ_ne : ∀ ξ : T, γ ξ ≠ 0)
    (hz_int : ∀ (i : Fin n') (ι : PrimePadicIso) (ξ : T), L.IsAllowed ι.prime ξ →
      γ ξ • L.lift ξ (z i) ∈ L.lattice ξ ι)
    (hz_short : ∀ (i : Fin n') (σ : ℂ ≃+* ℂ), L.normSqAt (z i) σ ≤ exp b_short)
    (hγ : HeightLe b_denom fun ι : PrimePadicIso ↦ ((‖γ (θ ι)‖ : ℂ) ^ 2)⁻¹)
    (hZ : HeightLe b_volume fun ι : PrimePadicIso ↦ L.volume 1 / L.volume (θ ι)) :
    0 ≤ c + 2 * δ + n' * (b_short + b_denom) + b_volume := by
  -- Write `Gram(1)` as a product of three factors, add their heights, and compare with the
  -- conjugates of `Gram(1)` by the product formula.
  let Gram (ξ : T) : ℂ := (gram ℂ (L.lift ξ ∘ Sum.elim y z)).det
  have h_gram (ξ : T) : Gram ξ = L.volume ξ * (gram ℂ (Sum.elim y z)).det :=
    det_gram_comp (L.lift ξ) _ (by simpa using h_card)
  have h_factor (ι : PrimePadicIso) : Gram 1 = ((‖γ (θ ι)‖ : ℂ) ^ 2) ^ n' * Gram (θ ι) *
      ((‖γ (θ ι)‖ : ℂ) ^ 2)⁻¹ ^ n' * (L.volume 1 / L.volume (θ ι)) := by
    have hγ_norm : (‖γ (θ ι)‖ : ℂ) ≠ 0 := by simpa using hγ_ne (θ ι)
    have hZ_ne : L.volume (θ ι) ≠ 0 := volume_ne_zero (h_inj (θ ι))
    simp [h_gram, field]
  have h_index : HeightLe (2 * δ) fun ι ↦ ((‖γ (θ ι)‖ : ℂ) ^ 2) ^ n' * Gram (θ ι) :=
    heightLe_pow_mul_det_gram hδ hθ (fun ι i ↦ hz_int i ι (θ ι) (hθ ι))
      fun ι i ↦ hz_int i ι.conj (θ ι) (hθ ι)
  have h_height : HeightLe (2 * δ + n' * b_denom + b_volume) fun _ ↦ Gram 1 := by
    simpa only [← h_factor, Pi.mul_def, Pi.pow_def] using (h_index.mul (hγ.pow n')).mul hZ
  have h_ne : Gram 1 ≠ 0 :=
    det_gram_ne_zero_iff_linearIndependent.2 (h_indep.map_injOn _ (h_inj 1).injOn)
  have h_conj (σ : ℂ ≃+* ℂ) : ‖σ (Gram 1)‖ ≤ exp (c + n' * b_short) :=
    (hc.sumElim hz_short).norm_map_det_gram_le σ
  linarith [h_height.neg_le_of_norm_map_le h_ne h_conj]

end Twist

end TwistedLattice

end New

end
