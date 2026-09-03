import FabiusFunction.SubspaceCount
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrices of a fixed rank over a finite field

This module proves the rank-enumeration theorem: over a finite field `K` with `Q = |K|`, the
number of `m × n` matrices of rank `r` is

`N_{m,n,r}(Q) = [m, r]_Q · [n, r]_Q · |GL_r(K)|`,   `|GL_r(K)| = ∏_{i<r} (Q^r - Q^i)`,

together with the source's "Equivalently" display in cleared, division-free form.

## What is covered

* `card_matrix_rank_eq`: the exact count, in the three-factor shape of the source, for an
  arbitrary pair of finite index types (not merely `Fin m`, `Fin n`) and for **every** `r : ℕ`.
  No hypothesis `r ≤ min m n` is imposed; the degenerate ranges are theorems, true by the
  zero-extension of the Gaussian triangle on one side and by the vanishing factor `Q^m - Q^m`
  in the falling product on the other.
* `card_matrix_rank_mul_prod_pow_sub_pow`: the source's second display

  `N_{m,n,r}(Q) = (∏_{i<r}(Q^m - Q^i)(Q^n - Q^i)) / ∏_{i<r}(Q^r - Q^i)`

  with the division cleared, i.e. `N · ∏_{i<r}(Q^r - Q^i) = ∏_{i<r}(Q^m - Q^i) ·
  ∏_{i<r}(Q^n - Q^i)`, over `ℕ` and unconditional in `r`.
* `gaussianBinomial_mul_gaussianBinomial_mul_prod_pow_sub_pow`: the polynomial shadow of that
  display over an **arbitrary commutative ring** -- at `q = 0`, at roots of unity, in positive
  characteristic -- where the source's quotient has no meaning.
* `card_linearMap_finrank_range_eq` and `card_linearMap_finrank_range_eq_mul`: the underlying
  linear-map count, for an arbitrary finite division ring `K` and arbitrary finite `K`-modules
  `V`, `W`, in place of `K^n` and `K^m`.  As in `SubspaceCount`, the primality of `Q` is never
  used.  Wedderburn's little theorem makes "finite division ring" coextensive with "finite
  field", so the gain here is that the proof never needs Wedderburn, not that new objects are
  covered.
* `card_linearIndependent_range`: Mathlib's `card_linearIndependent` with the hypothesis
  `k ≤ finrank K V` removed (both sides vanish when it fails).
* `card_injective_linearMap`, `kerFibreEquiv`, `card_linearMap_ker_eq`: the fibre data.

The matrix corollaries are stated for a `Field` rather than a division ring only because
`Matrix.rank` is defined over a `CommSemiring` and `Matrix.card_GL_field` is stated for a
`Field`.  That is a Mathlib boundary, not a mathematical one: the two linear-map theorems from
which they are deduced hold over any finite division ring.

## What is NOT covered

* **The source's own proof route.**  The monograph factors a rank-`r` matrix as `A = U V` with
  `U` of full column rank and `V` of full row rank, counts the pairs `(U, V)`, and divides by
  the order of the group `GL_r(K)` acting freely and transitively on the fibres.  Neither the
  existence of that factorization nor the freeness/transitivity of that action is formalized
  here; both are asserted in one sentence in the source and are not proved there either.  The
  substitute argument used below fibres the linear maps `V →ₗ[K] W` of rank `r` over their
  kernels: the fibre over `N` is, by `kerFibreEquiv`, the set of **injective** maps
  `V ⧸ N →ₗ[K] W`, hence the set of independent `r`-tuples of `W`, and the base is counted by
  the already-landed `card_submodule_finrank_eq_gaussianBinomial`.  This is a deliberate
  substitution of argument: it needs no orbit counting and no division, only the honest
  bijections `kerFibreEquiv` and `Equiv.sigmaFiberEquiv`.
* **The displayed fraction as a literal fraction.**  It is replaced by the cleared identity;
  see `card_matrix_rank_mul_prod_pow_sub_pow`.  Read over `ℕ` the source's quotient is exact but
  its exactness is silent in the source, and read as an identity of polynomials in `q` it leaves
  the polynomial ring altogether.
* **The order of `GL_r`.**  It is not reproved: `card_generalLinearGroup_eq_prod_range` merely
  restates Mathlib's `Matrix.card_GL_field` with the product reindexed from `Fin r` to
  `Finset.range r`.  The source likewise states `|GL_r(K)| = ∏_{i<r}(Q^r - Q^i)` inside the
  theorem without proof.

## Main declarations

* `instFiniteLinearMap`: a module of linear maps between finite modules is finite.  Mathlib has
  no such instance, and every `Nat.card_sigma` below needs one.
* `card_linearIndependent_range`, `card_injective_linearMap`.
* `kerFibreEquiv`, `card_linearMap_ker_eq`, `kerOfRank`.
* `card_linearMap_finrank_range_eq`, `card_linearMap_finrank_range_eq_mul`.
* `card_generalLinearGroup_eq_prod_range`.
* `card_matrix_rank_eq`, `card_matrix_rank_mul_prod_pow_sub_pow`.
* `gaussianBinomial_mul_gaussianBinomial_mul_prod_pow_sub_pow`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-- A module of linear maps between two finite modules is finite, since a linear map is
determined by its underlying function.  Mathlib proves the analogous statement for `Submodule`
(by hand, in `SubspaceCount`) but has no instance for `→ₗ`. -/
instance instFiniteLinearMap {R M₁ M₂ : Type*} [Semiring R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [Finite M₁] [Finite M₂] : Finite (M₁ →ₗ[R] M₂) :=
  Finite.of_injective (fun f : M₁ →ₗ[R] M₂ => (f : M₁ → M₂)) LinearMap.coe_injective

section LinearMapCount

variable {K : Type*} [DivisionRing K] [Fintype K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Finite V]
variable {W : Type*} [AddCommGroup W] [Module K W] [Finite W]

/-- **Independent tuples, with no bound on the length.**  Mathlib's `card_linearIndependent`
carries the hypothesis `k ≤ finrank K V`.  It is unnecessary: for `k > finrank K V` there are no
independent `k`-tuples, by `finrank_span_eq_card` and `Submodule.finrank_le`, and the falling
product acquires the vanishing factor at `i = finrank K V`. -/
theorem card_linearIndependent_range (k : ℕ) :
    Nat.card {s : Fin k → V // LinearIndependent K s}
      = ∏ i ∈ Finset.range k,
          (Fintype.card K ^ Module.finrank K V - Fintype.card K ^ i) := by
  rcases le_or_gt k (Module.finrank K V) with hk | hk
  · rw [card_linearIndependent hk]
    exact Fin.prod_univ_eq_prod_range
      (fun i => Fintype.card K ^ Module.finrank K V - Fintype.card K ^ i) k
  · haveI : IsEmpty {s : Fin k → V // LinearIndependent K s} :=
      ⟨fun s => by
        have h1 : Module.finrank K (Submodule.span K (Set.range s.1)) = k := by
          rw [finrank_span_eq_card s.2, Fintype.card_fin]
        have h2 : Module.finrank K (Submodule.span K (Set.range s.1))
            ≤ Module.finrank K V := Submodule.finrank_le _
        omega⟩
    rw [Nat.card_of_isEmpty]
    exact (Finset.prod_eq_zero (Finset.mem_range.mpr hk) (by simp)).symm

/-- A family is independent exactly when the linear map it induces from a basis is injective.
The auxiliary semiring is `ℕ`, not `K`: `Module.Basis.constr` requires `SMulCommClass K S W`,
which fails at `S = K` for a noncommutative `K`. -/
private theorem injective_constr_iff {X : Type*} [AddCommGroup X] [Module K X] {r : ℕ}
    (b : Module.Basis (Fin r) K X) (v : Fin r → W) :
    LinearIndependent K v ↔ Function.Injective (b.constr ℕ v) := by
  constructor
  · intro hv
    exact b.injective_constr_of_linearIndependent hv
  · intro hg
    have hcomp : (⇑(b.constr ℕ v) ∘ ⇑b) = v := by
      funext i
      simp
    have h2 := b.linearIndependent.map' (b.constr ℕ v) (LinearMap.ker_eq_bot.mpr hg)
    rwa [hcomp] at h2

/-- **Injective maps out of an `r`-dimensional module.**  Choosing a basis of the source
identifies them with the independent `r`-tuples of the target, so there are
`∏_{i<r} (Q^{dim W} - Q^i)` of them.  No relation between `r` and `finrank K W` is assumed. -/
theorem card_injective_linearMap {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]
    {r : ℕ} (hX : Module.finrank K X = r) :
    Nat.card {g : X →ₗ[K] W // Function.Injective g}
      = ∏ i ∈ Finset.range r,
          (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ i) := by
  classical
  have b : Module.Basis (Fin r) K X := Module.finBasisOfFinrankEq K X hX
  -- `LinearEquiv.coe_toEquiv` is a `rfl` lemma, so this ascription is a definitional cast.
  have hiff : ∀ v : Fin r → W,
      LinearIndependent K v ↔ Function.Injective ((b.constr ℕ).toEquiv v) := fun v =>
    injective_constr_iff b v
  have e : {v : Fin r → W // LinearIndependent K v} ≃
      {g : X →ₗ[K] W // Function.Injective g} :=
    Equiv.subtypeEquiv (b.constr ℕ).toEquiv hiff
  calc Nat.card {g : X →ₗ[K] W // Function.Injective g}
      = Nat.card {v : Fin r → W // LinearIndependent K v} := Nat.card_congr e.symm
    _ = ∏ i ∈ Finset.range r,
          (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ i) :=
        card_linearIndependent_range r

/-- **The fibre of the kernel map.**  The linear maps `V →ₗ[K] W` with kernel exactly `N` are
the injective linear maps `V ⧸ N →ₗ[K] W`.  This honest bijection is what replaces the source's
"every matrix is counted `|GL_r|` times"; no group action and no division occur. -/
def kerFibreEquiv (N : Submodule K V) :
    {f : V →ₗ[K] W // LinearMap.ker f = N} ≃
      {g : (V ⧸ N) →ₗ[K] W // Function.Injective g} where
  toFun f :=
    ⟨N.liftQ f.1 (le_of_eq f.2.symm),
      LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' N f.1 f.2.symm)⟩
  invFun g :=
    ⟨g.1 ∘ₗ N.mkQ, by
      rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr g.2, Submodule.comap_bot,
        Submodule.ker_mkQ]⟩
  left_inv f := Subtype.ext (Submodule.liftQ_mkQ N f.1 (le_of_eq f.2.symm))
  right_inv g :=
    Subtype.ext (Submodule.linearMap_qext N (Submodule.liftQ_mkQ N (g.1 ∘ₗ N.mkQ) _))

/-- **The fibre count.**  If `N` has codimension `r` in `V`, then exactly
`∏_{i<r} (Q^{dim W} - Q^i)` linear maps `V →ₗ[K] W` have kernel `N`. -/
theorem card_linearMap_ker_eq {N : Submodule K V} {r : ℕ}
    (hN : Module.finrank K N = Module.finrank K V - r) (hr : r ≤ Module.finrank K V) :
    Nat.card {f : V →ₗ[K] W // LinearMap.ker f = N}
      = ∏ i ∈ Finset.range r,
          (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ i) := by
  have hq : Module.finrank K (V ⧸ N) = r := by
    have h := LinearMap.finrank_range_add_finrank_ker N.mkQ
    rw [Submodule.range_mkQ, finrank_top, Submodule.ker_mkQ, hN] at h
    omega
  rw [Nat.card_congr (kerFibreEquiv (W := W) N)]
  exact card_injective_linearMap (W := W) (X := V ⧸ N) hq

/-- The kernel map on rank-`r` linear maps, landing in the Grassmannian of codimension-`r`
subspaces.  Rank-nullity fixes the target, with no bound on `r`: from
`dim (range f) + dim (ker f) = dim V` and `dim (range f) = r` one gets
`dim (ker f) = dim V - r` even when the subtraction truncates. -/
def kerOfRank (r : ℕ) (f : {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r}) :
    {N : Submodule K V // Module.finrank K N = Module.finrank K V - r} :=
  ⟨LinearMap.ker f.1, by
    have h := LinearMap.finrank_range_add_finrank_ker f.1
    have h2 : Module.finrank K (LinearMap.range f.1) = r := f.2
    omega⟩

/-- **The rank-`r` linear maps, counted by the kernel fibration.**  For every finite division
ring `K`, all finite `K`-modules `V`, `W` and every `r : ℕ`,

`#{f : V →ₗ[K] W | dim (range f) = r} = [dim V, r]_Q · ∏_{i<r} (Q^{dim W} - Q^i)`.

The base of the fibration is the Grassmannian of codimension-`r` subspaces of `V`, counted by
`card_submodule_finrank_eq_gaussianBinomial` as `[dim V, dim V - r]_Q`, which
`gaussianBinomial_symm` turns into `[dim V, r]_Q`; the fibres are constant by
`card_linearMap_ker_eq`.  For `r > dim V` both sides vanish. -/
theorem card_linearMap_finrank_range_eq (r : ℕ) :
    Nat.card {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r}
      = gaussianBinomial (Fintype.card K) (Module.finrank K V) r
        * ∏ i ∈ Finset.range r,
            (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ i) := by
  classical
  rcases le_or_gt r (Module.finrank K V) with hr | hr
  · letI : Fintype {N : Submodule K V // Module.finrank K N = Module.finrank K V - r} :=
      Fintype.ofFinite _
    have hfib : ∀ N : {N : Submodule K V // Module.finrank K N = Module.finrank K V - r},
        Nat.card {f : {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r} //
            kerOfRank r f = N}
          = ∏ i ∈ Finset.range r,
              (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ i) := by
      intro N
      have hN : Module.finrank K N.1 = Module.finrank K V - r := N.2
      have hpq : ∀ f : V →ₗ[K] W, LinearMap.ker f = N.1 →
          Module.finrank K (LinearMap.range f) = r := by
        intro f hf
        have h := LinearMap.finrank_range_add_finrank_ker f
        rw [hf] at h
        omega
      have e1 : {f : {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r} //
            kerOfRank r f = N} ≃
          {f : {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r} //
            LinearMap.ker f.1 = N.1} :=
        Equiv.subtypeEquivRight fun _ =>
          ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      have e2 : {f : {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r} //
            LinearMap.ker f.1 = N.1} ≃
          {f : V →ₗ[K] W //
            Module.finrank K (LinearMap.range f) = r ∧ LinearMap.ker f = N.1} :=
        Equiv.subtypeSubtypeEquivSubtypeInter
          (fun f : V →ₗ[K] W => Module.finrank K (LinearMap.range f) = r)
          (fun f : V →ₗ[K] W => LinearMap.ker f = N.1)
      have e3 : {f : V →ₗ[K] W //
            Module.finrank K (LinearMap.range f) = r ∧ LinearMap.ker f = N.1} ≃
          {f : V →ₗ[K] W // LinearMap.ker f = N.1} :=
        Equiv.subtypeEquivRight fun f => ⟨fun h => h.2, fun h => ⟨hpq f h, h⟩⟩
      rw [Nat.card_congr (e1.trans (e2.trans e3))]
      exact card_linearMap_ker_eq (r := r) hN hr
    calc Nat.card {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r}
        = Nat.card (Σ N : {N : Submodule K V // Module.finrank K N = Module.finrank K V - r},
            {f : {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r} //
              kerOfRank r f = N}) :=
          (Nat.card_congr (Equiv.sigmaFiberEquiv
            (kerOfRank (K := K) (V := V) (W := W) r))).symm
      _ = ∑ N : {N : Submodule K V // Module.finrank K N = Module.finrank K V - r},
            Nat.card {f : {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r} //
              kerOfRank r f = N} := Nat.card_sigma
      _ = Nat.card {N : Submodule K V // Module.finrank K N = Module.finrank K V - r}
            * ∏ i ∈ Finset.range r,
                (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ i) := by
          rw [Finset.sum_const_nat (fun N _ => hfib N), Finset.card_univ,
            Nat.card_eq_fintype_card]
      _ = gaussianBinomial (Fintype.card K) (Module.finrank K V) r
            * ∏ i ∈ Finset.range r,
                (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ i) := by
          rw [card_submodule_finrank_eq_gaussianBinomial, gaussianBinomial_symm _ hr]
  · haveI : IsEmpty {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r} :=
      ⟨fun f => by
        have h := LinearMap.finrank_range_add_finrank_ker f.1
        have h2 : Module.finrank K (LinearMap.range f.1) = r := f.2
        omega⟩
    rw [Nat.card_of_isEmpty, gaussianBinomial_eq_zero_of_lt _ hr, zero_mul]

/-- **The three-factor shape of the source, for linear maps.**  For every finite division ring
`K`, all finite `K`-modules `V`, `W` and every `r : ℕ`,

`#{f : V →ₗ[K] W | dim (range f) = r} = [dim W, r]_Q · [dim V, r]_Q · ∏_{i<r} (Q^r - Q^i)`.

Only `gaussianBinomial_nat_mul_prod_pow_sub_pow` separates this from
`card_linearMap_finrank_range_eq`: it rewrites `∏_{i<r}(Q^{dim W} - Q^i)` as
`[dim W, r]_Q · ∏_{i<r}(Q^r - Q^i)`.  For `r > dim W` both sides vanish, the left because the
falling product contains the factor `Q^{dim W} - Q^{dim W}`. -/
theorem card_linearMap_finrank_range_eq_mul (r : ℕ) :
    Nat.card {f : V →ₗ[K] W // Module.finrank K (LinearMap.range f) = r}
      = gaussianBinomial (Fintype.card K) (Module.finrank K W) r
        * gaussianBinomial (Fintype.card K) (Module.finrank K V) r
        * ∏ i ∈ Finset.range r, (Fintype.card K ^ r - Fintype.card K ^ i) := by
  have hQ : 1 < Fintype.card K := Fintype.one_lt_card
  have hQpos : 0 < Fintype.card K := lt_trans Nat.zero_lt_one hQ
  rw [card_linearMap_finrank_range_eq r]
  rcases le_or_gt r (Module.finrank K W) with hm | hm
  · rw [← gaussianBinomial_nat_mul_prod_pow_sub_pow hQpos hm]
    ring
  · have hzero : ∏ i ∈ Finset.range r,
        (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ i) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_range.mpr hm) ?_
      simp
    rw [hzero, gaussianBinomial_eq_zero_of_lt (Fintype.card K) hm]
    ring

end LinearMapCount

section Matrices

variable {K : Type*} [Field K] [Fintype K]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Mathlib's `Matrix.card_GL_field` with the product reindexed from `Fin r` to
`Finset.range r`, which is the shape the source writes `|GL_r(F_Q)| = ∏_{i=0}^{r-1}(Q^r - Q^i)`
in.  The order of `GL_r` is not reproved here. -/
theorem card_generalLinearGroup_eq_prod_range (r : ℕ) :
    Nat.card (Matrix.GeneralLinearGroup (Fin r) K)
      = ∏ i ∈ Finset.range r, (Fintype.card K ^ r - Fintype.card K ^ i) := by
  rw [Matrix.card_GL_field]
  exact Fin.prod_univ_eq_prod_range
    (fun i => Fintype.card K ^ r - Fintype.card K ^ i) r

/-- The rank of a matrix is the dimension of the range of the linear map it induces on the
standard coordinate spaces.  `Matrix.rank` is *defined* as `finrank R (range A.mulVecLin)` and
`Matrix.toLin'` is `mulVecLin` on the nose, so no choice of bases is involved. -/
private theorem finrank_range_toLin'_eq_rank (A : Matrix m n K) :
    Module.finrank K (LinearMap.range (Matrix.toLin' A)) = A.rank := by
  rw [Matrix.toLin'_apply', Matrix.rank]

/-- **Rank enumeration** (`thm:rank-matrices`).  Over a finite field `K` with `Q = |K|`, for
arbitrary finite index types `m`, `n` and **every** `r : ℕ`, the number of `m × n` matrices of
rank `r` is

`N = [|m|, r]_Q · [|n|, r]_Q · |GL_r(K)|`.

The source restricts to `m = Fin m`, `n = Fin n` and gives no range for `r`; the statement is in
fact true verbatim for every `r`, since for `r > |m|` the coefficient `[|m|, r]_Q` vanishes and
so does the count, and symmetrically in `n`, while `r = 0` gives `1 = 1 · 1 · 1`.

The proof is *not* the source's: no rank factorization `A = U V` and no `GL_r`-orbit count
appear.  The matrices are transported along `Matrix.toLin'` to linear maps
`(n → K) →ₗ[K] (m → K)` and counted by `card_linearMap_finrank_range_eq_mul`, which fibres over
kernels. -/
theorem card_matrix_rank_eq (r : ℕ) :
    Nat.card {A : Matrix m n K // A.rank = r}
      = gaussianBinomial (Fintype.card K) (Fintype.card m) r
        * gaussianBinomial (Fintype.card K) (Fintype.card n) r
        * Nat.card (Matrix.GeneralLinearGroup (Fin r) K) := by
  -- `LinearEquiv.coe_toEquiv` is a `rfl` lemma, so this ascription is a definitional cast.
  have hpred : ∀ A : Matrix m n K,
      Module.finrank K
          (LinearMap.range ((Matrix.toLin' (R := K) (m := m) (n := n)).toEquiv A))
        = A.rank := fun A => finrank_range_toLin'_eq_rank A
  have e : {A : Matrix m n K // A.rank = r} ≃
      {f : (n → K) →ₗ[K] (m → K) // Module.finrank K (LinearMap.range f) = r} :=
    Equiv.subtypeEquiv (Matrix.toLin' (R := K) (m := m) (n := n)).toEquiv
      (fun A => by simp only [hpred A])
  have hsrc : Module.finrank K (n → K) = Fintype.card n :=
    Module.finrank_fintype_fun_eq_card K
  have htgt : Module.finrank K (m → K) = Fintype.card m :=
    Module.finrank_fintype_fun_eq_card K
  have hmain := card_linearMap_finrank_range_eq_mul (K := K) (V := (n → K)) (W := (m → K)) r
  rw [hsrc, htgt] at hmain
  rw [Nat.card_congr e, hmain, card_generalLinearGroup_eq_prod_range (K := K) r]

/-- **The "Equivalently" display, with the division cleared.**  The source writes

`N_{m,n,r}(Q) = (∏_{i<r}(Q^m - Q^i)(Q^n - Q^i)) / ∏_{i<r}(Q^r - Q^i)`,

which is correct over `ℕ` for a prime power `Q` but silently asserts exactness of the division.
Multiplying through removes the quotient, and the resulting identity needs no hypothesis on `r`
at all: when `r` exceeds `|m|` or `|n|` both sides are `0`. -/
theorem card_matrix_rank_mul_prod_pow_sub_pow (r : ℕ) :
    Nat.card {A : Matrix m n K // A.rank = r}
        * ∏ i ∈ Finset.range r, (Fintype.card K ^ r - Fintype.card K ^ i)
      = (∏ i ∈ Finset.range r, (Fintype.card K ^ Fintype.card m - Fintype.card K ^ i))
        * ∏ i ∈ Finset.range r, (Fintype.card K ^ Fintype.card n - Fintype.card K ^ i) := by
  have hQ : 1 < Fintype.card K := Fintype.one_lt_card
  have hQpos : 0 < Fintype.card K := lt_trans Nat.zero_lt_one hQ
  rw [card_matrix_rank_eq r, card_generalLinearGroup_eq_prod_range (K := K) r]
  rcases le_or_gt r (Fintype.card m) with hm | hm
  · rcases le_or_gt r (Fintype.card n) with hn | hn
    · rw [← gaussianBinomial_nat_mul_prod_pow_sub_pow hQpos hm,
        ← gaussianBinomial_nat_mul_prod_pow_sub_pow hQpos hn]
      ring
    · have hz : ∏ i ∈ Finset.range r,
          (Fintype.card K ^ Fintype.card n - Fintype.card K ^ i) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_range.mpr hn) ?_
        simp
      rw [hz, gaussianBinomial_eq_zero_of_lt (Fintype.card K) hn]
      ring
  · have hz : ∏ i ∈ Finset.range r,
        (Fintype.card K ^ Fintype.card m - Fintype.card K ^ i) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_range.mpr hm) ?_
      simp
    rw [hz, gaussianBinomial_eq_zero_of_lt (Fintype.card K) hm]
    ring

end Matrices

/-- **The polynomial shadow of the rank-enumeration identity.**  Over every commutative ring and
for `r ≤ a`, `r ≤ b`,

`[a, r]_q · [b, r]_q · (∏_{i<r}(q^r - q^i))² = (∏_{i<r}(q^a - q^i)) · ∏_{i<r}(q^b - q^i)`.

Read over a finite field with `q = Q`, `a = m`, `b = n` this is the source's second display with
the quotient cleared and the left-hand count expanded by `card_matrix_rank_eq`; but no
finiteness, no regularity and no division is involved, so it also holds at `q = 0`, at roots of
unity, in positive characteristic and in the presence of zero divisors -- where the source's
fraction is undefined. -/
theorem gaussianBinomial_mul_gaussianBinomial_mul_prod_pow_sub_pow {R : Type*} [CommRing R]
    (q : R) {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) :
    gaussianBinomial q a r * gaussianBinomial q b r
        * (∏ i ∈ Finset.range r, (q ^ r - q ^ i))
        * ∏ i ∈ Finset.range r, (q ^ r - q ^ i)
      = (∏ i ∈ Finset.range r, (q ^ a - q ^ i))
        * ∏ i ∈ Finset.range r, (q ^ b - q ^ i) := by
  rw [← gaussianBinomial_mul_prod_pow_sub_pow q ha,
    ← gaussianBinomial_mul_prod_pow_sub_pow q hb]
  ring

/-- **The order of the general linear group as a division-free product.**
`∏_{i<n} (qⁿ - qⁱ) = q^{C(n,2)} ∏_{j<n} (q^{j+1} - 1)`.

This holds over an **arbitrary commutative ring**, for an **arbitrary** `q`: there is no
invertibility, nonvanishing or domain hypothesis, and none is needed, because the proof only
factors `qⁿ - qⁱ = qⁱ(q^{n-i} - 1)` and reflects the index.  Over a finite field with `q`
elements the left side is `|GLₙ(F_q)|`, so this exhibits that order as a power of `q` times a
`q`-factorial-like product; at `q = 2` it is the sequence `1, 1, 6, 168, 20160, …`.

Stated here rather than left implicit inside a counting argument because it is the shape other
work needs: identifying a denominator `q^{n²}(q⁻¹;q⁻¹)ₙ`-style prefactor with `|GLₙ|` runs through
exactly this identity. -/
theorem prod_pow_sub_pow_eq_pow_choose_two_mul {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∏ i ∈ Finset.range n, (q ^ n - q ^ i)
      = q ^ n.choose 2 * ∏ j ∈ Finset.range n, (q ^ (j + 1) - 1) := by
  have hfactor : ∀ i ∈ Finset.range n, q ^ n - q ^ i = q ^ i * (q ^ (n - i) - 1) := by
    intro i hi
    have hi' : i ≤ n := (Finset.mem_range.mp hi).le
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi']
  have hrefl : ∏ i ∈ Finset.range n, (q ^ (n - i) - 1)
      = ∏ j ∈ Finset.range n, (q ^ (j + 1) - 1) := by
    rw [← Finset.prod_range_reflect (fun j => q ^ (j + 1) - 1) n]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    congr 2
    omega
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, hrefl,
    Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, Nat.choose_two_right]

end Fabius
