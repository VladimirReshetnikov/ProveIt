import Lib.Base

/-!
# The q-binomial theorem, fibre sums, and Schur polynomials in the coefficients

The q-binomial theorem is proved as a sum over the subspaces of a vector space over a field with `q`
elements. There is a lemma on grouping a finite sum by the fibres of a map. Schur polynomials are
defined without division, as integer polynomials in the coefficients of a monic polynomial; `s_l(r)`
denotes the Schur polynomial with exponent tuple `l`, evaluated at a tuple of roots `r`. Three
algebraic facts serve to extract values of Schur polynomials from vanishing linear forms.

## Main definitions and results

* `New.q_binomial_submodule`: the sum of `New.heckePolyCoeff X U` over the subspaces `U` of `W` is
  `New.SiegelWeil.qPochhammer q (dim W) X`.
* `New.Variety.genericSchur`, `New.Variety.rootCoeffEval`: the Schur polynomial in the coefficients,
  and evaluation at the coefficients of the monic polynomial with a given multiset of roots.
* `New.Variety.rootCoeffEval_genericSchur_mul_det`: the value times the Vandermonde determinant is
  `det (r i ^ l j)`.
* `New.Variety.sum_lagrange_smul_rootCoeffEval`: for distinct elements r₁, …, r_a of a field,
  summing s_l(r₁, …, X rᵢ, …) against the Lagrange factors ∏_{k ≠ i} (X rᵢ − r_k)/(rᵢ − r_k)
  gives s_l(r)·∑ⱼ X^(l j).
* `New.Variety.map_prod_rootCoeffEval_eq_zero`: a linear form that kills the families
  j ↦ ∏_{i, σ} ∏_{t ∈ x(j, σ)} (1 − c(i, σ)(α) t) for all α, with the c(i, σ) algebraically
  independent, kills the products over σ of polynomials of bounded degree in the coefficients of
  ∏_{t ∈ x(j, σ)} (X − t).

## Relation to the literature

Known results: the q-binomial theorem, counted over the subspaces of a finite vector space, and the
bialternant formula for Schur polynomials.
-/

/-! ## The q-binomial theorem over the subspaces of a finite vector space -/

section QBinomial

open Finset Module Submodule

-- Finite types of vectors and of subspaces are summed over through `Fintype.ofFinite`.
attribute [local instance low] Fintype.ofFinite

/-- The product of `1 - q ^ l * X` over `0 ≤ l < m`. For `q` the norm of a split place, it is the
Hecke polynomial of the trivial representation in rank `m`. -/
@[simp]
noncomputable abbrev New.SiegelWeil.qPochhammer (q m : ℕ) (X : ℂ) : ℂ :=
  ∏ l ∈ range m, (1 - (q : ℂ) ^ l * X)

/-- The number `(-X) ^ d * q ^ (d choose 2)` attached to a subspace `U` of `k^n` of dimension `d`,
where `q` is the number of elements of `k`. -/
noncomputable abbrev New.heckePolyCoeff {n k : Type*} [Field k] (X : ℂ) (U : Submodule k (n → k)) :
    ℂ :=
  (-X) ^ finrank k U * (Nat.card k : ℂ) ^ (finrank k U).choose 2

/-- If `W` covers `H` in the lattice of subspaces, then a subspace `U ≤ W` is spanned by `U ⊓ H` and
any vector of `U` outside `H`. -/
lemma New.inf_sup_span_singleton_of_covBy {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {H W U : Submodule k V} (hHW : H ⋖ W) (hU : U ≤ W) {v : V} (hv : v ∈ U) (hvH : v ∉ H) :
    U ⊓ H ⊔ k ∙ v = U := by
  have span_le : k ∙ v ≤ U := by simpa
  have lt_sup : H < H ⊔ k ∙ v := left_lt_sup.2 (by simpa)
  have sup_eq : H ⊔ k ∙ v = W :=
    (hHW.eq_or_eq lt_sup.le (sup_le hHW.le (span_le.trans hU))).resolve_left lt_sup.ne'
  rw [inf_sup_assoc_of_le _ span_le, sup_eq, inf_of_le_left hU]

/-- If `W` covers `H` in the lattice of subspaces, then `U ⊓ H` has codimension one in every
subspace `U ≤ W` that is not contained in `H`. -/
lemma New.finrank_eq_finrank_inf_add_one_of_covBy {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {H W U : Submodule k V} (hHW : H ⋖ W) (hU : U ≤ W)
    (hUH : ¬U ≤ H) : finrank k U = finrank k ↥(U ⊓ H) + 1 := by
  obtain ⟨v, hv, hvH⟩ : ∃ v ∈ U, v ∉ H := Set.not_subset.1 hUH
  rw [← finrank_sup_span_singleton (show v ∉ U ⊓ H by simp [hvH]),
    inf_sup_span_singleton_of_covBy hHW hU hv hvH]

open scoped Classical in
/-- If `W` covers `H` and `v` is a vector of `W` outside `H`, then `U ↦ U ⊓ H` is a bijection from
the subspaces `U ≤ W` containing `v` onto the subspaces of `H`; stated for sums of a function. -/
lemma New.sum_inf_eq_sum_of_covBy {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Fintype (Submodule k V)] {H W : Submodule k V} (hHW : H ⋖ W) {v : V} (hvW : v ∈ W)
    (hvH : v ∉ H) (f : Submodule k V → ℂ) :
    ∑ U : Submodule k V with v ∈ U ∧ U ≤ W, f (U ⊓ H) = ∑ U : Submodule k V with U ≤ H, f U := by
  refine sum_nbij' (fun U ↦ U ⊓ H) (fun U ↦ U ⊔ k ∙ v) ?_ ?_ ?_ ?_ fun U _ ↦ rfl
  · simp
  · simp +contextual [hvW, hHW.le.trans', mem_sup_right]
  · simp +contextual [inf_sup_span_singleton_of_covBy hHW, hvH]
  · simp +contextual [sup_inf_assoc_of_le, (disjoint_span_singleton_of_notMem hvH).symm.eq_bot]

open scoped Classical in
/-- The q-binomial theorem for subspaces: for a subspace `W` of `k^n`, with `n` finite and `k` a
field with `q` elements, and for `X : ℂ`, the sum of `(-X) ^ dim U * q ^ (dim U choose 2)`
(`heckePolyCoeff X U`) over the subspaces `U ≤ W` is `∏ l < dim W, (1 - q ^ l * X)`
(`SiegelWeil.qPochhammer q (dim W) X`).

A variant of the finite q-binomial theorem as in Macdonald, with a sum over subspaces in place of
Gaussian binomial coefficients. -/
lemma New.q_binomial_submodule (n k : Type*) [Finite n] [Field k] [Finite k]
    (W : Submodule k (n → k)) (X : ℂ) :
    ∑ U : Submodule k (n → k) with U ≤ W, heckePolyCoeff X U =
      SiegelWeil.qPochhammer (Nat.card k) (finrank k W) X := by
  -- Induction along a chain of hyperplanes H ⋖ W. A subspace U ≤ W not contained in H is
  -- (U ⊓ H) ⊔ k v for every v in U outside H; count such pairs (U, v) in two ways.
  let q : ℂ := Nat.card k
  have q_ne : q - 1 ≠ 0 := by simp [q, sub_eq_zero, Fintype.one_lt_card.ne']
  let : LocallyFiniteOrder (Submodule k (n → k)) := Fintype.toLocallyFiniteOrder
  induction le_iff_reflTransGen_covBy.1 (OrderBot.bot_le W) with
  | refl => simp [filter_eq', heckePolyCoeff]
  | @tail H W _ hHW ih =>
    -- The vectors of U outside H number q ^ (d + 1) - q ^ d, where d is the rank of U ⊓ H.
    let outsideH (U : Submodule k (n → k)) : Finset (n → k) := Set.toFinset (U \ ↑(U ⊓ H))
    have card_eq (U : Submodule k (n → k)) :
        (#(U : Set (n → k)).toFinset : ℂ) = q ^ finrank k U := by
      simp [q, card_eq_pow_finrank (K := k) (V := U)]
    have card_outsideH {U : Submodule k (n → k)} (hU : U ≤ W) (hUH : ¬U ≤ H) :
        (#(outsideH U) : ℂ) = q ^ finrank k ↥(U ⊓ H) * (q - 1) := by
      simp only [outsideH]
      rw [Set.toFinset_sdiff, cast_card_sdiff (Set.toFinset_mono (SetLike.coe_mono inf_le_left)),
        card_eq, card_eq, finrank_eq_finrank_inf_add_one_of_covBy hHW hU hUH]
      ring
    -- The coefficient of U is -X q ^ d times that of U ⊓ H; spread it evenly over these vectors.
    let weight : ℂ := -X / (q - 1)
    let notInH : Finset (Submodule k (n → k)) := univ.filter (· ≤ W) \ univ.filter (· ≤ H)
    have coeff_eq_sum (U : Submodule k (n → k)) (hU : U ∈ notInH) :
        heckePolyCoeff X U = ∑ v ∈ outsideH U, weight * heckePolyCoeff X (U ⊓ H) := by
      have ⟨hUW, hUH⟩ : U ≤ W ∧ ¬U ≤ H := by simpa [notInH] using hU
      rw [sum_const, nsmul_eq_mul, card_outsideH hUW hUH, heckePolyCoeff, heckePolyCoeff,
        finrank_eq_finrank_inf_add_one_of_covBy hHW hUW hUH, Nat.choose_succ_succ',
        Nat.choose_one_right]
      simp only [weight, q] at q_ne ⊢
      field
    -- For fixed v, the map U ↦ U ⊓ H is a bijection from the U ≤ W containing v onto the U ≤ H.
    have sum_fibre (v : n → k) (hv : v ∈ outsideH W) :
        ∑ U with v ∈ U ∧ U ≤ W, weight * heckePolyCoeff X (U ⊓ H) =
          weight * ∑ U with U ≤ H, heckePolyCoeff X U := by
      obtain ⟨hvW, hvH⟩ : v ∈ W ∧ v ∉ H := by simp_all [outsideH]
      rw [← mul_sum, sum_inf_eq_sum_of_covBy hHW hvW hvH]
    have mem_pairs_iff (U : Submodule k (n → k)) (v : n → k) : U ∈ notInH ∧ v ∈ outsideH U ↔
        U ∈ univ.filter (fun U ↦ v ∈ U ∧ U ≤ W) ∧ v ∈ outsideH W := by
      grind [IsConcreteLE.le_iff, Submodule.mem_inf, SetLike.mem_coe]
    calc ∑ U with U ≤ W, heckePolyCoeff X U
      _ = ∑ v ∈ outsideH W, ∑ U with v ∈ U ∧ U ≤ W, weight * heckePolyCoeff X (U ⊓ H) +
          ∑ U with U ≤ H, heckePolyCoeff X U := by
        rw [← sum_comm' mem_pairs_iff, ← sum_congr rfl coeff_eq_sum,
          sum_sdiff (monotone_filter_right univ fun U _ hU ↦ hU.trans hHW.le)]
      _ = (1 - q ^ finrank k H * X) * ∑ U with U ≤ H, heckePolyCoeff X U := by
        rw [sum_congr rfl sum_fibre, sum_const, nsmul_eq_mul, card_outsideH le_rfl hHW.lt.not_ge,
          inf_of_le_right hHW.le]
        simp only [weight]
        field
      _ = SiegelWeil.qPochhammer (Nat.card k) (finrank k W) X := by
        rw [finrank_eq_finrank_inf_add_one_of_covBy hHW le_rfl hHW.lt.not_ge,
          inf_of_le_right hHW.le, ih, mul_comm, SiegelWeil.qPochhammer, SiegelWeil.qPochhammer,
          prod_range_succ]

end QBinomial

/-! ## Sums over an image grouped by fibres -/

/-- Let `S` be a finite set and `ψ` a map. If for `t ∈ S` the value `F (ψ t)` divided by the size of
the fibre of `ψ` in `S` through `t` is `G t / D`, and `G` has sum zero over `S`, then `F` has sum
zero over `ψ '' S`. -/
lemma New.Variety.finsum_image_eq_zero_of_fibers {T C : Type*} {S : Set T} (hS : S.Finite)
    (ψ : T → C) {G : T → ℂ} {F : C → ℂ} {D : ℂ} (h_sum : ∑ᶠ t ∈ S, G t = 0)
    (h_ratio : ∀ t ∈ S, F (ψ t) / Nat.card {s ∈ S | ψ s = ψ t} = G t / D) :
    ∑ᶠ c ∈ ψ '' S, F c = 0 := by
  classical
  -- Group the sum `∑ G t / D` over `S` by the fibres of `ψ`: the fibre over `c` contributes `F c`.
  lift S to Finset T using hS
  rw_mod_cast [finsum_mem_finset_eq_sum] at h_sum ⊢
  have fibre (t : T) (ht : t ∈ S) : F (ψ t) = ∑ s ∈ S with ψ s = ψ t, G s / D := by
    -- By `h_ratio` the summand is constant on the fibre.
    have const : ∀ s ∈ {s ∈ S | ψ s = ψ t}, G s / D = F (ψ t) / {s ∈ S | ψ s = ψ t}.card := by
      simp +contextual [← h_ratio]
    rw [Finset.sum_eq_card_nsmul const, nsmul_eq_mul,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨t, by simp [ht]⟩))]
  rw [S.sum_image' (fun s ↦ G s / D) fibre, ← S.sum_div, h_sum, zero_div]

/-!
## Schur polynomials in the coefficients of a monic polynomial

A Schur polynomial in `a` variables is symmetric, so it is an integer polynomial in the coefficients
of `∏ (X - r i)`. Here it is defined in that form, without division, for any tuple of exponents
`l : Fin a → ℕ` (classically `l j` is a part of a partition plus `j`).
-/

section SchurPolynomial

open Matrix Polynomial Finset Fin Lagrange

namespace New.Variety

variable {a : ℕ} (l : Fin a → ℕ) {R S : Type} [CommRing R] [CommRing S]
  (r : Fin a → R) (s : Multiset R)

/-- For exponents `l : Fin a → ℕ`, the determinant of the matrix of coefficients of the remainders
of the `X ^ l j` modulo `freeMonic ℤ a`, the generic monic polynomial of degree `a`. It is an
integer polynomial in the `a` generic coefficients. -/
noncomputable def genericSchur : MvPolynomial (Fin a) ℤ :=
  (of fun k j : Fin a ↦ (X ^ l j %ₘ freeMonic ℤ a).coeff k.val).det

/-- Evaluation of an integer polynomial in `a` variables at the coefficients of degree less than `a`
of `∏ (X - t)`, with `t` running over the multiset `s`. Applied to `genericSchur l`, with `s` of
size `a`, it gives the value of the Schur polynomial at the roots. -/
noncomputable def rootCoeffEval : MvPolynomial (Fin a) ℤ →ₐ[ℤ] R :=
  MvPolynomial.aeval (R := ℤ) fun i : Fin a ↦ (s.map fun t : R ↦ X - C t).prod.coeff i

/-- `rootCoeffEval s`, evaluation at the coefficients of `∏ t ∈ s, (X - t)`, commutes with a ring
homomorphism `f`, applied to the roots. -/
lemma rootCoeffEval_map (f : R →+* S) (q : MvPolynomial (Fin a) ℤ) :
    rootCoeffEval (a := a) (s.map f) q = f (rootCoeffEval s q) := by
  rw [rootCoeffEval, rootCoeffEval, MvPolynomial.map_aeval, MvPolynomial.aeval_eq_eval₂Hom,
    RingHom.ext_int (f.comp (algebraMap ℤ R)) (algebraMap ℤ S)]
  simp [← coeff_map, Polynomial.map_multiset_prod]

/-- The bialternant formula over a domain `R`: the Schur polynomial `genericSchur l`, evaluated at
the coefficients of `∏ (X - r i)`, times the Vandermonde determinant of `r` is the generalised
Vandermonde determinant `det (r i ^ l j)`. -/
lemma rootCoeffEval_genericSchur_mul_det [IsDomain R] :
    rootCoeffEval (univ.val.map r) (genericSchur l) * (vandermonde r).det =
      (of fun i j : Fin a ↦ r i ^ l j).det := by
  -- `φ` specialises the generic monic polynomial `freeMonic ℤ a` to `∏ (X - r k)`, which
  -- vanishes at `r i`; so the remainder of `X ^ l j` takes the value `r i ^ l j` there.
  let p : MonicDegreeEq R a := .mk (nodal univ r) nodal_monic (by simp)
  let φ : MvPolynomial (Fin a) ℤ →ₐ[ℤ] R := (MvPolynomial.mapEquivMonic ℤ R a).symm p
  have hφ : (freeMonic ℤ a).map φ = nodal univ r :=
    congrArg Subtype.val ((MvPolynomial.mapEquivMonic ℤ R a).apply_symm_apply p)
  have hφ_eq : rootCoeffEval (univ.val.map r) = φ := MvPolynomial.algHom_ext fun k ↦ by
    simp [rootCoeffEval, φ, p, MvPolynomial.mapEquivMonic, nodal, ← Fin.prod_ofFn,
      Function.comp_def]
  have h_rem (i j : Fin a) : (X ^ l j %ₘ freeMonic ℤ a).eval₂ φ (r i) = r i ^ l j := by
    rw [eval₂_modByMonic_eq_self_of_root (by simp [eval₂_eq_eval_map, hφ, eval_nodal_at_node]),
      eval₂_X_pow]
  -- Expanding this value in powers of `r i`: the Vandermonde matrix times the matrix of
  -- coefficients of the remainders has entries `r i ^ l j`.
  have h_mul : vandermonde r *
      φ.mapMatrix (of fun k j : Fin a ↦ (X ^ l j %ₘ freeMonic ℤ a).coeff k.val) =
        of fun i j : Fin a ↦ r i ^ l j := by
    ext i j
    rw [of_apply, ← h_rem i j]
    conv_rhs => rw [← sum_modByMonic_coeff (monic_freeMonic ℤ a) (degree_freeMonic ℤ a).le]
    simp [mul_apply, mul_comm, eval₂_finsetSum]
  rw [hφ_eq, genericSchur, mul_comm, AlgHom.map_det, ← det_mul, h_mul]

end New.Variety

end SchurPolynomial

/-! ## Extracting Schur polynomials from vanishing linear forms -/

section SchurExtraction

open NumberField Matrix Submodule Polynomial Finset Lagrange Multiset Set SetLike Fintype

namespace New.Variety

variable {a : ℕ} {ι S K R : Type _} [Fintype S] [Field K] [CommRing R] [Algebra K R]

/-- Lagrange interpolation of `X ^ j`, for `j < a`, at distinct nodes `r₁, …, r_a`, evaluated at a
polynomial `t`. -/
lemma sum_aeval_lagrange_basis_mul_C_pow (r : Fin a ↪ K) (t : K[X]) (j : Fin a) :
    ∑ k : Fin a, aeval t (Lagrange.basis Finset.univ r k) * C (r k) ^ j.val = t ^ j.val := by
  have h_pow : (X : K[X]) ^ j.val = ∑ k, Lagrange.basis univ r k * C (r k) ^ j.val := by
    simpa [mul_comm] using eq_interpolate (f := X ^ j.val) (s := univ) r.injective.injOn (by simp)
  simpa using congrArg (aeval t) h_pow.symm

/-- For distinct `r₁, …, r_a` in a field `K` and exponents `l : Fin a → ℕ`, the identity `∑ᵢ
∏_{k ≠ i} (X rᵢ - r_k) / (rᵢ - r_k) · s_l(r₁, …, X rᵢ, …, r_a) = s_l(r) · ∑ⱼ X ^ l j` holds in
`K[X]`. Here `s_l(r)` is `genericSchur l` evaluated by `rootCoeffEval` at the coefficients of
`∏ (T - r_k)`. This is the determinant of the coefficients of the remainders of the `X ^ l j` modulo
that product, so the exponents `l j` play the role of the alternant exponents `λ_j + a - j` of a
Schur polynomial, not of a partition `λ`. -/
lemma sum_lagrange_smul_rootCoeffEval (l : Fin a → ℕ) (r : Fin a ↪ K) :
    ∑ i : Fin a, aeval (X * C (r i)) (Lagrange.basis Finset.univ r i) •
        rootCoeffEval (univ.val.map fun k : Fin a ↦ (if k = i then X else 1) * C (r k))
          (genericSchur l) =
      C (rootCoeffEval (univ.val.map r) (genericSchur l)) * ∑ j : Fin a, X ^ l j := by
  -- Multiply by the Vandermonde determinant of `r` and use the bialternant formula.
  refine mul_right_cancel₀ (b := (vandermonde (C ∘ r)).det)
    (det_vandermonde_ne_zero_iff.2 (C_injective.comp r.injective)) ?_
  -- The image of the bialternant formula under `C`.
  have h_schur : C (rootCoeffEval (univ.val.map r) (genericSchur l)) * (vandermonde (C ∘ r)).det =
      (of fun k j : Fin a ↦ C (r k) ^ l j).det := by
    simpa [← rootCoeffEval_map, Function.comp_def] using
      rootCoeffEval_genericSchur_mul_det l (C ∘ r)
  -- By Lagrange interpolation, the row of `X * r i` is the combination of the rows of the `r k`
  -- with coefficients `basis k (X * r i)`; only `k = i` counts in the determinant.
  have replace_row (i : Fin a) :
      aeval (X * C (r i)) (Lagrange.basis univ r i) • (vandermonde (C ∘ r)).det =
        (vandermonde fun k ↦ (if k = i then X else 1) * C (r k)).det := by
    rw [← det_updateRow_sum _ i fun k ↦ aeval (X * C (r i)) (Lagrange.basis univ r k)]
    congr 1
    ext k j : 1
    by_cases hk : k = i <;> simp [hk, sum_aeval_lagrange_basis_mul_C_pow, Finset.sum_apply]
  -- So each term on the left becomes a generalised Vandermonde determinant with one row changed.
  have h_left (i : Fin a) : aeval (X * C (r i)) (Lagrange.basis univ r i) •
      rootCoeffEval (univ.val.map fun k : Fin a ↦ (if k = i then X else 1) * C (r k))
        (genericSchur l) * (vandermonde (C ∘ r)).det =
      (of fun k j : Fin a ↦ ((if k = i then X else 1) * C (r k)) ^ l j).det := by
    rw [smul_mul_assoc, ← mul_smul_comm, replace_row, rootCoeffEval_genericSchur_mul_det]
  rw [sum_mul, mul_right_comm, h_schur, Finset.sum_congr rfl fun i _ ↦ h_left i]
  -- It remains to show that the sum of these determinants is `det (r k ^ l j) * ∑ j, X ^ l j`.
  -- Expand the determinants: the term of a permutation `σ` gains the factor `X ^ l j`, `j` the
  -- column used in row `i`, and each `j` occurs once as `i` varies.
  have h_term (σ : Equiv.Perm (Fin a)) (i : Fin a) :
      ∏ j, ((if σ j = i then X else 1) * C (r (σ j))) ^ l j =
        X ^ l (σ.symm i) * ∏ j, C (r (σ j)) ^ l j := by
    simp_rw [mul_pow, prod_mul_distrib]
    simp [← Equiv.eq_symm_apply]
  simp_rw [det_apply', of_apply, h_term]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp [← Finset.sum_mul, σ.symm.sum_comp fun j ↦ X ^ l j, mul_assoc, mul_comm]

open MvPolynomial RingOfIntegers Finsupp

/-- For a number field `E` and a type `ι`, the doubled coordinate functions `α ↦ σ (2 * α i)` on
`(𝓞 E)^ι`, indexed by the pairs `(i, σ)` of an index `i: ι` and an embedding `σ` of `E` in `ℂ`, are
algebraically independent over `ℂ`. -/
lemma algebraicIndependent_embedding_two_mul {E : Type*} [Field E] [NumberField E] :
    AlgebraicIndependent ℂ fun (p : ι × (E →+* ℂ)) (α : ι → 𝓞 E) ↦ p.2 (2 * α p.1 : 𝓞 E) := by
  -- Write `αᵢ` in an integral basis of `𝓞 E`. A relation `P` becomes a polynomial in the
  -- coordinates that vanishes at all natural numbers, hence is zero; the change of variables is
  -- invertible over `ℂ` because the embedded integral basis `b` is a basis of `(E →+* ℂ) → ℂ`.
  refine algebraicIndependent_iff.2 fun P hP ↦ ?_
  let I : Type _ := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b : Module.Basis I ℂ ((E →+* ℂ) → ℂ) := canonicalEmbedding.latticeBasis E
  -- `coord (i, σ)` is `σ (2 αᵢ)` as a linear form in the coordinates of `αᵢ`.
  let coord : ι × (E →+* ℂ) → MvPolynomial (ι × I) ℂ :=
    fun (i, σ) ↦ 2 • ∑ k : I, .X (i, k) * .C (b k σ)
  have h_nat (z : ι × I → ℕ) : MvPolynomial.aeval (fun p ↦ (z p : ℂ)) (P.bind₁ coord) = 0 := by
    let α (i : ι) : 𝓞 E := ∑ k : I, (z (i, k) : 𝓞 E) * basis E k
    have hPα : MvPolynomial.aeval (fun p : ι × (E →+* ℂ) ↦ p.2 (2 * α p.1 : 𝓞 E)) P = 0 := by
      simpa [comp_aeval_apply] using congrArg (Pi.evalAlgHom ℂ _ α) hP
    have hb (k : I) (σ : E →+* ℂ) : b k σ = σ (basis E k) := by simp [b, I]
    simpa [aeval_bind₁, α, hb, coord, two_mul] using hPα
  have h_zero : P.bind₁ coord = 0 := by
    refine funext_set (fun _ ↦ Set.range (Nat.cast : ℕ → ℂ))
      (fun _ ↦ infinite_range_of_injective Nat.cast_injective) fun x hx ↦ ?_
    choose z hz using fun p : ι × I ↦ hx p (Set.mem_univ p)
    simpa [← _root_.funext hz, ← aeval_eq_eval] using h_nat z
  -- To evaluate `P` at `v`, take as coordinates those of `v (i, ·) / 2` in the basis `b`.
  refine MvPolynomial.funext fun v ↦ ?_
  let y (p : ι × I) : ℂ := b.repr (fun σ ↦ v (p.1, σ) / 2) p.2
  have h_coord (p : ι × (E →+* ℂ)) : MvPolynomial.aeval y (coord p) = v p := by
    have h_repr : ∑ k : I, y (p.1, k) * b k p.2 = v p / 2 := by
      simpa [y] using congrFun (b.sum_repr fun σ ↦ v (p.1, σ) / 2) p.2
    simp [coord, two_mul, h_repr]
  simpa [aeval_bind₁, h_coord] using congrArg (MvPolynomial.aeval y) h_zero

/-- Let the functions `c (i, σ) : A → K` be algebraically independent over `K`, let each polynomial
`q σ` have total degree at most `card ι`, and let each multiset `x j σ` have `a` elements. If a
linear form `L` kills the family `j ↦ ∏_{i, σ} ∏_{t ∈ x j σ} (1 - c (i, σ) α * t)` for every `α`,
then it kills `j ↦ ∏_σ rootCoeffEval (x j σ) (q σ)`, where `rootCoeffEval (x j σ)` evaluates at the
coefficients of `∏_{t ∈ x j σ} (X - t)`. -/
lemma map_prod_rootCoeffEval_eq_zero [Fintype ι] {A : Type*} {q : S → MvPolynomial (Fin a) ℤ}
    (h_deg : ∀ σ : S, (q σ).totalDegree ≤ Fintype.card ι) {c : ι × S → A → K}
    (hc : AlgebraicIndependent K c) {J : Type*} {x : J → S → Multiset R}
    (hx : ∀ (j : J) (σ : S), (x j σ).card = a) (L : (J → R) →ₗ[K] K)
    (hL : ∀ α : A, L (fun j : J ↦
      ∏ i : ι, ∏ σ : S, ((x j σ).map fun t : R ↦ 1 - algebraMap K R (c (i, σ) α) * t).prod) = 0) :
    L (fun j : J ↦ ∏ σ : S, rootCoeffEval (x j σ) (q σ)) = 0 := by
  classical
  -- Let `e σ k` be the signed elementary symmetric functions of `x · σ`, and `M σ` their span.
  -- Comparing coefficients shows that `L` kills `∏ σ, M σ ^ card ι`, and
  -- `rootCoeffEval (x · σ) (q σ)` lies in `M σ ^ card ι`.
  let e (σ : S) (k : Fin a.succ) (j : J) : R := (-1) ^ k.1 * (x j σ).esymm k
  let M (σ : S) : Submodule K (J → R) := span K (.range (e σ))
  -- Vieta's formula at `X = 1` for the multiset `b • x j σ`.
  have vieta (j : J) (σ : S) (b : K) :
      ((x j σ).map fun t ↦ 1 - b • t).prod = ∑ k : Fin a.succ, b ^ k.1 • e σ k j := by
    simpa [e, eval_multiset_prod, sum_range, eval_finsetSum, hx, ← pow_smul_esymm] using
      congrArg (Polynomial.eval 1) ((x j σ).map fun t ↦ b • t).prod_X_sub_X_eq_sum_esymm
  -- Expand the product in `hL`.
  have expand (α : A) :
      L (∑ y : ι × S → Fin a.succ, (∏ p, c p α ^ (y p).1) • ∏ p, e p.2 (y p)) = 0 := by
    rw [← hL α]
    refine congrArg L (_root_.funext fun j ↦ ?_)
    simp_rw [← Algebra.smul_def, vieta, ← prod_prod_type']
    simp [prod_univ_sum, prod_smul]
  -- This is a linear relation between monomials in the `c (i, σ)`, which are linearly
  -- independent; so each coefficient `L (∏ p, e p.2 (y p))` is zero.
  have coeff_zero (y : ι × S → Fin a.succ) : L (∏ p, e p.2 (y p)) = 0 := by
    let expo (y : ι × S → Fin a.succ) : ι × S →₀ ℕ := equivFunOnFinite.symm (Fin.val ∘ y)
    have indep : LinearIndependent K fun y : ι × S → Fin a.succ ↦
        MvPolynomial.aeval c (monomial (expo y) (1 : K)) :=
      ((basisMonomials (ι × S) K).linearIndependent.map_injOn (MvPolynomial.aeval c).toLinearMap
        hc.injOn).comp expo (equivFunOnFinite.symm.injective.comp Fin.val_injective.comp_left)
    refine Fintype.linearIndependent_iff.1 indep (fun y ↦ L (∏ p, e p.2 (y p))) ?_ y
    ext α
    simpa [expo, MvPolynomial.aeval_monomial, mul_comm] using expand α
  -- The products `∏ p, e p.2 (y p)` span `∏ σ, M σ ^ card ι`.
  have le_ker : ∏ σ : S, ∏ _ : ι, M σ ≤ L.ker := by
    rw [← prod_prod_type_right' fun (_ : ι) (σ : S) ↦ M σ]
    simpa [M, prod_span, span_le, ← image_fintype_prod_pi, ← range_piMap,
      range_subset_iff] using coeff_zero
  -- A monomial of `q σ` is evaluated to a product of at most `card ι` coefficients of
  -- `∏ (X - t)`, which are the `e σ k`; pad with `e σ 0 = 1`.
  have eval_mem (σ : S) : (fun j ↦ rootCoeffEval (x j σ) (q σ)) ∈ ∏ _ : ι, M σ := by
    have one_le_M : 1 ≤ M σ :=
      one_le.2 (subset_span ⟨0, _root_.funext fun j ↦ by simp [e, Multiset.esymm]⟩)
    have eval_eq : (fun j ↦ rootCoeffEval (x j σ) (q σ)) =
        ∑ d ∈ (q σ).support, (q σ).coeff d • ∏ k : Fin a, e σ k.castSucc.rev ^ d k := by
      ext j
      simp [rootCoeffEval, aeval_eq_eval₂Hom, eval₂_eq', prod_X_sub_C_coeff, hx, e]
    rw [eval_eq, Finset.prod_const, Finset.card_univ]
    refine sum_mem fun d hd ↦ zsmul_mem ?_ _
    have monomial_mem : ∏ k : Fin a, e σ k.castSucc.rev ^ d k ∈ M σ ^ ∑ k, d k := by
      simpa using prod_pow_mem_graded (fun m : ℕ ↦ M σ ^ m) 1 (fun k : Fin a ↦ e σ k.castSucc.rev) d
        (by simp [M, mem_span_of_mem])
    exact pow_le_pow_right' one_le_M
      (by simpa [sum_fintype] using (le_totalDegree hd).trans (h_deg σ)) monomial_mem
  simpa [prod_fn] using le_ker
    (Finset.prod_hom_rel (r := fun f N ↦ f ∈ N) ⟨1, by simp⟩ fun σ _ _ ↦ mul_mem_mul (eval_mem σ))

end New.Variety

end SchurExtraction
