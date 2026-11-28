import New.UpperBound.ElementaryDivisors.Edges
import New.UpperBound.ElementaryDivisors.FrobeniusFactors

/-!
# Averaging: removing the terms of large defect in all Levi translates at once

Fix a Frobenius cycle `T` over `W` and `O` (`New.FrobeniusCycle`; `N = 2 ℓ` letters, `P` a power of
the prime `p`, `w ^ 2 = p`) and an edge, with the Levi subgroup `G` of blocks of sizes `r` and
`k - r`. Forms are written in the normalized monomials of the edge with weights `b_β`, and
`⟨h, h'⟩ = ∑_β h'_β b_β h_β` is the pairing with the forms of the dual edge
(`New.FrobeniusCycle.IsEdgePairing`). Fix `c : ℕ` and put `c* = 3 k c` (`New.defectThreshold`) and
`c₀ = T.multinomialExponent k`. Let `O` be a valuation domain of characteristic `0` in which `p` is
not a unit, and let `P ^ ℓ` be large. The main result
`New.FrobeniusCycle.exists_average_mem_defectConditions_and_dvd_sub` gives a matrix `Av` such that
no `G(W)`-translate of `Av h` has a term of defect above `3 c*` modulo `w ^ c`, while
`⟨Av h, h'⟩ ≡ p ^ (N c₀) ⟨h, h'⟩` modulo `w ^ c` for all `h'` in the halfway lattices of all edges
from the origin of the dual edge (`New.FrobeniusCycle.allEdgesForms`).

Substitute generic matrices, one copy for each letter, in `h`
(`New.FrobeniusCycle.substitutionOperator`). For a set `J` of copies, `Av_J h`
(`New.FrobeniusCycle.partialAverage`) is obtained by applying the average (`New.Average.IsAverage`)
in the copies `j ∈ J` and `p ^ c₀` times the evaluation at `1` in the others. Then
`Av_∅ h = p ^ (N c₀) h`, and `Av` is `Av_J` for the set of all copies. A monomial in one copy is bad
if its row weight for `New.rootVector a r`, `r = a + 1`, is above `2 c* P ^ ℓ`. The substitution in
the frame `g ∈ G(W)` is the one formed from the factors
`New.FrobeniusCycle.conjFrobGenericMatrix g`.

* `New.FrobeniusCycle.contractOtherCopies`, `New.FrobeniusCycle.conjSubst_contractOtherCopies_one`:
  the linear forms are applied in all copies but one, in a frame `g`; the change of frame conjugates
  the remaining copy.
* `New.FrobeniusCycle.abs_weight_div_sub_defect_le`: let the forms be invariant under `G(W)`. If the
  coefficient of `α` in the entry `β` of `contractOtherCopies` is not divisible by `w ^ c`, then the
  row weight of `α` over `P ^ ℓ` is within `c*` of the defect of `β` at the letter `j + ℓ`, for the
  remaining copy `j`.
* `New.FrobeniusCycle.lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies`: hence a defect
  of `β` above `3 c*` makes `α` bad, and a bad `α` makes the defect exceed `c*`.
* `New.FrobeniusCycle.pow_dvd_pairing_partialAverage_insert_sub`: one more copy in `J` does not
  change the pairing modulo `w ^ c`. The main result adds these differences along a chain of
  subsets.

Notions from other files:
* `New.FrobeniusCycle.letterRep`: the matrix of `g ∈ GL_k(W)` on the forms, which have degree `n` in
  each letter and are twisted at the letter `s` by `T.embedding s`.
* `New.FrobeniusCycle.substitutionOperator`: the Kronecker product over the letters `s` of the
  matrices on forms of degree `n` that are built from given factors `ψ s d`; with
  `New.FrobeniusCycle.frobGenericMatrix` the factor is the entrywise power `P ^ d` of the copy
  `s - d` of the generic matrix, and odd letters take the cofactor matrix of the product.
* `New.Average.IsAverage`: a linear form that is invariant under conjugation by the Levi subgroup
  and vanishes on bad monomials. If a polynomial of bounded degree has all bad coefficients of its
  Levi conjugates in an ideal, the form agrees on it with a multiple of the evaluation at `1` modulo
  this ideal.
* `New.FrobeniusCycle.defectConditions`: the vectors whose `G(W)`-translates have their coefficients
  of defect above a bound in a given ideal.

## Relation to the literature

Linear forms on polynomials in a generic matrix that are invariant under the Levi subgroup split
evaluation at the identity by weight, up to a power of `p`. This gives a map into the forms without
terms of large defect that keeps the pairing up to `p ^ (N c₀)` modulo `w ^ c`. The Schur algebra as
dual of polynomials in a generic matrix, its spanning by finite points in low degree, and truncation
by weights are known in the literature. Related work: Benson–Doty, Schur–Weyl duality over finite
fields, 2009; Green, Polynomial representations of GL_n, 1980; Donkin, On Schur algebras and related
algebras I, 1986.
-/

noncomputable section

namespace New

open MvPolynomial Matrix IsLocalRing Function Module PiTensorProduct Finset Fintype Ideal Average

/-! ### Tensor products of linear forms on polynomials -/

section TensorDual

variable {ι σ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A linear form on polynomials is determined by its values on the monomials. -/
lemma map_eq_sum_coeff_mul (m : Dual R (MvPolynomial σ R)) (ψ : MvPolynomial σ R) :
    m ψ = ∑ α ∈ ψ.support, ψ.coeff α * m (monomial α 1) := by
  conv_lhs => rw [ψ.as_sum, map_sum]
  exact sum_congr rfl fun α _ ↦ by
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]

/-- If for each exponent `α` either `z` divides the coefficient of `α` in `ψ` or the linear form `m`
vanishes on the monomial of exponent `α`, then `z` divides `m ψ`. -/
lemma dvd_map_of_forall_monomial {m : Dual R (MvPolynomial σ R)} {ψ : MvPolynomial σ R} {z : R}
    (h_all : ∀ α : σ →₀ ℕ, ¬z ∣ ψ.coeff α → m (monomial α 1) = 0) : z ∣ m ψ := by
  rw [map_eq_sum_coeff_mul]
  exact dvd_sum fun α _ ↦ by
    by_cases h_dvd : z ∣ ψ.coeff α <;> simp [h_all α, h_dvd, dvd_mul_of_dvd_left]

/-- The tensor product of linear forms `l j` on polynomials in disjoint blocks of variables: the
product of the forms on `⨂_ι R[X_σ]`, pulled back along `R[X_{ι × σ}] → ⨂_ι R[X_σ]`. -/
def tensorDual (l : ι → Dual R (MvPolynomial σ R)) : Dual R (MvPolynomial (ι × σ) R) :=
  dualDistrib (tprod R l) ∘ₗ
    (aeval fun v : ι × σ ↦ singleAlgHom v.1 (X v.2) :
      MvPolynomial (ι × σ) R →ₐ[R] PiTensorProduct R fun _ : ι ↦ MvPolynomial σ R).toLinearMap

/-- On a product of polynomials `f j`, one in each block, the tensor product of the forms `l j` is
the product of the values `l j (f j)`. -/
lemma tensorDual_prod_rename (l : ι → Dual R (MvPolynomial σ R)) (f : ι → MvPolynomial σ R) :
    tensorDual l (∏ j : ι, rename (fun v : σ ↦ (j, v)) (f j)) = ∏ j : ι, l j (f j) := by
  let Ψ : MvPolynomial (ι × σ) R →ₐ[R] PiTensorProduct R fun _ : ι ↦ MvPolynomial σ R :=
    aeval fun v : ι × σ ↦ singleAlgHom v.1 (X v.2)
  have h_block (j : ι) : Ψ.comp (rename fun v : σ ↦ (j, v)) =
      singleAlgHom (A := fun _ : ι ↦ MvPolynomial σ R) j := algHom_ext fun v ↦ by simp [Ψ]
  have hΨ : Ψ (∏ j : ι, rename (fun v : σ ↦ (j, v)) (f j)) = tprod R f := by
    simp [← Ψ.comp_apply, h_block, ← tprod_prod, univ_prod_mulSingle]
  rw [tensorDual, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hΨ, dualDistrib_apply]

/-- On the monomial of exponent `ν`, the tensor product of the forms `l j` is the product of the
values of `l j` at the monomials of exponent `ν.curry j`, the parts of `ν` in the blocks. -/
lemma tensorDual_monomial [Fintype σ] (l : ι → Dual R (MvPolynomial σ R)) (ν : ι × σ →₀ ℕ) :
    tensorDual l (monomial ν 1) = ∏ j : ι, l j (monomial (ν.curry j) 1) := by
  simp [← tensorDual_prod_rename, monomial_eq, prod_prod_type]

/-- The value of the tensor product of the forms `l j` at `f` is the sum over the monomials of `f`
of the coefficient times the product of the values of the `l j` at the parts of the monomial. -/
lemma tensorDual_eq_sum [Fintype σ] (l : ι → Dual R (MvPolynomial σ R))
    (f : MvPolynomial (ι × σ) R) :
    tensorDual l f = ∑ ν ∈ f.support, f.coeff ν * ∏ j : ι, l j (monomial (ν.curry j) 1) := by
  simp only [map_eq_sum_coeff_mul (tensorDual l) f, tensorDual_monomial]

/-- If the form in each block is `evalAtOne z`, that is `z` times the evaluation at the identity
matrix, then the tensor product of the forms is `z` to the number of blocks times the evaluation at
the identity matrix in every block. -/
lemma tensorDual_evalAtOne {k : ℕ} {A : Type} [CommRing A] (z : A)
    (f : MvPolynomial (ι × Fin k × Fin k) A) :
    tensorDual (fun _ : ι ↦ evalAtOne z) f = z ^ Fintype.card ι *
      eval (fun v : ι × Fin k × Fin k ↦ vec (1 : Matrix (Fin k) (Fin k) A) v.2) f := by
  rw [tensorDual_eq_sum, eval_eq', mul_sum]
  refine sum_congr rfl fun ν _ ↦ ?_
  simp [evalAtOne_apply, eval_monomial, prod_prod_type, prod_mul_distrib, mul_left_comm]

/-- Apply the forms `l i` in all blocks `i ≠ j` of variables; a polynomial in the block `j`
remains. A monomial of exponent `ν` gives the product of the values of the `l i` at its parts
`ν.curry i`, times the monomial of exponent `ν.curry j`. -/
def tensorDualExcept (l : ι → Dual R (MvPolynomial σ R)) (j : ι) (f : MvPolynomial (ι × σ) R) :
    MvPolynomial σ R :=
  ∑ ν ∈ f.support,
    (f.coeff ν * ∏ i ∈ univ.erase j, l i (monomial (ν.curry i) 1)) • monomial (ν.curry j) 1

/-- Applying a form `m` to `tensorDualExcept l j f`, the polynomial left in the block `j` after the
forms `l i` are applied in the other blocks, gives `tensorDual (update l j m) f`: the tensor product
of the forms with `l j` replaced by `m`. -/
lemma map_tensorDualExcept [Fintype σ] (l : ι → Dual R (MvPolynomial σ R)) (j : ι)
    (m : Dual R (MvPolynomial σ R)) (f : MvPolynomial (ι × σ) R) :
    m (tensorDualExcept l j f) = tensorDual (update l j m) f := by
  rw [tensorDual_eq_sum, tensorDualExcept, map_sum]
  refine sum_congr rfl fun ν _ ↦ ?_
  have h_rest : ∀ i ∈ univ.erase j, update l j m i = l i :=
    fun i hi ↦ update_of_ne (ne_of_mem_erase hi) m l
  simp +contextual [← prod_erase_mul _ _ (mem_univ j), h_rest, mul_assoc]

/-- Let `f` be a polynomial in blocks of variables indexed by `ι`, and let `tensorDualExcept l j f`
be the polynomial in the block `j` obtained by applying the linear forms `l i` in all blocks
`i ≠ j`. If `z` does not divide its coefficient of `α`, then `α` is the part in the block `j` of a
monomial `ν` whose coefficient in `f` is not divisible by `z` and whose other parts are not killed
by the forms `l i`. -/
lemma exists_of_not_dvd_coeff_tensorDualExcept {l : ι → Dual R (MvPolynomial σ R)} {j : ι}
    {f : MvPolynomial (ι × σ) R} {z : R} {α : σ →₀ ℕ}
    (h_coeff : ¬z ∣ (tensorDualExcept l j f).coeff α) :
    ∃ ν : ι × σ →₀ ℕ, ν.curry j = α ∧ ¬z ∣ f.coeff ν ∧
      ∀ i ≠ j, l i (monomial (ν.curry i) 1) ≠ 0 := by
  classical
  contrapose! h_coeff with h_all
  simp only [tensorDualExcept, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul]
  refine dvd_sum fun ν _ ↦ ?_
  -- Each summand has `z` as a factor of its coefficient, or a factor `0`.
  by_cases h_part : ν.curry j = α
  · by_cases h_dvd : z ∣ f.coeff ν
    · simpa [h_part] using h_dvd.mul_right _
    · obtain ⟨i, hi, h_zero⟩ := h_all ν h_part h_dvd
      rw [prod_eq_zero (mem_erase.2 ⟨hi, mem_univ i⟩) h_zero]
      simp
  · simp [h_part]

/-- The polynomial in the block `j` that remains of `f` after the forms `l i` are applied in the
blocks `i ≠ j` has at most the degree of `f` in the block `j`. -/
lemma tensorDualExcept_mem_restrictTotalDegree (l : ι → Dual R (MvPolynomial σ R)) (j : ι)
    {f : MvPolynomial (ι × σ) R} {D : ℕ}
    (h_degree : ∀ ν : ι × σ →₀ ℕ, f.coeff ν ≠ 0 → (ν.curry j).degree ≤ D) :
    tensorDualExcept l j f ∈ restrictTotalDegree σ R D := by
  exact Submodule.sum_mem _ fun ν hν ↦ Submodule.smul_mem _ _ <| (mem_restrictTotalDegree ..).2 <|
    (totalDegree_monomial_le _ _).trans (h_degree ν (mem_support_iff.1 hν))

end TensorDual

namespace FrobeniusCycle

variable {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O]
  (T : FrobeniusCycle N W O)

/-! ### Linear forms applied to the substitution -/

/-- The entries of `T.substitutionOperator r ℓ n T.frobGenericMatrix` are polynomials in `N` generic
`k × k` matrices, the copies, one for each letter `j ∈ ℤ/N`. This is the matrix over `O` obtained by
applying to each entry the tensor product of linear forms `l j`, one for each copy. Its rows and
columns are indexed by the monomials of degree `n` in each of `N` groups of `k` variables. -/
def frobContraction (n r ℓ : ℕ) (l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)) :
    Matrix (Exponents N k n) (Exponents N k n) O :=
  (T.substitutionOperator r ℓ n T.frobGenericMatrix).map (tensorDual l)

/-- The matrix `T.frobContraction n r ℓ l`, indexed by the monomials of degree `n` in each of `N`
groups of `k` variables (`Exponents N k n`), arises from the substitution of `N` generic `k × k`
matrices by applying a linear form `l j` in the entries of the `j`-th one. If each form is `z` times
the evaluation at the identity matrix (`evalAtOne z`), it is the scalar matrix `z ^ N`. -/
lemma frobContraction_evalAtOne (r ℓ : ℕ) (z : O) :
    T.frobContraction (k := k) n r ℓ (fun _ : ZMod N ↦ evalAtOne z) =
      z ^ N • (1 : Matrix (Exponents N k n) (Exponents N k n) O) := by
  -- At the identity matrices `substitutionOperator` is `1`.
  let ev : MvPolynomial (ZMod N × Fin k × Fin k) O →+* O :=
    eval fun v : ZMod N × Fin k × Fin k ↦ vec (1 : Matrix (Fin k) (Fin k) O) v.2
  have h_factor (s : ZMod N) (d : ℕ) : (T.frobGenericMatrix s d).map ev = 1 :=
    Matrix.ext fun b c ↦ by simp [ev, one_apply, T.prime.ne_zero, eq_comm]
  have h_one : (T.substitutionOperator (k := k) r ℓ n T.frobGenericMatrix).map ev = 1 := by
    -- `substitutionOperator_map_eq_conj` at `g = 1` moves `ev` into the factors.
    simp [T.substitutionOperator_map_eq_conj ev (one_mem _), h_factor, substitutionOperator_one]
  ext β β'
  simp [frobContraction, tensorDual_evalAtOne, ← h_one, ev]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `T` be a Frobenius cycle, with ring maps `T.embedding j : W →+* O` for the letters
`j ∈ ℤ/N`, and let `ρ(g) = T.letterRep n g` be the matrix of `g ∈ GL_k(W)` on polynomials of degree
`n` in each of `N` groups of `k` variables. For a family `ψ` of factors,
`S(ψ) = T.substitutionOperator r ℓ n ψ` is a matrix of the same size; here its entries are
polynomials in `N` generic matrices `X_j`. Write `l(S)` for `S.map (tensorDual l)`, the matrix over
`O` obtained by applying the linear form `l j` in the entries of `X_j` for every `j`. Let `g` be
block diagonal with blocks of sizes `r` and `k - r`, and let `m j` be `l j` composed with
`X ↦ g⁻¹ X g` through `T.embedding j` (`conjSubst`). Then `ρ(g) m(S(ψ₁)) = l(S(ψ_g)) ρ(g)`. Here
`ψ₁ = T.frobGenericMatrix` consists of the entrywise powers `P ^ d` of the `X_j`, so that
`m(S(ψ₁)) = T.frobContraction n r ℓ m`, and `ψ_g = T.conjFrobGenericMatrix g` is the same family
with the powers taken in the basis given by `g`. -/
lemma letterRep_mul_frobContraction {r ℓ : ℕ} {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r))
    {l m : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hm : ∀ (j : ZMod N) (ψ : MvPolynomial (Fin k × Fin k) O),
      m j ψ = l j (conjSubst (T.embedding j) g ψ)) :
    T.letterRep n g * T.frobContraction n r ℓ m =
      (T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g)).map (tensorDual l) *
        T.letterRep n g := by
  -- Move the conjugation by `g` from the forms to the generic matrices.
  let conj :
      MvPolynomial (ZMod N × Fin k × Fin k) O →ₐ[O] MvPolynomial (ZMod N × Fin k × Fin k) O :=
    aeval fun v : ZMod N × Fin k × Fin k ↦
      rename (fun u : Fin k × Fin k ↦ (v.1, u)) (conjSubst (T.embedding v.1) g (X v.2))
  have h_monomial (ν : ZMod N × Fin k × Fin k →₀ ℕ) : conj (monomial ν 1) = ∏ j : ZMod N,
      rename (fun u : Fin k × Fin k ↦ (j, u))
        (conjSubst (T.embedding j) g (monomial (ν.curry j) 1)) := by
    simp [conj, monomial_eq, prod_prod_type]
  have h_forms : tensorDual m = tensorDual l ∘ₗ conj.toLinearMap :=
    linearMap_ext fun ν ↦ LinearMap.ext_ring <| by
      simp [tensorDual_monomial, h_monomial, tensorDual_prod_rename, hm]
  let T' : FrobeniusCycle N W (MvPolynomial (ZMod N × Fin k × Fin k) O) := T.map C
  have h_entry (s : ZMod N) (b c : Fin k) :
      conj (X (s, b, c)) = T'.letterConj g⁻¹ s (of fun b' c' : Fin k ↦ X (s, b', c')) b c := by
    simp [T', conj, letterConj, conjSubst, linSubst, ← C_mul', map, mul_apply, mul_assoc,
      mul_comm (X _), sum_prod_type, mul_sum]
  have h_frame : (fun (s : ZMod N) (d : ℕ) ↦
      T'.letterConj g s ((T.frobGenericMatrix s d).map conj.toRingHom)) =
        T.conjFrobGenericMatrix g := by
    funext s d
    simp only [conjFrobGenericMatrix]
    congr 1 with b c : 1
    simp [h_entry, T']
  -- After `conj`, the operator is a conjugate of the operator `F` in the frame `g`.
  set F := T.substitutionOperator (k := k) r ℓ n (T.conjFrobGenericMatrix g)
  have h_op : (T.substitutionOperator r ℓ n T.frobGenericMatrix).map conj.toRingHom =
      (T.letterRep n g⁻¹).map C * F * (T.letterRep n g).map C := by
    rw [← substitutionOperator_frobeniusCycle_map T C, substitutionOperator_map_eq_conj _ _ hg,
      h_frame, letterRep_map, letterRep_map, substitutionOperator_frobeniusCycle_map]
  have h_contraction : T.frobContraction n r ℓ m =
      T.letterRep n g⁻¹ * F.map (tensorDual l) * T.letterRep n g := by
    rw [← map_C_mul_mul_C, ← h_op, frobContraction, h_forms, Matrix.map_map, LinearMap.coe_comp,
      AlgHom.coe_toLinearMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [h_contraction, ← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

/-! ### One copy at a time -/

/-- The substitution in the frame `g`, that is `T.substitutionOperator` at the factors
`T.conjFrobGenericMatrix g`, is a matrix of polynomials in `N` generic matrices, the copies. It is
applied to the translate `T.letterRep n g *ᵥ h`, and the linear forms `l i` are applied in all
copies `i ≠ j`. The result is a vector, indexed by `β`, of polynomials in the entries of the copy
`j`. -/
def contractOtherCopies (r ℓ : ℕ) (l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O))
    (j : ZMod N) (g : GL (Fin k) W) (h : Exponents N k n → O) (β : Exponents N k n) :
    MvPolynomial (Fin k × Fin k) O :=
  ∑ γ : Exponents N k n, (T.letterRep n g *ᵥ h) γ •
    tensorDualExcept l j (T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g) β γ)

/-- Let `g` be block diagonal with blocks of sizes `r` and `k - r`, and let each `l i` be invariant
under `X ↦ g⁻¹ X g` through `T.embedding i` (`conjSubst`). Then a form `m` applied to the entries of
`T.contractOtherCopies r ℓ l j g h` gives the translate by `g` of `T.frobContraction n r ℓ l' *ᵥ h`,
where `l'` is `l` with `l j` replaced by `m` composed with the conjugation. -/
lemma map_contractOtherCopies {r ℓ : ℕ} {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    {j : ZMod N} {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r))
    (hl : ∀ (i : ZMod N) (ψ : MvPolynomial (Fin k × Fin k) O),
      l i (conjSubst (T.embedding i) g ψ) = l i ψ)
    (m : Dual O (MvPolynomial (Fin k × Fin k) O)) (h : Exponents N k n → O) (β : Exponents N k n) :
    m (T.contractOtherCopies r ℓ l j g h β) =
      (T.letterRep n g *ᵥ T.frobContraction n r ℓ
        (update l j (m ∘ₗ (conjSubst (T.embedding j) g).toLinearMap)) *ᵥ h) β := by
  have h_update (i : ZMod N) (ψ : MvPolynomial (Fin k × Fin k) O) :
      update l j (m ∘ₗ (conjSubst (T.embedding j) g).toLinearMap) i ψ =
        update l j m i (conjSubst (T.embedding i) g ψ) := by
    obtain rfl | hi := eq_or_ne i j <;> simp [*]
  calc m (T.contractOtherCopies r ℓ l j g h β)
      = ∑ γ : Exponents N k n, (T.letterRep n g *ᵥ h) γ * tensorDual (update l j m)
          (T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g) β γ) := by
        simp only [contractOtherCopies, map_sum, map_smul, map_tensorDualExcept, smul_eq_mul]
    _ = ((T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g)).map
          (tensorDual (update l j m)) *ᵥ T.letterRep n g *ᵥ h) β := by
        simp only [mulVec, dotProduct, Matrix.map_apply, mul_comm]
    _ = _ := by rw [mulVec_mulVec, mulVec_mulVec, T.letterRep_mul_frobContraction hg h_update]

/-- The entries of `T.contractOtherCopies r ℓ l j 1 h` are the polynomials in the `j`-th generic
matrix that are left when the forms `l i` are applied in the others. A form `m` applied to them
gives `T.frobContraction`, with `m` at the place `j` and `l i` at the others, applied to `h`. -/
lemma map_contractOtherCopies_one {r ℓ : ℕ} {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    {j : ZMod N} (m : Dual O (MvPolynomial (Fin k × Fin k) O)) (h : Exponents N k n → O)
    (β : Exponents N k n) :
    m (T.contractOtherCopies r ℓ l j 1 h β) = (T.frobContraction n r ℓ (update l j m) *ᵥ h) β := by
  simp [contractOtherCopies, conjFrobGenericMatrix_one, frobContraction, mulVec_apply, dotProduct,
    map_tensorDualExcept, one_apply, mul_comm]

/-- Change of basis. Let `F_g = T.contractOtherCopies r ℓ l j g h` be the vector of polynomials in
one generic matrix `X` that arises by substituting `N` generic matrices, in the basis given by `g`,
in the translate of `h` by `g`, and applying the linear forms `l i` in all of them but the `j`-th.
Let `g` be block diagonal with blocks of sizes `r` and `k - r`, and let each `l i` be invariant
under `X ↦ g⁻¹ X g` through `T.embedding i` (`conjSubst`). Then `F_1(g⁻¹ X g)`, with the conjugation
through `T.embedding j`, is the translate of `F_g(X)` by `g⁻¹`. -/
lemma conjSubst_contractOtherCopies_one {r ℓ : ℕ}
    {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)} {j : ZMod N} {g : GL (Fin k) W}
    (hg : g ∈ levi W (twoBlock k r))
    (hl : ∀ (i : ZMod N) (ψ : MvPolynomial (Fin k × Fin k) O),
      l i (conjSubst (T.embedding i) g ψ) = l i ψ)
    (h : Exponents N k n → O) (γ : Exponents N k n) :
    conjSubst (T.embedding j) g (T.contractOtherCopies r ℓ l j 1 h γ) =
      ∑ β : Exponents N k n, T.letterRep n g⁻¹ γ β • T.contractOtherCopies r ℓ l j g h β := by
  ext α
  let v : Exponents N k n → O := T.frobContraction n r ℓ
    (update l j (lcoeff O α ∘ₗ (conjSubst (T.embedding j) g).toLinearMap)) *ᵥ h
  have h_frame (β : Exponents N k n) :
      (T.contractOtherCopies r ℓ l j g h β).coeff α = (T.letterRep n g *ᵥ v) β :=
    T.map_contractOtherCopies hg hl (lcoeff O α) h β
  calc (conjSubst (T.embedding j) g (T.contractOtherCopies r ℓ l j 1 h γ)).coeff α
      = v γ := T.map_contractOtherCopies_one
        (lcoeff O α ∘ₗ (conjSubst (T.embedding j) g).toLinearMap) h γ
    _ = (T.letterRep n g⁻¹ *ᵥ T.letterRep n g *ᵥ v) γ := by simp [mulVec_mulVec, ← map_mul]
    _ = (∑ β : Exponents N k n,
          T.letterRep n g⁻¹ γ β • T.contractOtherCopies r ℓ l j g h β).coeff α := by
      simp [mulVec_apply, dotProduct, h_frame]

/-- Each polynomial `T.contractOtherCopies r ℓ l j 1 h β`, which is left in the `j`-th generic
matrix when the forms `l i` are applied in the others, has total degree at most
`N n k (ℓ + 2) P ^ ℓ`. -/
lemma contractOtherCopies_one_mem_restrictTotalDegree {r ℓ : ℕ}
    {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)} {j : ZMod N} (h : Exponents N k n → O)
    (β : Exponents N k n) :
    T.contractOtherCopies r ℓ l j 1 h β ∈
      restrictTotalDegree (Fin k × Fin k) O (N * n * k * (ℓ + 2) * T.P ^ ℓ) := by
  rw [contractOtherCopies, conjFrobGenericMatrix_one]
  exact Submodule.sum_mem _ fun γ _ ↦ Submodule.smul_mem _ _ <|
    tensorDualExcept_mem_restrictTotalDegree l j fun _ hν ↦
      T.degree_le_of_coeff_substitutionOperator hν j

/-- Weight and defect in one copy. Let `T` be a Frobenius cycle (`P = T.P`, `w = T.sqrtPrime`,
`w ^ 2 = p`) from a local ring `W` to a domain
`O` of characteristic `0` in which `p` is not a unit. Let `r = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ` and
`ℓ ≤ N`. Let each linear form `l i` be invariant under conjugation, through `T.embedding i`, by the
Levi subgroup of the blocks of sizes `r` and `k - r`. Let `β` be a monomial of degree `n` in each
letter. The polynomial `T.contractOtherCopies r ℓ l j g h β` in one generic matrix is the entry `β`
of the vector obtained from `T.letterRep n g *ᵥ h` by substituting the `N` generic matrices
conjugated by `g` and applying the `l i` in all of them but the `j`-th. Let its coefficient of `α`
not be divisible by `w ^ c`. Then the row weight of `α` (its degree in the row `r` minus its degree
in the row `a`), divided by `P ^ ℓ`, is within `defectThreshold k c = 3 k c` of the defect of `β` at
the letter `j + ℓ`. The defect is a weighted sum over all letters of the degrees of `β` in the
variables `a` and `r`, with the real weights `T.defectWeight (j + ℓ) a r`; `exponentOf β` is `β` as
one exponent vector. -/
lemma abs_weight_div_sub_defect_le [IsDomain O] [CharZero O] {a r : Fin k} {ℓ c : ℕ}
    (hp : ¬IsUnit (T.p : O)) (ha : a + 1 = r.val) (h_size : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ)
    (hℓ : ℓ ≤ N) {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hl : ∀ i : ZMod N, ∀ u ∈ levi W (twoBlock k r), ∀ ψ : MvPolynomial (Fin k × Fin k) O,
      l i (conjSubst (T.embedding i) u ψ) = l i ψ)
    {j : ZMod N} {g : GL (Fin k) W} {h : Exponents N k n → O} {β : Exponents N k n}
    {α : Fin k × Fin k →₀ ℕ}
    (h_coeff : ¬T.sqrtPrime ^ c ∣ (T.contractOtherCopies r ℓ l j g h β).coeff α) :
    |(α.weight (fun v : Fin k × Fin k ↦ rootVector a r v.1) : ℤ) / (T.P : ℝ) ^ ℓ -
      (exponentOf β).weight (T.defectWeight (j + ℓ) a r)| ≤ defectThreshold k c := by
  -- Some monomial `ν` in all copies, with the part `α` in the copy `j`, has a coefficient that is
  -- not divisible by `w ^ c`, and for `i ≠ j` no `l i` kills its part in the copy `i`.
  obtain ⟨γ, hγ⟩ : ∃ γ : Exponents N k n, ¬T.sqrtPrime ^ c ∣ (tensorDualExcept l j
      (T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g) β γ)).coeff α := by
    contrapose! h_coeff with h_all
    simpa [contractOtherCopies, coeff_sum] using dvd_sum fun γ _ ↦ (h_all γ).mul_left _
  obtain ⟨ν, rfl, hν, h_ne_zero⟩ : ∃ ν : ZMod N × Fin k × Fin k →₀ ℕ, ν.curry j = α ∧
      ¬T.sqrtPrime ^ c ∣ (T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g) β γ).coeff ν ∧
      ∀ i ≠ j, l i (monomial (ν.curry i) 1) ≠ 0 := exists_of_not_dvd_coeff_tensorDualExcept hγ
  -- An invariant form kills the monomials whose row and column weights differ, so the copies
  -- `i ≠ j` contribute nothing to the weight of `ν`.
  have h_balanced (i : ZMod N) (hi : i ∈ univ.erase j) :
      (ν.curry i).weight (fun v : Fin k × Fin k ↦ rootVector a r v.1) =
        (ν.curry i).weight (fun v : Fin k × Fin k ↦ rootVector a r v.2) := by
    by_contra h_ne
    exact h_ne_zero i (ne_of_mem_erase hi) (apply_monomial_eq_zero_of_weight_ne (twoBlock k r)
      (T.embedding i) T.prime.pos hp (rootVector a r) (hl i) h_ne)
  have h_weight : T.copyWeight ℓ a r j ν =
      ((ν.curry j).weight (fun v : Fin k × Fin k ↦ rootVector a r v.1) : ℤ) / T.P ^ ℓ := by
    rw [copyWeight,
      Finset.sum_eq_zero fun i hi ↦ by rw [h_balanced i hi, sub_self, mul_zero], add_zero]
  rw [← h_weight, abs_sub_comm]
  exact T.abs_defect_sub_copyWeight_le ha j h_size hℓ g hν

/-- Let `T` be a Frobenius cycle from a local ring `W` to a domain `O` of characteristic `0` in
which `p` is not a unit. Let `r = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ` and `ℓ ≤ N`. Let each linear form
`l i` be invariant under conjugation, through `T.embedding i`, by the Levi subgroup of the blocks of
sizes `r` and `k - r`. Let `β` be a monomial of degree `n` in each letter. The polynomial
`T.contractOtherCopies r ℓ l j g h β` in one generic matrix is the entry `β` of the vector obtained
from `T.letterRep n g *ᵥ h` by substituting the `N` generic matrices conjugated by `g` and applying
the `l i` in all of them but the `j`-th. Let its coefficient of `α` not be divisible by `w ^ c`, and
put `c* = 3 k c`. The row weight of `α` is its degree in the row `r` minus its degree in the row
`a`, and the defect of `β` at the letter `j + ℓ` is its weighted degree for the weights
`T.defectWeight (j + ℓ) a r`. If the defect is above `3 c*`, then the row weight is above
`2 c* P ^ ℓ`; if the row weight is above `2 c* P ^ ℓ`, then the defect is above `c*`. -/
lemma lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies [IsDomain O] [CharZero O]
    {a r : Fin k} {ℓ c : ℕ} (hp : ¬IsUnit (T.p : O))
    (ha : a + 1 = r.val) (h_size : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ) (hℓ : ℓ ≤ N)
    {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hl : ∀ i : ZMod N, ∀ u ∈ levi W (twoBlock k r), ∀ ψ : MvPolynomial (Fin k × Fin k) O,
      l i (conjSubst (T.embedding i) u ψ) = l i ψ)
    {j : ZMod N} {g : GL (Fin k) W} {h : Exponents N k n → O} {β : Exponents N k n}
    {α : Fin k × Fin k →₀ ℕ}
    (h_coeff : ¬T.sqrtPrime ^ c ∣ (T.contractOtherCopies r ℓ l j g h β).coeff α) :
    (3 * defectThreshold k c < (exponentOf β).weight (T.defectWeight (j + ℓ) a r) →
      2 * defectThreshold k c * (T.P : ℤ) ^ ℓ <
        α.weight (fun v : Fin k × Fin k ↦ rootVector a r v.1)) ∧
    (2 * defectThreshold k c * (T.P : ℤ) ^ ℓ <
        α.weight (fun v : Fin k × Fin k ↦ rootVector a r v.1) →
      defectThreshold k c < (exponentOf β).weight (T.defectWeight (j + ℓ) a r)) := by
  set wt : ℤ := α.weight fun v : Fin k × Fin k ↦ rootVector a r v.1
  have h_bad_iff : 2 * defectThreshold k c * (T.P : ℤ) ^ ℓ < wt ↔
      2 * defectThreshold k c < wt / (T.P : ℝ) ^ ℓ := by
    rw [lt_div_iff₀ (pow_pos (zero_lt_one.trans T.one_lt_P) ℓ)]
    norm_cast
  obtain ⟨h_lower, h_upper⟩ :=
    abs_le.1 (T.abs_weight_div_sub_defect_le hp ha h_size hℓ hl h_coeff)
  rw [h_bad_iff]
  constructor <;> intro <;> linarith

/-! ### The averaging map -/

/-- The map `Av_J`: the substitution `T.substitutionOperator` at generic matrices, one for each
letter, is applied, then the forms `I j` (averages, in the applications) in the copies `j ∈ J` and
`p ^ c₀` times the evaluation at the identity matrix in the other copies,
`c₀ = T.multinomialExponent k`. -/
def partialAverage (n r ℓ : ℕ) (I : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O))
    (J : Finset (ZMod N)) : Matrix (Exponents N k n) (Exponents N k n) O :=
  T.frobContraction n r ℓ
    (J.piecewise I fun _ : ZMod N ↦ evalAtOne ((T.p : O) ^ T.multinomialExponent k))

/-- With no average, the map `Av_∅` is `p ^ (N c₀)` times the identity, where
`c₀ = T.multinomialExponent k`. -/
lemma partialAverage_empty {ℓ : ℕ} (r : ℕ) (I : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)) :
    T.partialAverage n r ℓ I ∅ = (T.p : O) ^ (N * T.multinomialExponent k) • 1 := by
  rw [partialAverage, piecewise_empty, frobContraction_evalAtOne, ← pow_mul, mul_comm]

/-- Let `T` be a Frobenius cycle over a domain `O` of characteristic `0` in which `p` is not a unit.
Let `r = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ` and `ℓ ≤ N`, and put `c* = 3 k c`. Let the `I j` be
averages; they are linear forms on polynomials in a generic matrix, invariant under the Levi
subgroup of the blocks of sizes `r` and `k - r`, that vanish on the monomials of row weight above
`2 c* P ^ ℓ`. Let `Av = T.partialAverage n r ℓ I univ` be the matrix obtained from the substitution
of `N` generic matrices by applying `I j` in the `j`-th one for every `j`. Then for every
coefficient vector `h`, `w ^ c` divides the coefficient in each Levi translate of `Av h` of each
monomial with defect above `3 c*` at some letter; the defect is the weighted degree for
`T.defectWeight`. -/
lemma partialAverage_univ_mulVec_mem_defectConditions [IsDomain O] [CharZero O] {a r : Fin k}
    {ℓ c : ℕ} (hp : ¬IsUnit (T.p : O)) (ha : a + 1 = r.val)
    (h_size : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ) (hℓ : ℓ ≤ N) {D : ℕ}
    {I : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hI : ∀ j : ZMod N, IsAverage (twoBlock k r) (T.embedding j) (rootVector a r)
      (2 * defectThreshold k c * T.P ^ ℓ) ((T.p : O) ^ T.multinomialExponent k) D (I j))
    (h : Exponents N k n → O) :
    T.partialAverage n r ℓ I univ *ᵥ h ∈
      T.defectConditions n a r (span {T.sqrtPrime ^ c}) (3 * defectThreshold k c) := by
  rintro g hg β ⟨i, h_defect⟩
  obtain ⟨j, rfl⟩ : ∃ j : ZMod N, j + ℓ = i := ⟨i - ℓ, sub_add_cancel i ℓ⟩
  -- The translate by `g` is `I j` applied to the polynomial that remains in the copy `j`.
  have h_invariant : I j ∘ₗ (conjSubst (T.embedding j) g).toLinearMap = I j :=
    LinearMap.ext ((hI j).map_conjSubst g hg)
  have h_value : (T.letterRep n g *ᵥ T.partialAverage n r ℓ I univ *ᵥ h) β =
      I j (T.contractOtherCopies r ℓ I j g h β) := by
    rw [T.map_contractOtherCopies hg fun i ↦ (hI i).map_conjSubst g hg, h_invariant, update_eq_self,
      partialAverage, piecewise_univ]
  rw [mem_span_singleton, h_value]
  -- Modulo `w ^ c` this polynomial has only bad monomials, on which `I j` vanishes.
  refine dvd_map_of_forall_monomial fun α h_coeff ↦ (hI j).map_monomial_eq_zero α ?_
  exact (T.lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies hp ha h_size hℓ
    (fun i ↦ (hI i).map_conjSubst) h_coeff).1 h_defect

/-- Let `T` be a Frobenius cycle over a valuation domain `O` of characteristic `0` in which `p` is
not a unit. Let `r = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ` and `ℓ ≤ N`, and put `c* = 3 k c` and
`c₀ = T.multinomialExponent k`. Let the `I j` be averages up to the degree `N n k (ℓ + 2) P ^ ℓ`,
whose bad monomials are those of row weight above `2 c* P ^ ℓ`. The matrix
`Av_J = T.partialAverage n r ℓ I J` arises from the substitution of `N` generic matrices by applying
`I i` in the `i`-th one for `i ∈ J`, and `p ^ c₀` times the evaluation at `1` for `i ∉ J`. Let the
weights `b` define a pairing `⟨h, h'⟩ = ∑_β h'_β b_β h_β` that makes the matrices of `g` and `gᵀ`
adjoint, with `b b' = p ^ (N c₀)`. Let `h' ∈ T.allEdgesForms k n r`: it is `w ^ (-m) Δ f` for a
vector `f` over `O` with `w ^ (-m) Δ g f` integral for all `g ∈ GL_k(W)`, where
`Δ = T.depthScaling k n r` is a diagonal matrix of powers of `w`. Then
`⟨Av_{J ∪ {j}} h, h'⟩ ≡ ⟨Av_J h, h'⟩` modulo `w ^ c` for `j ∉ J`. -/
lemma pow_dvd_pairing_partialAverage_insert_sub [IsDomain O] [CharZero O] {a r : Fin k} {ℓ c : ℕ}
    [ValuationRing O] (hp : ¬IsUnit (T.p : O))
    (ha : a + 1 = r.val) (h_size : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ) (hℓ : ℓ ≤ N)
    {I : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hI : ∀ j : ZMod N, IsAverage (twoBlock k r) (T.embedding j) (rootVector a r)
      (2 * defectThreshold k c * T.P ^ ℓ) ((T.p : O) ^ T.multinomialExponent k)
      (N * n * k * (ℓ + 2) * T.P ^ ℓ) (I j))
    {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b') {J : Finset (ZMod N)} {j : ZMod N}
    (hj : j ∉ J) (h : Exponents N k n → O) {h' : Exponents N k n → O}
    (hh' : h' ∈ T.allEdgesForms k n r) :
    T.sqrtPrime ^ c ∣ h' ⬝ᵥ (b * T.partialAverage n r ℓ I (insert j J) *ᵥ h) -
      h' ⬝ᵥ (b * T.partialAverage n r ℓ I J *ᵥ h) := by
  -- The difference is `(I j - ev) ψ` for the pairing `ψ` of `h'` with the polynomials that remain
  -- in the copy `j`. It is enough to show that the bad monomials of the conjugates of `ψ` have
  -- coefficients divisible by `w ^ c`.
  let ev : Dual O (MvPolynomial (Fin k × Fin k) O) :=
    evalAtOne ((T.p : O) ^ T.multinomialExponent k)
  let l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O) := J.piecewise I fun _ ↦ ev
  have hl (i : ZMod N) (u : GL (Fin k) W) (hu : u ∈ levi W (twoBlock k r))
      (φ : MvPolynomial (Fin k × Fin k) O) : l i (conjSubst (T.embedding i) u φ) = l i φ := by
    by_cases hi : i ∈ J <;> simp [l, ev, hi, (hI i).map_conjSubst u hu, evalAtOne_conjSubst]
  let ψ : MvPolynomial (Fin k × Fin k) O :=
    ∑ β : Exponents N k n, (h' β * b β) • T.contractOtherCopies r ℓ l j 1 h β
  have hψ (m : Dual O (MvPolynomial (Fin k × Fin k) O)) :
      m ψ = h' ⬝ᵥ (b * T.frobContraction n r ℓ (update l j m) *ᵥ h) := by
    simp [ψ, T.map_contractOtherCopies_one, dotProduct, mul_assoc]
  have h_degree : ψ.totalDegree ≤ N * n * k * (ℓ + 2) * T.P ^ ℓ := (mem_restrictTotalDegree ..).1 <|
    sum_mem fun β _ ↦ Submodule.smul_mem _ _ (T.contractOtherCopies_one_mem_restrictTotalDegree h β)
  have h_update_ev : update l j ev = l :=
    update_eq_self_iff.2 (piecewise_eq_of_notMem J I (fun _ ↦ ev) hj).symm
  suffices h_mem : I j ψ - ev ψ ∈ span {T.sqrtPrime ^ c} by
    rwa [hψ, hψ, h_update_ev, mem_span_singleton, ← piecewise_insert] at h_mem
  refine (hI j).sub_evalAtOne_mem (span {T.sqrtPrime ^ c}) ψ h_degree fun g hg α h_bad ↦ ?_
  -- The coefficient of `α` in the conjugate of `ψ` is a combination of the pairings of `h'` with
  -- the translates by `g⁻¹` of the monomials `β`. The scalars are coefficients of
  -- `contractOtherCopies` in the frame `g`.
  have h_coeff : (conjSubst (T.embedding j) g ψ).coeff α = ∑ β : Exponents N k n,
      (T.contractOtherCopies r ℓ l j g h β).coeff α *
        h' ⬝ᵥ (b * T.letterRep n g⁻¹ *ᵥ Pi.single β 1) := by
    simp only [ψ, map_sum, map_smul, T.conjSubst_contractOtherCopies_one hg fun i ↦ hl i g hg,
      coeff_sum, coeff_smul, smul_eq_mul, mulVec_single_one, dotProduct, Pi.mul_apply, col_apply,
      mul_sum]
    exact sum_comm.trans (sum_congr rfl fun β _ ↦ sum_congr rfl fun γ _ ↦ by ring)
  rw [mem_span_singleton, h_coeff]
  refine dvd_sum fun β _ ↦ ?_
  by_cases h_dvd : T.sqrtPrime ^ c ∣ (T.contractOtherCopies r ℓ l j g h β).coeff α
  · exact h_dvd.mul_right _
  · -- As `α` is bad, the defect of `β` is large, so the pairing is divisible by `w ^ c`.
    have h_defect : defectThreshold k c < (exponentOf β).weight (T.defectWeight (j + ℓ) a r) :=
      (T.lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies hp ha h_size hℓ hl
        h_dvd).2 h_bad
    have h_lt : a < r := Fin.lt_def.2 (by lia)
    exact (hb.pow_dvd_pairing_letterRep T h_lt hh' (inv_mem hg) h_defect).mul_left _

/-- The averaging map. Let `T` be a Frobenius cycle (`P = T.P`, `w = T.sqrtPrime`, `w ^ 2 = p`)
over a valuation domain `O` of characteristic
`0` in which `p` is not a unit. Vectors are coefficient vectors of polynomials of degree `n` in each
of `N` groups of `k` variables, on which `GL_k(W)` acts by `T.letterRep n`. Let `r = a + 1`,
`N = 2 ℓ` and `N k (ℓ + 2) n + n + k < P ^ ℓ`. Put `c* = 3 k c` and
`c₀ = T.multinomialExponent k = k² log_p P^N`. Let the weights `b` define a pairing
`⟨h, h'⟩ = ∑_β h'_β b_β h_β` that makes the matrices of `g` and `gᵀ` adjoint, with
`b b' = p ^ (N c₀)`. For every `c` there is a matrix `Av` with two properties.
* For all `h` and all `g` in the Levi subgroup of the blocks of sizes `r` and `k - r`, `w ^ c`
  divides the coefficient in `g Av h` of each monomial with defect above `3 c*` at some letter `i`;
  the defect is the weighted degree for the weights `T.defectWeight i a r`.
* `⟨Av h, h'⟩ ≡ p ^ (N c₀) ⟨h, h'⟩` modulo `w ^ c` for all `h` and all
  `h' ∈ T.allEdgesForms k n r`. -/
theorem exists_average_mem_defectConditions_and_dvd_sub [IsDomain O] [CharZero O] {a r : Fin k}
    [ValuationRing O] (hp : ¬IsUnit (T.p : O)) (ha : a + 1 = r.val) {ℓ : ℕ}
    (hℓ : ℓ + ℓ = N) (h_size : N * k * (ℓ + 2) * n + n + k < T.P ^ ℓ)
    {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b') (c : ℕ) :
    ∃ Av : Matrix (Exponents N k n) (Exponents N k n) O,
      (∀ h : Exponents N k n → O,
        Av *ᵥ h ∈ T.defectConditions n a r (span {T.sqrtPrime ^ c}) (3 * defectThreshold k c)) ∧
      ∀ (h : Exponents N k n → O), ∀ h' ∈ T.allEdgesForms k n r,
        T.sqrtPrime ^ c ∣ h' ⬝ᵥ (b * Av *ᵥ h) -
          (T.p : O) ^ (N * T.multinomialExponent k) * h' ⬝ᵥ (b * h) := by
  obtain ⟨h_small, hℓ_le⟩ : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ ∧ ℓ ≤ N := by lia
  -- `D` bounds the degree in one copy; it is small against `P ^ N`, so the averages exist.
  let D : ℕ := N * n * k * (ℓ + 2) * T.P ^ ℓ
  have hD : D + k < T.P ^ N :=
    calc D + k < D + T.P ^ ℓ := by lia
      _ = (N * k * (ℓ + 2) * n + 1) * T.P ^ ℓ := by ring
      _ ≤ T.P ^ ℓ * T.P ^ ℓ := Nat.mul_le_mul_right _ (by lia)
      _ = T.P ^ N := by rw [← pow_add, hℓ]
  have hD_pow : D < T.p ^ (T.frobExp * N) := by
    simpa only [pow_mul] using (Nat.le_add_right D k).trans_lt hD
  have h_exists (j : ZMod N) : ∃ I : Dual O (MvPolynomial (Fin k × Fin k) O),
      IsAverage (twoBlock k r) (T.embedding j) (rootVector a r) (2 * defectThreshold k c * T.P ^ ℓ)
        ((T.p : O) ^ T.multinomialExponent k) D I :=
    exists_isAverage (twoBlock k r) (T.embedding j) T.prime hp (T.frobExp * N) hD_pow
      (hD.le.trans_eq T.card_residueField.symm) _ _
  choose I hI using h_exists
  refine ⟨T.partialAverage n r ℓ I univ,
    T.partialAverage_univ_mulVec_mem_defectConditions hp ha h_small hℓ_le hI, fun h h' hh' ↦ ?_⟩
  -- Add the differences along a chain of subsets that starts at `∅`.
  have h_chain (J : Finset (ZMod N)) :
      T.sqrtPrime ^ c ∣ h' ⬝ᵥ (b * T.partialAverage n r ℓ I J *ᵥ h) -
        (T.p : O) ^ (N * T.multinomialExponent k) * h' ⬝ᵥ (b * h) := by
    induction J using Finset.induction_on with
    | empty => simp [partialAverage_empty, smul_mulVec]
    | insert j J hj ih =>
      simpa only [sub_add_sub_cancel] using dvd_add
        (T.pow_dvd_pairing_partialAverage_insert_sub hp ha h_small hℓ_le hI hb hj h hh') ih
  exact h_chain univ

end FrobeniusCycle

end New

end
