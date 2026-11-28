import Lib.General.LinearAlgebra.HermiteForm
import Lib.LocalGL.Green.HallAlgebra
import New.UpperBound.ElementaryDivisors.InvariantAverage
import New.UpperBound.ElementaryDivisors.RootLemma

/-!
# Edges, halfway lattices and duality

An edge is a pair of lattices `L' ⊆ L` with `p L ⊆ L'` and `L / L'` of dimension `r` over the
residue field; `L'` is its origin. Let `w ^ 2 = p`, and consider forms of degree `n` in each of `N`
letters, with `k` variables in each letter. In a basis of `L'` adapted to the edge, the forms that
are integral for the lattice `L' + w L`, times `w ^ (-n N / 2)`, have as basis the normalized
monomials `w ^ (-depth β) z ^ β`, where the depth is the degree in the deep variables
(`New.FrobeniusCycle.deepIndicator`). This module of forms is the halfway lattice of the edge. The
file works with coefficient vectors in the normalized monomials, so the halfway lattice is the
module of all vectors.

* `New.monomialLattice`, `New.dividedPowerLattice`: the spans `H ⊇ H°` of the monomials `z ^ β` and
  of the `(n! ^ N / β!) z ^ β`; both are stable under `GL_k(W)`.
* `New.FrobeniusCycle.allEdgesForms`: the forms that lie in the halfway lattices of all edges from
  `L'`.
* `New.FrobeniusCycle.IsEdgePairing`: weights of a pairing for which `ρ(g)` and `ρ(gᵀ)` are adjoint;
  it pairs the halfway lattices of an edge and its dual.
* `New.FrobeniusCycle.edgeRestriction`, `New.FrobeniusCycle.originFunctions`: functions on origins
  as functions on edges, and the functions on edges that depend only on the origin.
* `New.FrobeniusCycle.exists_originFunctions_factorization_det_dvd`,
  `New.FrobeniusCycle.mulVec_mulVec_eq_self_of_mem_originFunctions`: if every edge occurs, these
  functions form a direct summand, in which the integral functions on origins have small colength.
* `New.FrobeniusCycle.pow_dvd_letterRep_mulVec_of_mem_allEdgesForms`,
  `New.FrobeniusCycle.IsEdgePairing.pow_dvd_pairing_letterRep`: vectors in `allEdgesForms` have
  coefficients divisible by a power of `w` at monomials of large defect, and pair with these
  monomials to multiples of a power of `w`.

Notions from other files:
* `New.FrobeniusCycle`: a prime `p`, ring maps from `W` to `O` indexed by the letters `s ∈ ℤ/N`,
  which are alternately even and odd, and an element `w` of `O` with `w ^ 2 = p`.
* `New.FrobeniusCycle.letterRep`: the matrix `ρ(g)` of `g ∈ GL_k(W)` on coefficient vectors. It
  substitutes the image of `g` in even letters and of its inverse transpose in odd letters;
  `ρ(g) h` is the translate of `h` by `g`.
* `New.twoBlock`: the blocks of sizes `r` and `k - r`; `New.parahoric`, `New.levi`: the stabilizer
  of the edge and the block diagonal subgroup.
* `New.FrobeniusCycle.translatesIn`: vectors whose translates by a Levi subgroup have coefficients
  in an ideal at a set of monomials. Two cases are `New.FrobeniusCycle.deepForms` (no translate has
  a monomial of depth below a bound) and `New.FrobeniusCycle.defectConditions`.
* `New.FrobeniusCycle.defectWeight`: real weights on the two variables of a root in each letter; the
  defect of a monomial is its weighted degree, and `defectConditions` is the condition on block
  diagonal translates at the monomials of large defect.

## Relation to the literature

See `New.UpperBound.Divisibility.LocalDivisibility` for related work.
-/

noncomputable section

namespace New

open MvPolynomial Matrix IsLocalRing Function Module Finset Fintype Ideal

/-- The left cosets of the parahoric subgroup with blocks of sizes `r` and `k - r`. For `r ≤ k` they
index the edges into the lattice `W ^ k`, that is, the sublattices that contain `𝔪 W ^ k`, for the
maximal ideal `𝔪` of `W`, and have a quotient of dimension `r` over the residue field: the
parahoric subgroup is the stabilizer of one of them. As matrices act transposed, the same cosets
index the edges from a lattice, which is how they are used here. -/
abbrev ParahoricCosets (W : Type) [CommRing W] [IsLocalRing W] (k r : ℕ) : Type :=
  GL (Fin k) W ⧸ parahoric W (twoBlock k r)

/-! ### Linear algebra and divisibility -/

/-- Elementary divisors of a matrix `J` over a valuation domain with at least as many rows as
columns, as witnessed by an embedding `ι` of the column indices in the row indices: there are an
invertible `P` and a matrix `Q` with a left inverse `R` such that column `i` of `J * P⁻¹` is `t i`
times column `i` of `Q`. -/
lemma exists_mul_inv_eq_mul_diagonal {O I I' : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (ι : I ↪ I') (J : Matrix I' I O) :
    ∃ (Q : Matrix I' I O) (R : Matrix I I' O) (P : GL I O) (t : I → O),
      R * Q = 1 ∧ J * P⁻¹.val = Q * diagonal t := by
  -- A Hermite form reduces `J` to a square matrix `D`, which has a Smith form.
  obtain ⟨U, -, D, -, hJ : J = U.val.submatrix id ι * D, -⟩ := isValuationPair_top.hermite ι J
  obtain ⟨K, -, P, -, t, rfl : D = K.val * diagonal t * P.val⟩ :=
    isValuationPair_top.smith_normal_form D
  have hU : U⁻¹.val.submatrix ι id * U.val.submatrix id ι = 1 := by
    rw [← submatrix_mul U⁻¹.val U.val ι id ι bijective_id, U.inv_mul, submatrix_one_embedding]
  refine ⟨U.val.submatrix id ι * K.val, K⁻¹.val * U⁻¹.val.submatrix ι id, P, t, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ K.val, hU, Matrix.one_mul, K.inv_mul]
  · simp only [hJ, Matrix.mul_assoc, P.mul_inv, Matrix.mul_one]

/-- Vectors with dual rows are independent modulo the maximal ideal. Let the columns `j ∈ s` of `Q`
have dual rows in `R`, that is, column `j` of `R * Q` is the `j`-th unit vector. Suppose that for
each `x ∈ X` the block `i ↦ Q (x, i) j` of such a column reduces into the subspace `S` over the
residue field. Then `s` has at most `|X| dim S` elements. -/
lemma card_le_mul_finrank_of_dual_rows {O X I E : Type*} [CommRing O] [IsLocalRing O] [Fintype X]
    [Fintype I] [DecidableEq E] (Q : Matrix (X × I) E O) (R : Matrix E (X × I) O) {s : Finset E}
    {S : Submodule (ResidueField O) (I → ResidueField O)}
    (h_dual : ∀ j ∈ s, ∀ i : E, (R * Q) i j = if i = j then 1 else 0)
    (h_mem : ∀ j ∈ s, ∀ x : X, (fun i : I ↦ residue O (Q (x, i) j)) ∈ S) :
    #s ≤ Fintype.card X * finrank (ResidueField O) S := by
  let v (j : s) (x : X) : S := ⟨fun i ↦ residue O (Q (x, i) j), h_mem j (coe_mem j) x⟩
  have h_indep : LinearIndependent (ResidueField O) v := by
    refine Fintype.linearIndependent_iff.2 fun c hc i ↦ ?_
    have h_entry (y : X × I) : ∑ j : s, c j * residue O (Q y j) = 0 := by
      simpa [v] using congrArg (fun f : X → S ↦ S.subtype (f y.1) y.2) hc
    -- Pair the relation with row `i` of `R`: only the coefficient `c i` survives.
    calc c i = ∑ j : s, c j * residue O ((R * Q) i j) := by
          simp [h_dual, apply_ite (residue O)]
      _ = ∑ y : X × I, residue O (R i y) * ∑ j : s, c j * residue O (Q y j) := by
          simp only [Matrix.mul_apply, map_sum, map_mul, mul_sum, mul_left_comm]
          exact sum_comm
      _ = 0 := by simp only [h_entry, mul_zero, sum_const_zero]
  simpa [finrank_pi_fintype] using h_indep.fintype_card_le_finrank

/-- If every `t i` divides `w ^ x`, then their product divides `w ^ l`, where `l` counts the pairs
`(i, δ)` with `δ < x` such that `t i` does not divide `w ^ δ`. -/
lemma prod_dvd_pow_sum_card {O I : Type*} [CommRing O] [DecidableRel fun y z : O ↦ y ∣ z]
    [Fintype I] {t : I → O} {w : O} {x : ℕ} (ht : ∀ i : I, t i ∣ w ^ x) :
    ∏ i : I, t i ∣ w ^ ∑ δ ∈ range x, #{i : I | ¬t i ∣ w ^ δ} := by
  -- The least `l` with `t i ∣ w ^ l` is at most the number of `δ < x` with `¬t i ∣ w ^ δ`.
  have h_one (i : I) : t i ∣ w ^ #{δ ∈ range x | ¬t i ∣ w ^ δ} := by
    have h_ex : ∃ l : ℕ, t i ∣ w ^ l := ⟨x, ht i⟩
    have h_range : range (Nat.find h_ex) ⊆ {δ ∈ range x | ¬t i ∣ w ^ δ} := by
      simp only [subset_iff, mem_filter, Finset.mem_range]
      exact fun δ hδ ↦ ⟨hδ.trans_le (Nat.find_min' h_ex (ht i)), Nat.find_min h_ex hδ⟩
    refine (Nat.find_spec h_ex).trans (pow_dvd_pow w ?_)
    simpa only [Finset.card_range] using card_le_card h_range
  have h_count : ∑ i : I, #{δ ∈ range x | ¬t i ∣ w ^ δ} =
      ∑ δ ∈ range x, #{i : I | ¬t i ∣ w ^ δ} := by simp only [card_filter, sum_comm (s := range x)]
  rw [← h_count, ← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ fun i _ ↦ h_one i

/-- Cancelling a power of `w ≠ 0` in a divisibility: if `w ^ m` divides `w ^ d * x`, then
`w ^ (m - d)` divides `x`, with truncated subtraction. -/
lemma pow_sub_dvd_of_pow_dvd_pow_mul {O : Type} [CommRing O] [IsDomain O] {w x : O} (hw : w ≠ 0)
    {m d : ℕ} (h_dvd : w ^ m ∣ w ^ d * x) : w ^ (m - d) ∣ x := by
  obtain hmd | hdm := le_total m d
  · simp [Nat.sub_eq_zero_of_le hmd]
  · rwa [← Nat.add_sub_cancel' hdm, pow_add, mul_dvd_mul_iff_left (pow_ne_zero d hw)] at h_dvd

/-! ### The two lattices of forms -/

section Lattices

open Nat

variable {N k n : ℕ} [NeZero N] (O K : Type) [CommRing O] [CommRing K] [Algebra O K]

/-- The number `n! ^ N / β!` for an exponent `β` of degree `n` in each of the `N` letters, where
`β!` is the product of the factorials of all entries of `β`. -/
def dividedPowerCoeff (β : Exponents N k n) : ℕ :=
  n ! ^ N / ∏ s : ZMod N, ∏ b : Fin k, ((β s).val b)!

/-- The number `n! ^ N / β!` is the product over the letters `s` of the multinomial coefficients of
the exponent vectors `β s`. -/
lemma dividedPowerCoeff_eq_prod_multinomial (β : Exponents N k n) :
    dividedPowerCoeff β = ∏ s : ZMod N, multinomial univ (β s).val := by
  have h_letter (s : ZMod N) :
      (∏ b : Fin k, ((β s).val b)!) * multinomial univ (β s).val = n ! := by
    rw [multinomial_spec, (mem_finsuppAntidiag.1 (β s).property).left]
  refine Nat.div_eq_of_eq_mul_right (by positivity) ?_
  simp [← prod_mul_distrib, h_letter]

variable (N k n) in
/-- The lattice `H` of forms with coefficients in `O`: the `O`-span, in the polynomials over the
`O`-algebra `K`, of the monomials `z ^ β` of degree `n` in each of the `N` letters, with `k`
variables in each letter. -/
def monomialLattice : Submodule O (MvPolynomial (Fin k × ZMod N) K) :=
  Submodule.span O (Set.range fun β : Exponents N k n ↦ monomial (exponentOf β) (1 : K))

variable (N k n) in
/-- The lattice `H°` of divided powers: the `O`-span, in the polynomials over the `O`-algebra `K`,
of the `(n! ^ N / β!) z ^ β`, for the monomials `z ^ β` of degree `n` in each of the `N` letters,
with `k` variables in each letter. -/
def dividedPowerLattice : Submodule O (MvPolynomial (Fin k × ZMod N) K) :=
  Submodule.span O
    (Set.range fun β : Exponents N k n ↦ monomial (exponentOf β) (dividedPowerCoeff β : K))

/-- The span `H°` of the `(n! ^ N / β!) z ^ β` lies in the span `H` of the monomials `z ^ β`. -/
theorem dividedPowerLattice_le_monomialLattice :
    dividedPowerLattice N k n O K ≤ monomialLattice N k n O K := by
  refine Submodule.span_le.2 (Set.range_subset_iff.2 fun β ↦ ?_)
  have h_mem : monomial (exponentOf β) (1 : K) ∈ monomialLattice N k n O K :=
    Submodule.subset_span ⟨β, rfl⟩
  simpa [smul_monomial] using nsmul_mem h_mem (dividedPowerCoeff β)

/-- Over a domain of characteristic `0`, the `n`-th symmetric powers of a matrix `A` and of `Aᵀ` are
transposes of each other up to the multinomial coefficients of the exponents. -/
lemma symPowMatrix_mul_multinomial {σ O : Type} [Fintype σ] [DecidableEq σ] [CommRing O]
    [IsDomain O] [CharZero O] {n : ℕ} (A : Matrix σ σ O) (α β : Monomials σ n) :
    symPowMatrix n A α β * multinomial univ β.val =
      multinomial univ α.val * symPowMatrix n Aᵀ β α := by
  -- Multiply by `α! β!` and use `γ! * multinomial γ = n!` in degree `n`.
  let fact (γ : Monomials σ n) : ℕ := ∏ i : σ, (γ.val i)!
  have h_fact (γ : Monomials σ n) : (fact γ : O) * multinomial univ γ.val = n ! := by
    rw [← cast_mul, multinomial_spec, (mem_finsuppAntidiag.1 γ.property).left]
  have h_ne (γ : Monomials σ n) : (fact γ : O) ≠ 0 := cast_ne_zero.2 (by positivity)
  have h_adjoint : fact α * symPowMatrix n A α β = fact β * symPowMatrix n Aᵀ β α :=
    Average.prod_factorial_mul_coeff_linSubst A α.val β.val
  refine mul_left_cancel₀ (mul_ne_zero (h_ne α) (h_ne β)) ?_
  calc fact α * fact β * (symPowMatrix n A α β * multinomial univ β.val)
      = fact α * symPowMatrix n A α β * (fact β * multinomial univ β.val) := by ring
    _ = fact β * symPowMatrix n Aᵀ β α * (fact α * multinomial univ α.val) := by
        rw [h_adjoint, h_fact, h_fact]
    _ = fact α * fact β * (multinomial univ α.val * symPowMatrix n Aᵀ β α) := by ring

end Lattices

namespace FrobeniusCycle

section Edges
variable {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O]
  (T : FrobeniusCycle N W O)

/-- A coefficient vector `v` lies in `T.translatesIn n τ I B` if and only if its translates by the
Levi subgroup of the labelling `τ` have their coefficients at the exponents in `B` in `I`. -/
lemma mem_translatesIn_iff {τ : Fin k → ℕ} {I : Ideal O} {B : Set (Exponents N k n)}
    {v : Exponents N k n → O} :
    v ∈ T.translatesIn n τ I B ↔ ∀ g ∈ levi W τ, ∀ β ∈ B, (T.letterRep n g *ᵥ v) β ∈ I :=
  Iff.rfl

/-- Let `v` be a coefficient vector whose translates `T.letterRep n g *ᵥ v`, for `g` in the Levi
subgroup of the labelling `τ`, have their coefficients at the exponents in `B` in the maximal ideal
of `O`. Then the translates of the reduction of `v`, for the Frobenius cycle pushed to the residue
field, have their coefficients at `B` in the zero ideal. -/
lemma residue_mem_translatesIn [IsLocalRing O] {τ : Fin k → ℕ} {B : Set (Exponents N k n)}
    {v : Exponents N k n → O} (hv : v ∈ T.translatesIn n τ (maximalIdeal O) B) :
    (fun β : Exponents N k n ↦ residue O (v β)) ∈
      (T.map (residue O)).translatesIn n τ (⊥ : Ideal (ResidueField O)) B := by
  rw [mem_translatesIn_iff] at hv ⊢
  intro g hg β hβ
  have h_residue : ((T.map (residue O)).letterRep n g *ᵥ fun α ↦ residue O (v α)) β =
      residue O ((T.letterRep n g *ᵥ v) β) := by simp [letterRep_map, mulVec, dotProduct]
  simpa only [h_residue, Submodule.mem_bot, residue_eq_zero_iff] using hv g hg β hβ

/-! ### Stability of the two lattices of forms -/

/-- Over an `O`-algebra `K`, the translate by `g ∈ GL_k(W)` of `c z ^ β`, with `c ∈ O`, has the
coefficient `ρ(g)_{αβ} c` at `z ^ α`, where `ρ = T.letterRep n`. -/
lemma polyAction_map_monomial {K : Type} [CommRing K] [Algebra O K] (g : GL (Fin k) W)
    (β : Exponents N k n) (c : O) :
    (T.map (algebraMap O K)).polyAction g (monomial (exponentOf β) (algebraMap O K c)) =
      ∑ α : Exponents N k n,
        monomial (exponentOf α) (algebraMap O K (T.letterRep n g α β * c)) := by
  have h_single : monomial (exponentOf β) (algebraMap O K c) =
      polyOfCoeffs (Pi.single β (algebraMap O K c)) := by
    simp [polyOfCoeffs, Pi.single_apply, apply_ite]
  rw [h_single, polyAction_polyOfCoeffs, letterRep_map]
  simp [polyOfCoeffs, Algebra.smul_def, mul_comm]

/-- The lattice `H`, the `O`-span of the monomials of degree `n` in each letter in the polynomials
over the `O`-algebra `K`, is stable under `GL_k(W)`. An element `g` acts by linear substitution,
through the image of `g` in even letters and of its inverse transpose in odd letters. -/
theorem polyAction_mem_monomialLattice {K : Type} [CommRing K] [Algebra O K] (g : GL (Fin k) W)
    {h : MvPolynomial (Fin k × ZMod N) K} (h_mem : h ∈ monomialLattice N k n O K) :
    (T.map (algebraMap O K)).polyAction g h ∈ monomialLattice N k n O K := by
  let act : MvPolynomial (Fin k × ZMod N) K →ₗ[O] MvPolynomial (Fin k × ZMod N) K :=
    ((T.map (algebraMap O K)).polyAction g).toLinearMap.restrictScalars O
  suffices h_le : monomialLattice N k n O K ≤ (monomialLattice N k n O K).comap act from
    h_le h_mem
  refine Submodule.span_le.2 (Set.range_subset_iff.2 fun β ↦ ?_)
  have h_act : act (monomial (exponentOf β) 1) =
      ∑ α : Exponents N k n, T.letterRep n g α β • monomial (exponentOf α) (1 : K) := by
    simpa [act, Algebra.smul_def, C_mul_monomial] using T.polyAction_map_monomial (K := K) g β 1
  rw [SetLike.mem_coe, Submodule.mem_comap, h_act]
  exact sum_mem fun α _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

/-- Let `O` be a domain of characteristic `0`. The lattice `H°`, the `O`-span of the
`(n! ^ N / β!) z ^ β` in the polynomials over the `O`-algebra `K`, is stable under `GL_k(W)`. -/
theorem polyAction_mem_dividedPowerLattice [IsDomain O] [CharZero O] {K : Type} [CommRing K]
    [Algebra O K] (g : GL (Fin k) W) {h : MvPolynomial (Fin k × ZMod N) K}
    (h_mem : h ∈ dividedPowerLattice N k n O K) :
    (T.map (algebraMap O K)).polyAction g h ∈ dividedPowerLattice N k n O K := by
  -- In the basis of divided powers `g` acts by the transpose of the matrix `ρ'` built from the
  -- transposes of the matrices of the letters, which has entries in `O`.
  let act : MvPolynomial (Fin k × ZMod N) K →ₗ[O] MvPolynomial (Fin k × ZMod N) K :=
    ((T.map (algebraMap O K)).polyAction g).toLinearMap.restrictScalars O
  let ρ' : Matrix (Exponents N k n) (Exponents N k n) O :=
    kroneckerPi fun s : ZMod N ↦ symPowMatrix n (T.letterMatrix s g)ᵀ
  have h_entry (α β : Exponents N k n) :
      T.letterRep n g α β * dividedPowerCoeff β = dividedPowerCoeff α * ρ' β α := by
    simp only [letterRep_apply, ρ', kroneckerPi, of_apply, dividedPowerCoeff_eq_prod_multinomial,
      Nat.cast_prod, ← prod_mul_distrib, symPowMatrix_mul_multinomial]
  suffices h_le : dividedPowerLattice N k n O K ≤ (dividedPowerLattice N k n O K).comap act from
    h_le h_mem
  refine Submodule.span_le.2 (Set.range_subset_iff.2 fun β ↦ ?_)
  have h_act : act (monomial (exponentOf β) (dividedPowerCoeff β)) =
      ∑ α : Exponents N k n, ρ' β α • monomial (exponentOf α) (dividedPowerCoeff α : K) := by
    have h_expand : act (monomial (exponentOf β) (algebraMap O K (dividedPowerCoeff β))) =
        ∑ α : Exponents N k n,
          monomial (exponentOf α) (algebraMap O K (dividedPowerCoeff α * ρ' β α)) := by
      simp only [← h_entry]
      exact T.polyAction_map_monomial g β (dividedPowerCoeff β)
    simpa [Algebra.smul_def, C_mul_monomial, mul_comm] using h_expand
  rw [SetLike.mem_coe, Submodule.mem_comap, h_act]
  exact sum_mem fun α _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

/-! ### One edge -/

/-- The matrix that takes coefficients in the monomials `z ^ β` to coefficients in the normalized
monomials `w ^ (-depth β) z ^ β`, which form a basis of the halfway lattice of the edge. It is
diagonal with entries `w ^ depth β`, where `depth β` is the degree of `z ^ β` in the deep
variables. The variable `b` of the letter `s`, with `b` counted from `0`, is deep if `s` is even
and `r ≤ b`, or `s` is odd and `b < r`. -/
def depthScaling (k n r : ℕ) : Matrix (Exponents N k n) (Exponents N k n) O :=
  diagonal fun β : Exponents N k n ↦ T.sqrtPrime ^ T.depth k n r β

/-- The normalized coefficient at `β`, namely the `β` entry of `T.depthScaling k n r *ᵥ h`, is
`T.sqrtPrime ^ T.depth k n r β` times the coefficient `h β`. -/
lemma depthScaling_mulVec_apply (r : ℕ) (h : Exponents N k n → O) (β : Exponents N k n) :
    (T.depthScaling k n r *ᵥ h) β = T.sqrtPrime ^ T.depth k n r β * h β := mulVec_diagonal _ h β

/-- The matrix `T.depthScaling k n r` scales the deep variables of each letter by `T.sqrtPrime`.
These are the variables where `T.deepIndicator r` is `1`. It is the Kronecker product over the
letters `s` of the `n`-th symmetric powers of the diagonal matrices with entry `T.sqrtPrime` at the
deep variables and `1` at the others. -/
lemma depthScaling_eq_kroneckerPi (r : ℕ) :
    T.depthScaling k n r = kroneckerPi fun s : ZMod N ↦
      symPowMatrix n (diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s)) :=
  T.diagonal_pow_depth T.sqrtPrime

/-- The stabilizer of the edge preserves its halfway lattice, spanned by the monomials
`w ^ (-depth β) z ^ β`. The diagonal matrix `Δ = T.depthScaling k n r` has entries `w ^ depth β`. If
`u` lies in the parahoric subgroup for the blocks of sizes `r` and `k - r`, which stabilizes the
edge, then `Δ ρ(u) = A Δ` for a matrix `A` over `O`. -/
lemma exists_depthScaling_mul_letterRep_eq {r : ℕ} {u : GL (Fin k) W}
    (hu : u ∈ parahoric W (twoBlock k r)) :
    ∃ A : Matrix (Exponents N k n) (Exponents N k n) O,
      T.depthScaling k n r * T.letterRep n u = A * T.depthScaling k n r := by
  -- The entries in a shallow row and a deep column are divisible by `p = w ^ 2`.
  have h_dvd (s : ZMod N) (i j : Fin k) : T.sqrtPrime ^ T.deepIndicator r (j, s) ∣
      T.sqrtPrime ^ T.deepIndicator r (i, s) * T.letterMatrix s u i j := by
    obtain hij | hij := le_or_gt (T.deepIndicator r (j, s)) (T.deepIndicator r (i, s))
    · exact (pow_dvd_pow T.sqrtPrime hij).mul_right _
    · -- The deep block is the second one for `s` even and the first one for `s` odd.
      have h_even (hs : T.isEven s = true) : twoBlock k r i < twoBlock k r j := by
        grind [deepIndicator, twoBlock]
      have h_odd (hs : T.isEven s = false) : twoBlock k r j < twoBlock k r i := by
        grind [deepIndicator, twoBlock]
      have hp : T.sqrtPrime ^ 2 ∣ T.letterMatrix s u i j := by
        rw [T.sqrtPrime_sq]
        exact T.p_dvd_letterMatrix_of_mem_parahoric s hu i j h_even h_odd
      exact ((pow_dvd_pow T.sqrtPrime (by grind [deepIndicator])).trans hp).mul_left _
  -- The quotients form the integral matrix `A s` of the letter `s`.
  choose A hA using fun s i j ↦ exists_eq_mul_left_of_dvd (h_dvd s i j)
  have h_letter (s : ZMod N) :
      (diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s)) * T.letterMatrix s u =
        of (A s) * diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s) :=
    Matrix.ext fun i j ↦ by rw [diagonal_mul, mul_diagonal, hA, of_apply]
  refine ⟨kroneckerPi fun s : ZMod N ↦ symPowMatrix n (of (A s)), ?_⟩
  simp only [depthScaling_eq_kroneckerPi, letterRep_apply, ← kroneckerPi_mul, ← map_mul, h_letter]

omit [NeZero N] in
/-- If `g` lies in the Levi subgroup of the labelling `τ`, then the matrix of `g` on the letter `s`,
the image of `g` or of its inverse transpose, vanishes at `(i, j)` when `τ i ≠ τ j`. -/
lemma letterMatrix_eq_zero_of_mem_levi {τ : Fin k → ℕ} {g : GL (Fin k) W} (hg : g ∈ levi W τ)
    (s : ZMod N) {i j : Fin k} (hij : τ i ≠ τ j) : T.letterMatrix s g i j = 0 := by
  have h_inv : g⁻¹ j i = 0 := inv_mem hg j i hij.symm
  rw [letterMatrix_apply, Matrix.map_apply]
  split_ifs <;> simp only [transpose_apply, hg i j hij, h_inv, map_zero]

/-- The block diagonal subgroup preserves depth. Here `T` is a Frobenius cycle, with letters
`s ∈ ℤ/N`, alternately even and odd, and `w = T.sqrtPrime` a square root of its prime. The matrix
`T.letterRep n g` acts on the coefficient vectors of forms of degree `n` in each letter, in `k`
variables, by the image of `g` in even letters and of its inverse transpose in odd letters. Let
`g ∈ GL_k(W)` be block diagonal with blocks of sizes `r` and `k - r` (`levi W (twoBlock k r)`).
Then this matrix commutes with the diagonal matrix `T.depthScaling k n r`, whose entry at the
exponent `β` is `w ^ depth β`, where `depth β` is the degree in the variables of index `b ≥ r` in
even letters and `b < r` in odd letters. -/
lemma commute_depthScaling_letterRep {r : ℕ} {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r)) :
    Commute (T.depthScaling k n r) (T.letterRep n g) := by
  have h_letter (s : ZMod N) :
      (diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s)) * T.letterMatrix s g =
        T.letterMatrix s g * diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s) := by
    ext i j
    rw [diagonal_mul, mul_diagonal, mul_comm]
    by_cases hij : twoBlock k r i = twoBlock k r j
    · have h_depth : T.deepIndicator r (i, s) = T.deepIndicator r (j, s) := by
        grind [deepIndicator, twoBlock]
      rw [h_depth]
    · simp [T.letterMatrix_eq_zero_of_mem_levi hg s hij]
  simp only [commute_iff_eq, depthScaling_eq_kroneckerPi, letterRep_apply, ← kroneckerPi_mul,
    ← map_mul, h_letter]

/-- The forms that lie in the halfway lattices of all edges from the origin, in the normalized
coefficients `v` of one edge. The form is `w ^ (-m) h` for an integral form `h`; every edge from
the origin has an adapted basis in which it becomes a translate by some `g ∈ GL_k(W)`, and the
normalized coefficients of all these translates are integral. -/
def allEdgesForms (k n r : ℕ) : Submodule O (Exponents N k n → O) where
  carrier := {v : Exponents N k n → O | ∃ (m : ℕ) (h : Exponents N k n → O),
    T.sqrtPrime ^ m • v = T.depthScaling k n r *ᵥ h ∧
    ∀ (g : GL (Fin k) W) (β : Exponents N k n),
      T.sqrtPrime ^ m ∣ (T.depthScaling k n r *ᵥ T.letterRep n g *ᵥ h) β}
  add_mem' := by
    rintro v v' ⟨m, h, hv, h_dvd⟩ ⟨m', h', hv', h_dvd'⟩
    refine ⟨m + m', T.sqrtPrime ^ m' • h + T.sqrtPrime ^ m • h', ?_, fun g β ↦ ?_⟩
    · simp only [mulVec_add, mulVec_smul, ← hv, ← hv', pow_add]
      module
    · simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_add]
      exact dvd_add (by simpa [mul_comm] using mul_dvd_mul_left (T.sqrtPrime ^ m') (h_dvd g β))
        (mul_dvd_mul_left _ (h_dvd' g β))
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  smul_mem' := by
    rintro c v ⟨m, h, hv, h_dvd⟩
    refine ⟨m, c • h, ?_, fun g β ↦ ?_⟩
    · rw [mulVec_smul, ← hv, smul_comm]
    · simpa only [mulVec_smul, Pi.smul_apply, smul_eq_mul] using (h_dvd g β).mul_left c

/-- Integral forms lie in the halfway lattices of all edges from the origin: the normalized
coefficients of a form with coefficients `h` in `O` belong to `allEdgesForms`. -/
lemma depthScaling_mulVec_mem_allEdgesForms (r : ℕ) (h : Exponents N k n → O) :
    T.depthScaling k n r *ᵥ h ∈ T.allEdgesForms k n r :=
  ⟨0, h, by simp, by simp⟩

/-! ### Duality -/

/-- The number `c₀ = k² log_p q`, where `q = p ^ (T.frobExp * N)` is the size of the residue field
of `W`. Here `T.frobExp` is the exponent of the power `P = p ^ T.frobExp` that links consecutive
letters: the ring map of the letter `s + 1` is the `P`-th power of that of `s` modulo `p`. A
multinomial coefficient of degree less than `q` with at most `k²` parts has `p`-adic valuation at
most `c₀`. -/
def multinomialExponent (k : ℕ) : ℕ := k ^ 2 * (T.frobExp * N)

/-- The weights `b` define a pairing `⟨h, h'⟩ = ∑_β h'_β b_β h_β` on coefficient vectors for which
the matrices `ρ(g) = T.letterRep n g` and `ρ(gᵀ)` are adjoint, and the vector `b'` inverts `b` up to
the factor `p ^ (N c₀)`, where `c₀ = T.multinomialExponent k`. It is used as the pairing, in
normalized coefficients, of the halfway lattices of an edge and of the edge of dual lattices. -/
structure IsEdgePairing (b b' : Exponents N k n → O) : Prop where
  /-- The adjoint of `ρ(g)` is `ρ(gᵀ)`: entry by entry, `diag(b) ρ(gᵀ) = ρ(g)ᵀ diag(b)`. -/
  adjoint : ∀ (g : GL (Fin k) W) (α β : Exponents N k n),
    b β * T.letterRep n (transposeGL g) β α = b α * T.letterRep n g α β
  /-- The pairing is perfect up to `p ^ (N c₀)`. -/
  mul_eq_pow : ∀ β : Exponents N k n, b β * b' β = (T.p : O) ^ (N * T.multinomialExponent k)

/-- Let `⟨h, h'⟩ = ∑_β h'_β b_β h_β`, where the weights `b` satisfy `diag(b) ρ(gᵀ) = ρ(g)ᵀ diag(b)`
for `ρ = T.letterRep n`. Then translation by `g` is adjoint to translation by the transpose of `g`:
`⟨ρ(g) h, h'⟩ = ⟨h, ρ(gᵀ) h'⟩`. -/
lemma IsEdgePairing.dotProduct_letterRep_mulVec {T : FrobeniusCycle N W O}
    {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b') (g : GL (Fin k) W)
    (h h' : Exponents N k n → O) :
    h' ⬝ᵥ (b * T.letterRep n g *ᵥ h) = (T.letterRep n (transposeGL g) *ᵥ h') ⬝ᵥ (b * h) := by
  have h_diag (v : Exponents N k n → O) : b * v = diagonal b *ᵥ v :=
    funext fun β ↦ (mulVec_diagonal b v β).symm
  have h_adj : diagonal b * T.letterRep n g = (T.letterRep n (transposeGL g))ᵀ * diagonal b :=
    Matrix.ext fun α β ↦ by rw [diagonal_mul, mul_diagonal, transpose_apply, ← hb.adjoint, mul_comm]
  rw [h_diag, h_diag, mulVec_mulVec, h_adj, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The pairing `⟨h, h'⟩ = ∑_β h'_β b_β h_β` is perfect up to `p ^ (N c₀)`, where
`c₀ = T.multinomialExponent k` and `b_β b'_β = p ^ (N c₀)` for all `β`: every linear form
`h' ↦ h' ⬝ᵥ η`, times `p ^ (N c₀)`, is the pairing with the vector `h = b' * η`. -/
lemma IsEdgePairing.pairing_mul_eq_pow_mul_dotProduct {T : FrobeniusCycle N W O}
    {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b') (η h' : Exponents N k n → O) :
    h' ⬝ᵥ (b * (b' * η)) = (T.p : O) ^ (N * T.multinomialExponent k) * h' ⬝ᵥ η := by
  have h_mul : b * (b' * η) = (T.p : O) ^ (N * T.multinomialExponent k) • η :=
    funext fun β ↦ by simp [← mul_assoc, hb.mul_eq_pow]
  simp [h_mul]

/-- For a Frobenius cycle `T` over a valuation domain `O` of characteristic zero, a pairing of an
edge with the edge of dual lattices exists if `p = T.p` is not a unit in `O` and the degree `n` in
each letter is less than `q = T.q`, the number of elements of the residue field of `W`. -/
lemma exists_isEdgePairing [IsDomain O] [ValuationRing O] [CharZero O] (hp : ¬IsUnit (T.p : O))
    (hn : n < T.q) : ∃ b b' : Exponents N k n → O, T.IsEdgePairing b b' := by
  -- In one letter, `b₀ γ` is `p ^ (k log_p q)` divided by a multinomial coefficient, and with these
  -- weights the substitutions by a matrix and by its transpose are adjoint.
  obtain ⟨b₀, hb₀_mul, hb₀_adj⟩ :=
    Average.exists_isAdjointWeight (Fin k) T.prime hp (T.frobExp * N)
  -- The factor `u` raises the exponent `k log_p q` to `c₀ = k² log_p q`.
  let u : O := (T.p : O) ^ ((k - 1) * k * (T.frobExp * N))
  refine ⟨fun β ↦ ∏ s, u * b₀ (β s).val, fun β ↦ ∏ s, ((β s).val.multinomial : O),
    fun g α β ↦ ?_, fun β ↦ ?_⟩
  · have h_transpose (s : ZMod N) : T.letterMatrix s (transposeGL g) = (T.letterMatrix s g)ᵀ := by
      -- The simp lemma `coe_units_inv` would hide that the inverse is one in `GL`.
      by_cases h_even : T.isEven s <;>
        simp [letterMatrix_apply, h_even, transposeGL, transpose_map, -coe_units_inv]
    simp only [letterRep_apply, kroneckerPi, of_apply, ← prod_mul_distrib, h_transpose]
    refine prod_congr rfl fun s _ ↦ ?_
    have h_adj : b₀ (β s).val * symPowMatrix n (T.letterMatrix s g)ᵀ (β s) (α s) =
        b₀ (α s).val * symPowMatrix n (T.letterMatrix s g) (α s) (β s) := by
      simpa [symPowMatrix, mul_comm] using
        (hb₀_adj (T.letterMatrix s g) (α s).val (β s).val).symm
    rw [mul_assoc, h_adj, mul_assoc]
  · have h_exponent : (k - 1) * k * (T.frobExp * N) + k * (T.frobExp * N) =
        T.multinomialExponent k := by
      rw [multinomialExponent, ← add_mul, Nat.sub_one_mul, Nat.sub_add_cancel k.le_mul_self, sq]
    have h_letter (s : ZMod N) :
        u * b₀ (β s).val * (β s).val.multinomial = (T.p : O) ^ T.multinomialExponent k := by
      rw [mul_assoc, mul_comm (b₀ _), ← hb₀_mul _ (by rwa [Monomials.degree_eq, pow_mul]),
        Fintype.card_fin, ← pow_add, h_exponent]
    simp only [← prod_mul_distrib, h_letter, prod_const, card_univ, ZMod.card, ← pow_mul,
      mul_comm N]

/-! ### Functions on edges -/

section Global

variable {X E : Type*} [Fintype X] [DecidableEq X]

/-- The map from the integral functions on the set `X` of origins to the functions on the set `E`
of edges. The edge `e` has the origin `src e`, and `g e` passes to a basis adapted to `e`. The
value at `e` is the vector of normalized coefficients of the translate by `g e` of the value at
`src e`. -/
def edgeRestriction (n r : ℕ) (src : E → X) (g : E → GL (Fin k) W) :
    Matrix (E × Exponents N k n) (X × Exponents N k n) O :=
  of fun (x : E × Exponents N k n) (y : X × Exponents N k n) ↦
    if src x.1 = y.1 then (T.depthScaling k n r * T.letterRep n (g x.1)) x.2 y.2 else 0

/-- The functions `ψ` on edges, with values in the halfway lattices, that depend only on the origin:
some `sqrtPrime ^ m • ψ` is the image under `edgeRestriction` of an integral function `φ` on
origins. -/
def originFunctions (n r : ℕ) (src : E → X) (g : E → GL (Fin k) W) :
    Submodule O (E × Exponents N k n → O) where
  carrier := {ψ : E × Exponents N k n → O | ∃ (m : ℕ) (φ : X × Exponents N k n → O),
    T.sqrtPrime ^ m • ψ = T.edgeRestriction n r src g *ᵥ φ}
  add_mem' := by
    rintro ψ ψ' ⟨m, φ, hψ⟩ ⟨m', φ', hψ'⟩
    refine ⟨m + m', T.sqrtPrime ^ m' • φ + T.sqrtPrime ^ m • φ', ?_⟩
    rw [mulVec_add, mulVec_smul, mulVec_smul, ← hψ, ← hψ', pow_add]
    module
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro c ψ ⟨m, φ, hψ⟩
    exact ⟨m, c • φ, by rw [mulVec_smul, ← hψ, smul_comm]⟩

/-- The value at `(e, β)` of `T.edgeRestriction n r src g *ᵥ φ` is the `β` entry of `Δ ρ(g e)`
applied to `α ↦ φ (src e, α)`, where `Δ = T.depthScaling k n r` and `ρ = T.letterRep n`. So it is
the translate by `g e` of the value of `φ` at the origin `src e` of the edge `e`, with coefficients
rescaled by powers of `T.sqrtPrime`. -/
lemma edgeRestriction_mulVec_apply {r : ℕ} {src : E → X} {g : E → GL (Fin k) W}
    (φ : X × Exponents N k n → O) (e : E) (β : Exponents N k n) :
    (T.edgeRestriction n r src g *ᵥ φ) (e, β) =
      (T.depthScaling k n r *ᵥ T.letterRep n (g e) *ᵥ
        fun α : Exponents N k n ↦ φ (src e, α)) β := by
  rw [mulVec_mulVec]
  simp [edgeRestriction, mulVec, dotProduct, sum_prod_type]

omit [Fintype X] in
/-- The transpose of `edgeRestriction`: its value on `ψ` at the origin `x` is the sum over the edges
`e` from `x` of `(Δ ρ(g e))ᵀ ψ(e)`, where `Δ = T.depthScaling k n r` and `ρ = T.letterRep n`. -/
lemma transpose_edgeRestriction_mulVec [Fintype E] {r : ℕ} {src : E → X} {g : E → GL (Fin k) W}
    (ψ : E × Exponents N k n → O) (x : X) (α : Exponents N k n) :
    ((T.edgeRestriction n r src g)ᵀ *ᵥ ψ) (x, α) = ∑ e : E with src e = x,
      ((T.depthScaling k n r * T.letterRep n (g e))ᵀ *ᵥ
        fun β : Exponents N k n ↦ ψ (e, β)) α := by
  simp [edgeRestriction, mulVec, dotProduct, Fintype.sum_prod_type, sum_filter, -transpose_mul]

/-- From edges to all bases. Let the edge `e : E` have the origin `src e : X` and a change of basis
`g e ∈ GL_k(W)`. With `ρ = T.letterRep n` and the diagonal matrix `Δ = T.depthScaling k n r`, which
multiplies the coefficient at `β` by `T.sqrtPrime ^ depth β`, the restriction
`T.edgeRestriction n r src g` sends `φ` to the function with value `Δ ρ(g e) φ(src e)` at `e`.
Suppose that every edge from every origin occurs: each pair of a point of `X` and a left coset of
the parahoric subgroup for the blocks of sizes `r` and `k - r` (`ParahoricCosets`) is
`(src e, (g e)⁻¹)` for some `e`. If `z` divides every coefficient of the restriction of `φ`, then it
divides those of `Δ ρ(γ) φ(y)` for all `y ∈ X` and `γ ∈ GL_k(W)`. -/
lemma dvd_depthScaling_mulVec_of_dvd_edgeRestriction {r : ℕ} {src : E → X} {g : E → GL (Fin k) W}
    (h_surj : Surjective fun e : E ↦ ((src e, ↑(g e)⁻¹) : X × ParahoricCosets W k r))
    {z : O} {φ : X × Exponents N k n → O}
    (hz : ∀ x : E × Exponents N k n, z ∣ (T.edgeRestriction n r src g *ᵥ φ) x) (y : X)
    (γ : GL (Fin k) W) (β : Exponents N k n) :
    z ∣ (T.depthScaling k n r *ᵥ T.letterRep n γ *ᵥ fun α : Exponents N k n ↦ φ (y, α)) β := by
  -- Write `γ = u * g e` with `u` parahoric and `src e = y`.
  obtain ⟨e, rfl, he⟩ : ∃ e : E, src e = y ∧ g e * γ⁻¹ ∈ parahoric W (twoBlock k r) := by
    simpa [QuotientGroup.eq] using h_surj (y, ↑γ⁻¹)
  have hu : γ * (g e)⁻¹ ∈ parahoric W (twoBlock k r) := by simpa using inv_mem he
  obtain ⟨A, hA : T.depthScaling k n r * T.letterRep n (γ * (g e)⁻¹) = A * T.depthScaling k n r⟩ :=
    T.exists_depthScaling_mul_letterRep_eq hu
  have h_translate : T.depthScaling k n r * T.letterRep n γ =
      A * (T.depthScaling k n r * T.letterRep n (g e)) := by
    rw [← mul_assoc, ← hA, mul_assoc, ← map_mul, inv_mul_cancel_right]
  rw [mulVec_mulVec, h_translate, ← mulVec_mulVec, ← mulVec_mulVec]
  refine dvd_sum fun α _ ↦ Dvd.dvd.mul_left ?_ _
  simpa only [edgeRestriction_mulVec_apply] using hz (e, α)

/-- Let `ψ` be in `T.originFunctions n r src g`: for some `m`, the multiple `w ^ m • ψ` is the
restriction to edges (`edgeRestriction`) of a function `φ` on the origins with values in `O`, where
`w = T.sqrtPrime` and the value of the restriction at the edge `e` is `Δ ρ(g e) φ(src e)`, for
`Δ = T.depthScaling k n r` and `ρ = T.letterRep n`. Suppose that every edge from every origin
occurs: each pair of a point of `X` and a left coset of the parahoric subgroup is
`(src e, (g e)⁻¹)` for some `e`. Then each value `v = ψ(e)` lies in the halfway lattices of all
edges (`allEdgesForms`): for some `m` and some `h` with `w ^ m • v = Δ h`, the power `w ^ m`
divides all coefficients of `Δ ρ(γ) h` for every `γ ∈ GL_k(W)`. -/
lemma apply_mem_allEdgesForms {r : ℕ} {src : E → X} {g : E → GL (Fin k) W}
    (h_surj : Surjective fun e : E ↦ ((src e, ↑(g e)⁻¹) : X × ParahoricCosets W k r))
    {ψ : E × Exponents N k n → O} (hψ : ψ ∈ T.originFunctions n r src g) (e : E) :
    (fun β : Exponents N k n ↦ ψ (e, β)) ∈ T.allEdgesForms k n r := by
  obtain ⟨m, φ, hφ : T.sqrtPrime ^ m • ψ = T.edgeRestriction n r src g *ᵥ φ⟩ := hψ
  refine ⟨m, T.letterRep n (g e) *ᵥ fun α : Exponents N k n ↦ φ (src e, α), ?_, fun γ β ↦ ?_⟩
  · exact funext fun β ↦ by simp [← edgeRestriction_mulVec_apply, ← hφ]
  · rw [mulVec_mulVec _ (T.letterRep n γ), ← map_mul]
    exact T.dvd_depthScaling_mulVec_of_dvd_edgeRestriction h_surj (fun x ↦ by simp [← hφ])
      (src e) (γ * g e) β

/-- If `z` divides `c` times every entry of one column of an invertible matrix, it divides `c`. -/
lemma dvd_of_forall_dvd_mul_inv_apply {I : Type*} [Fintype I] [DecidableEq I] (P : GL I O)
    {z c : O} {i : I} (h_col : ∀ j : I, z ∣ c * P⁻¹.val j i) : z ∣ c := by
  have h_diag : ∑ j : I, P.val i j * (c * P⁻¹.val j i) = c := by
    simp only [mul_left_comm, ← mul_sum, ← Matrix.mul_apply, P.mul_inv, one_apply_eq, mul_one]
  rw [← h_diag]
  exact dvd_sum fun j _ ↦ (h_col j).mul_left _

/-- The integral functions on origins have small colength in the functions on edges that depend only
on the origin. Here `O` is a valuation domain and `T` is a Frobenius cycle from the local ring `W`
to `O`. `w = T.sqrtPrime` squares to the prime `T.p`. The edge `e : E` has the origin `src e : X`
and a change of basis `g e ∈ GL_k(W)`. The matrix `T.edgeRestriction n r src g` sends a function `φ`
on origins to `e ↦ Δ ρ(g e) φ(src e)`. Here `ρ = T.letterRep n`, and `Δ` multiplies the coefficient
at `β` by `w ^ depth β`. `T.originFunctions n r src g` consists of the `ψ` with some `w ^ m • ψ` in
the image of this matrix.

Suppose that every edge from every origin occurs. That is, each pair of a point of `X` and a left
coset in `ParahoricCosets W k r` is `(src e, (g e)⁻¹)` for some `e`. Suppose also that all depths
are at most `x`. Then there are matrices `Q` and `R` with `R * Q = 1`, such that `Q *ᵥ φ` lies in
`originFunctions` for every `φ`. Moreover `Q * d = edgeRestriction` for a `d` whose determinant
divides `w ^ l`. Here `l` is `|X|` times the sum over `1 ≤ δ ≤ x` of the dimensions of the spaces
`deepForms`. These are the forms over the residue field of `O` all of whose translates have only
monomials of depth at least `δ`. -/
lemma exists_originFunctions_factorization_det_dvd [Fintype E] [DecidableEq E] {r : ℕ} {src : E → X}
    {g : E → GL (Fin k) W} [IsDomain O] [ValuationRing O]
    (h_surj : Surjective fun e : E ↦ ((src e, ↑(g e)⁻¹) : X × ParahoricCosets W k r))
    {x : ℕ} (h_depth : ∀ β : Exponents N k n, T.depth k n r β ≤ x) :
    ∃ (Q : Matrix (E × Exponents N k n) (X × Exponents N k n) O)
      (R : Matrix (X × Exponents N k n) (E × Exponents N k n) O)
      (d : Matrix (X × Exponents N k n) (X × Exponents N k n) O),
      (∀ φ : X × Exponents N k n → O, Q *ᵥ φ ∈ T.originFunctions n r src g) ∧
      R * Q = 1 ∧
      Q * d = T.edgeRestriction n r src g ∧
      d.det ∣ T.sqrtPrime ^ (Fintype.card X * ∑ δ ∈ range x,
        finrank (ResidueField O) ((T.map (residue O)).deepForms k n r (δ + 1))) := by
  classical
  -- Elementary divisors: `J * P⁻¹ = Q * diagonal t` for the inclusion `J`.
  set J : Matrix (E × Exponents N k n) (X × Exponents N k n) O := T.edgeRestriction n r src g
  let ι : X × Exponents N k n ↪ E × Exponents N k n :=
    .ofSurjective _ ((Prod.fst_surjective.comp h_surj).prodMap surjective_id)
  obtain ⟨Q, R, P, t, hRQ : R * Q = 1, hJP : J * P⁻¹.val = Q * diagonal t⟩ :=
    exists_mul_inv_eq_mul_diagonal ι J
  -- So `t i` divides the normalized coefficients of all translates of column `i` of `P⁻¹`.
  have ht_dvd (i : X × Exponents N k n) (y : X) (γ : GL (Fin k) W) (β : Exponents N k n) :
      t i ∣ T.sqrtPrime ^ T.depth k n r β * (T.letterRep n γ *ᵥ fun α ↦ P⁻¹.val (y, α) i) β := by
    rw [← depthScaling_mulVec_apply]
    refine T.dvd_depthScaling_mulVec_of_dvd_edgeRestriction (φ := P⁻¹.val.col i) h_surj
      (fun e ↦ ?_) y γ β
    change t i ∣ (J * P⁻¹.val) e i
    simp [hJP, -coe_units_inv]
  -- With `γ = 1`, it divides `w ^ x` times a column of an invertible matrix, hence `w ^ x`.
  have ht_pow (i : X × Exponents N k n) : t i ∣ T.sqrtPrime ^ x := by
    refine dvd_of_forall_dvd_mul_inv_apply P (i := i) fun ⟨y, β⟩ ↦ ?_
    have h_mul : t i ∣ T.sqrtPrime ^ T.depth k n r β * P⁻¹.val (y, β) i := by
      simpa using ht_dvd i y 1 β
    exact h_mul.trans (mul_dvd_mul_right (pow_dvd_pow T.sqrtPrime (h_depth β)) _)
  refine ⟨Q, R, diagonal t * P.val, fun φ ↦ ?_, hRQ, ?_, ?_⟩
  · -- With `w ^ x = t i * t' i`, the vector `w ^ x • Q φ` is a value of `J`.
    choose t' ht' using (ht_pow : ∀ i : X × Exponents N k n, ∃ c : O, T.sqrtPrime ^ x = t i * c)
    have h_scalar : diagonal t *ᵥ diagonal t' *ᵥ φ = T.sqrtPrime ^ x • φ :=
      funext fun i ↦ by simp [mulVec_diagonal, ← mul_assoc, ← ht']
    exact ⟨x, P⁻¹.val *ᵥ diagonal t' *ᵥ φ,
      by rw [mulVec_mulVec, hJP, ← mulVec_mulVec, h_scalar, mulVec_smul]⟩
  · rw [← Matrix.mul_assoc, ← hJP, Matrix.mul_assoc, P.inv_mul, Matrix.mul_one]
  -- If `t j` does not divide `w ^ δ`, column `j` has only depths above `δ` modulo `𝔪_O`.
  have h_deep (δ : ℕ) (j : X × Exponents N k n) (hj : ¬t j ∣ T.sqrtPrime ^ δ) (y : X) :
      (fun α ↦ P⁻¹.val (y, α) j) ∈
        T.translatesIn n 0 (maximalIdeal O) {β | T.depth k n r β < δ + 1} := by
    intro γ _ β hβ
    refine (mem_maximalIdeal _).2 fun h_unit ↦ hj ?_
    exact (h_unit.dvd_mul_right.1 (ht_dvd j y γ β)).trans
      (pow_dvd_pow T.sqrtPrime (Nat.le_of_lt_succ hβ))
  -- The columns of `P⁻¹` are independent modulo `𝔪_O`, which bounds the number of these `j`.
  have h_card (δ : ℕ) : #{i : X × Exponents N k n | ¬t i ∣ T.sqrtPrime ^ δ} ≤ Fintype.card X *
      finrank (ResidueField O) ((T.map (residue O)).deepForms k n r (δ + 1)) :=
    card_le_mul_finrank_of_dual_rows P⁻¹.val P.val (fun j _ i ↦ by rw [P.mul_inv, one_apply])
      fun j hj y ↦ T.residue_mem_translatesIn (h_deep δ j (mem_filter.1 hj).2 y)
  rw [det_mul, det_diagonal, (isUnits_det_units P).mul_right_dvd, mul_sum]
  exact (prod_dvd_pow_sum_card ht_pow).trans
    (pow_dvd_pow T.sqrtPrime (sum_le_sum fun δ _ ↦ h_card δ))

/-- Let the edge `e : E` have the origin `src e : X` and a change of basis `g e ∈ GL_k(W)`. Let
`T.edgeRestriction n r src g` be the matrix that sends a function `φ` on origins to
`e ↦ Δ ρ(g e) φ(src e)`, for `ρ = T.letterRep n` and `Δ = T.depthScaling k n r`, and let
`T.originFunctions n r src g` be the module of the `ψ` with `T.sqrtPrime ^ m • ψ` in its image for
some `m`. If `O` is a domain of characteristic zero, `Q` has a left inverse `R` and this matrix
factors as `Q * d`, then `Q R` fixes every such `ψ`. -/
lemma mulVec_mulVec_eq_self_of_mem_originFunctions [Fintype E] {r : ℕ} {src : E → X}
    {g : E → GL (Fin k) W} [IsDomain O] [CharZero O]
    {Q : Matrix (E × Exponents N k n) (X × Exponents N k n) O}
    {R : Matrix (X × Exponents N k n) (E × Exponents N k n) O}
    {d : Matrix (X × Exponents N k n) (X × Exponents N k n) O} (hRQ : R * Q = 1)
    (hQd : Q * d = T.edgeRestriction n r src g) {ψ : E × Exponents N k n → O}
    (hψ : ψ ∈ T.originFunctions n r src g) :
    Q *ᵥ R *ᵥ ψ = ψ := by
  obtain ⟨m, φ, hφ : T.sqrtPrime ^ m • ψ = T.edgeRestriction n r src g *ᵥ φ⟩ := hψ
  refine smul_right_injective _ (pow_ne_zero m T.sqrtPrime_ne_zero)
    (?_ : T.sqrtPrime ^ m • Q *ᵥ R *ᵥ ψ = T.sqrtPrime ^ m • ψ)
  -- Both sides become `Q (d φ)`, as `R Q = 1`.
  rw [← mulVec_smul, ← mulVec_smul, hφ, ← hQd, ← mulVec_mulVec, mulVec_mulVec _ R, hRQ, one_mulVec]

end Global

end Edges

/-! ### Large defect -/

variable {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O]
variable (T : FrobeniusCycle N W O) [IsDomain O] [CharZero O]
variable {a r : Fin k}

/-- A large defect forces a divisible coefficient. Let `O` be a domain of characteristic zero, `T` a
Frobenius cycle and `w = T.sqrtPrime`, so `w ^ 2 = p`. Let `a < r` be indices of variables, so `a`
is in the first and `r` in the second of the blocks `b < r`, `b ≥ r`. In a letter `s` let
`(u_s, ū_s)` be `(r, a)` if `s` is even and `(a, r)` if it is odd. The defect of `β` at the letter
`i`, which is its weight for `T.defectWeight i a r`, is `β_i(u_i) + ∑_s P ^ ((s - i) mod N)
(β_s(u_s) - β_s(ū_s)) / (q - 1)`, for `P = p ^ T.frobExp` and `q = P ^ N`.

If `w ^ m` divides `w ^ depth β * (ρ(g) F) β` for all `g` and `β`, where `ρ = T.letterRep n`, then
`w ^ (m + j)` divides it at the exponents `β` of defect at least `3 j`. -/
lemma pow_add_dvd_of_le_defect {m j : ℕ} (i : ZMod N) (ha : a < r) {F : Exponents N k n → O}
    (hF : ∀ (g : GL (Fin k) W) (β : Exponents N k n),
      T.sqrtPrime ^ m ∣ T.sqrtPrime ^ T.depth k n r β * (T.letterRep n g *ᵥ F) β)
    {β : Exponents N k n} {g : GL (Fin k) W}
    (hβ : 3 * j ≤ (exponentOf β).weight (T.defectWeight i a r)) :
    T.sqrtPrime ^ (m + j) ∣ T.sqrtPrime ^ T.depth k n r β * (T.letterRep n g *ᵥ F) β := by
  -- The depth rises by `1` along the root `(a, r)` in each letter.
  have h_depth (δ : Exponents N k n) : (exponentOf δ).weight (fun x : Fin k × ZMod N ↦
      (T.deepIndicator r x : ℝ)) = T.depth k n r δ := by simp [depth, Finsupp.weight_eq_sum]
  have h_step (s : ZMod N) :
      (T.deepIndicator r (T.rootVar a r s) : ℝ) - T.deepIndicator r (T.rootVar r a s) = 1 := by
    by_cases h_even : T.isEven s <;> simp [deepIndicator, rootVar, h_even, ha]
  have h_translates (γ : GL (Fin k) W) (_ : γ ∈ rootSL W a r) :
      T.polyAction γ (polyOfCoeffs (T.letterRep n g *ᵥ F)) ∈
        gaussFiltration (adicFiltration T.sqrtPrime)
          (fun x : Fin k × ZMod N ↦ (T.deepIndicator r x : ℝ)) m := by
    rw [polyAction_polyOfCoeffs, mulVec_mulVec, ← map_mul, polyOfCoeffs, LinearMap.sum_apply]
    refine _root_.sum_mem fun δ _ ↦ monomial_mem_gaussFiltration ?_
    change T.sqrtPrime ^ ⌈m - (exponentOf δ).weight fun x ↦ (T.deepIndicator r x : ℝ)⌉₊ ∣ _
    rw [h_depth, Nat.ceil_sub_natCast, Nat.ceil_natCast]
    exact pow_sub_dvd_of_pow_dvd_pow_mul T.sqrtPrime_ne_zero (hF (γ * g) δ)
  -- Hence the depth may be lowered by a third of the defect.
  set defect : ℝ := (exponentOf β).weight (T.defectWeight i a r) with h_defect
  have h_gain : T.sqrtPrime ^ ⌈m - (T.depth k n r β - defect / 3)⌉₊ ∣ (T.letterRep n g *ᵥ F) β := by
    simpa [h_defect, weight_sub_defectWeight_div_three, h_depth, polyOfCoeffs, coeff_sum] using
      T.mem_gaussFiltration_sub_defect_div_three i ha.ne h_step h_translates (exponentOf β)
  have h_exponent : m + j ≤ T.depth k n r β + ⌈m - (T.depth k n r β - defect / 3)⌉₊ := by
    rify
    linarith [Nat.le_ceil (m - (T.depth k n r β - defect / 3))]
  exact (pow_dvd_pow T.sqrtPrime h_exponent).trans
    (by simpa only [pow_add] using mul_dvd_mul_left _ h_gain)

/-- Let `O` be a domain of characteristic zero, `w = T.sqrtPrime` the square root of the prime of
the Frobenius cycle `T`, and `a < r` indices of variables, one in each of the blocks `b < r`,
`b ≥ r`. Let `v` lie in `T.allEdgesForms k n r`: for some `m` and some `h` with `w ^ m • v = Δ h`,
the power `w ^ m` divides all coefficients of `Δ ρ(γ) h` for every `γ ∈ GL_k(W)`. Here
`ρ = T.letterRep n` and `Δ = T.depthScaling k n r` multiplies the coefficient at `β` by
`w ^ depth β`. Let `g` be block diagonal (`levi`). If `β` has defect at least `3 j` at the letter
`i`, that is, `β_i(u_i) + ∑_s P ^ ((s - i) mod N) (β_s(u_s) - β_s(ū_s)) / (q - 1) ≥ 3 j` with
`(u_s, ū_s)` equal to `(r, a)` for even and `(a, r)` for odd `s` (`T.defectWeight i a r`;
`P = p ^ T.frobExp`, `q = P ^ N`), then `w ^ j` divides the coefficient at `β` of `ρ(g) v`. -/
lemma pow_dvd_letterRep_mulVec_of_mem_allEdgesForms (ha : a < r) {v : Exponents N k n → O}
    (hv : v ∈ T.allEdgesForms k n r) {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r)) {j : ℕ}
    {i : ZMod N} {β : Exponents N k n}
    (hβ : 3 * j ≤ (exponentOf β).weight (T.defectWeight i a r)) :
    T.sqrtPrime ^ j ∣ (T.letterRep n g *ᵥ v) β := by
  obtain ⟨m, F, hvF : T.sqrtPrime ^ m • v = T.depthScaling k n r *ᵥ F, h_dvd⟩ := hv
  have h_normalized (γ : GL (Fin k) W) (δ : Exponents N k n) :
      T.sqrtPrime ^ m ∣ T.sqrtPrime ^ T.depth k n r δ * (T.letterRep n γ *ᵥ F) δ := by
    simpa only [depthScaling_mulVec_apply] using h_dvd γ δ
  have h_translate : T.sqrtPrime ^ m * (T.letterRep n g *ᵥ v) β =
      T.sqrtPrime ^ T.depth k n r β * (T.letterRep n g *ᵥ F) β :=
    calc T.sqrtPrime ^ m * (T.letterRep n g *ᵥ v) β
      _ = (T.letterRep n g *ᵥ T.depthScaling k n r *ᵥ F) β := by simp [← hvF, mulVec_smul]
      _ = T.sqrtPrime ^ T.depth k n r β * (T.letterRep n g *ᵥ F) β := by
          rw [mulVec_mulVec, ← (T.commute_depthScaling_letterRep hg).eq, ← mulVec_mulVec,
            depthScaling_mulVec_apply]
  rw [← mul_dvd_mul_iff_left (pow_ne_zero m T.sqrtPrime_ne_zero), ← pow_add, h_translate]
  exact T.pow_add_dvd_of_le_defect i ha h_normalized hβ

/-- Let `O` be a domain of characteristic zero. The forms in the halfway lattices of all edges
(`allEdgesForms`) satisfy the conditions on an edge (`defectConditions`): their block diagonal
translates have, modulo `sqrtPrime ^ c`, no term of defect above `3 c*` along the root `(a, r)`,
where `c* = 3 k c` is `defectThreshold k c` and `a < r` are indices, one in each block. -/
lemma allEdgesForms_le_defectConditions (ha : a < r) (c : ℕ) :
    T.allEdgesForms k n r ≤ T.defectConditions n a r (span {T.sqrtPrime ^ c})
      (3 * defectThreshold k c) := by
  rintro v hv g hg β ⟨i, h_defect :
    (3 * defectThreshold k c : ℝ) < (exponentOf β).weight (T.defectWeight i a r)⟩
  have h_le : (3 * c : ℝ) ≤ defectThreshold k c := mod_cast three_mul_le_defectThreshold a.pos c
  exact mem_span_singleton.2
    (T.pow_dvd_letterRep_mulVec_of_mem_allEdgesForms ha hv hg (j := c) (by linarith))

/-- Let `O` be a domain of characteristic zero, `w = T.sqrtPrime` (so `w ^ 2 = p`) and
`ρ = T.letterRep n`. Let `(b, b')` be an edge pairing: `ρ(g)` and `ρ(gᵀ)` are adjoint for
`∑_β h'_β b_β h_β`, and `b_β b'_β` is a fixed power of `p` (`IsEdgePairing`). Let `v` lie in
`T.allEdgesForms k n r`: for some `m` and some `h` with `w ^ m • v = Δ h`, the power `w ^ m` divides
all coefficients of `Δ ρ(γ) h` for every `γ`, where `Δ = T.depthScaling k n r`. Let `a < r` be
indices of variables, one in each of the blocks `b < r`, `b ≥ r`, let `g` be block diagonal, and let
`β` have defect above `c* = 3 k c` (`defectThreshold k c`) at the letter `i`. This defect, the
weight for `T.defectWeight i a r`, is `β_i(u_i) + ∑_s P ^ ((s - i) mod N) (β_s(u_s) -
β_s(ū_s)) / (q - 1)`, with `(u_s, ū_s) = (r, a)` for even and `(a, r)` for odd `s`,
`P = p ^ T.frobExp`, `q = P ^ N`. Then `w ^ c` divides the pairing, by the weights `b`, of `v` with
the image under `ρ(g)` of the unit vector at `β`. -/
lemma IsEdgePairing.pow_dvd_pairing_letterRep {b b' : Exponents N k n → O}
    (hb : T.IsEdgePairing b b') (ha : a < r) {v : Exponents N k n → O}
    (hv : v ∈ T.allEdgesForms k n r) {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r)) {c : ℕ}
    {i : ZMod N} {β : Exponents N k n}
    (hβ : defectThreshold k c < (exponentOf β).weight (T.defectWeight i a r)) :
    T.sqrtPrime ^ c ∣ v ⬝ᵥ (b * T.letterRep n g *ᵥ Pi.single β 1) := by
  have hg' : transposeGL g ∈ levi W (twoBlock k r) := fun i j hij ↦ hg j i hij.symm
  -- The pairing is `b β` times the coefficient at `β` of the translate of `v` by the transpose.
  have h_pairing : v ⬝ᵥ (b * T.letterRep n g *ᵥ Pi.single β 1) =
      (T.letterRep n (transposeGL g) *ᵥ v) β * b β := by
    rw [hb.dotProduct_letterRep_mulVec]
    simp [dotProduct, Pi.single_apply]
  have h_le : (3 * c : ℝ) ≤ defectThreshold k c := mod_cast three_mul_le_defectThreshold a.pos c
  rw [h_pairing]
  exact (T.pow_dvd_letterRep_mulVec_of_mem_allEdgesForms ha hv hg' (h_le.trans hβ.le)).mul_right _

end FrobeniusCycle

end New

end
