import Lib.General.Algebra.SeriesBounds
import Lib.LocalGL.SphericalChainLemma
import New.Congruences.GaloisRepresentations.SelmerHypotheses

/-!
# Chains of roots for weak lifts, and Hecke-stable subspaces of forms

Let `O` be a descent pair, with spaces W and V of ranks r < n, put t = n − r, and let `f` be a
nonzero eigenform on V with Galois representation R. Its normalised representation is u = R ⊗ χ. The
case of interest is that det (1 − u(g)) = 0 for all g, the condition that defines weak lifts.

Notions from other files:
* `New.Parameters`, `New.Data`: the fixed parameters P and admissible data D over them (numerical
  scales, ranks, levels); D determines the CM field E = `D.E`.
* `New.DescentPair`: places, weights and a hermitian space W of rank r, beside the definite space
  V = `New.stdSpace` of rank n > r; `New.DescentPair.rankDiff` is t = n − r. The forms on V have
  the weight (`columnCount`, `detExp`): column numbers and a power of the determinant at each
  infinite place.
* `New.Patching.Isotypic`: spaces of forms with given Hecke eigenvalues at almost all places; such a
  space `x` has Hecke polynomials `x.heckePolyAt w` and a Galois representation `x.galRep`.
* `New.Selmer.normalisedRep`: the twist of a Galois representation by the ℓ-adic character
  χ = `New.Selmer.normalizingAvatar`, the avatar of an algebraic Hecke character made from W.
* `Ω`: a fixed algebraic closure of ℚ, so that Gal(Ω/E) is the absolute Galois group of E.
* `New.mostFrobenii`: a filter on the triples of a place, a place of `Ω` over it and a geometric
  Frobenius element there.
* `ιℓ`: the fixed isomorphism ι from `ℂ` to `ℚ̄_ℓ`.

## Main definitions and results

* `New.Selmer.exists_diagonal_mem_norm_ge`: diagonal operators, one for each vector of a basis, are
  combined into one operator with an eigenvalue at each vector at least as large in norm.
* `New.Selmer.isRoot_hecke_chain`: if det (1 − u(g)) = 0 for all g, the Hecke polynomial at a split
  place w ∤ ℓ has the chain of roots X₀, X₀q, …, X₀q^(t−1), where q is the norm of w and
  ι(X₀) = χ(Frob_w)⁻¹.
* `New.Selmer.eventually_exists_hasRootChain`: for most Frobenius elements φ, if u has integral
  characteristic polynomials with root 1 and that of u(φ) is congruent to a product of S and ∏_{j<t}
  (X − c(φ)^j), with c the inverse cyclotomic character, for a polynomial S with ‖S(1)‖ ≥ 1, the
  rescaled Hecke polynomial is ∏ (X − q^i) times a divisor of an integral polynomial with value 1 at
  1.
* `New.Selmer.orthogonal_mem_invtSubmodule_heckePolyOnForms`, `New.Selmer.le_of_isotypic_mem`: the
  orthogonal complement of a Hecke-stable subspace Z is Hecke stable, and Z lies in a subspace N
  once every nonzero form of Z in an isotypic space lies in N.
-/

/-!
## A single operator from several diagonal operators

Take operators that are diagonal in one basis, one for each basis vector. Some integral combination
has at every basis vector an eigenvalue of norm at least that of the operator chosen for it, since
finitely many hyperplanes do not cover a space over the infinite residue field of `ℚ̄_ℓ`.
-/

section DeterminantBound

open Module Matrix Finset Real NormedField Submodule MvPolynomial

/-- For a square array `l p k` of elements of `ℚ̄_ℓ` there are coefficients `d p` of norm at most
one such that, for every `k`, the combination `∑ p, l p k * d p` has norm at least `‖l k k‖`. -/
lemma New.Selmer.exists_integral_combination_norm_ge {ℓ : ℕ} [ThePrime ℓ] {m : ℕ}
    (l : Fin m → Fin m → PadicAlgCl ℓ) :
    ∃ d : Fin m → PadicAlgCl ℓ, (∀ p : Fin m, ‖d p‖ ≤ 1) ∧
      ∀ k : Fin m, ‖l k k‖ ≤ ‖∑ p : Fin m, l p k * d p‖ := by
  -- Take an integral point at which each linear form `F k` has norm at least that of each of its
  -- coefficients; the coefficient of `X k` in `F k` is `l k k`.
  let F (k : Fin m) : MvPolynomial (Fin m) (PadicAlgCl ℓ) := ∑ p : Fin m, l p k • X p
  obtain ⟨d, hd⟩ : ∃ d : Fin m → (valuation (K := PadicAlgCl ℓ)).valuationSubring,
      ∀ (k : Fin m) (s : Fin m →₀ ℕ),
        valuation ((F k).coeff s) ≤ valuation (eval (fun p ↦ (d p : PadicAlgCl ℓ)) (F k)) :=
    exists_val_coeff_le_val_eval valuation F
  refine ⟨fun p ↦ d p, fun p ↦ (d p).property, fun k ↦ ?_⟩
  have h_coeff : (F k).coeff (.single k 1) = l k k := by simp [F]
  rw [← h_coeff]
  simpa [F] using NNReal.coe_mono (hd k (.single k 1))

/-- Let `Good` be a set of operators on `Z` that contains every combination of `m` of its members
with `ℓ`-adically integral coefficients. If for each `k` the operator that is diagonal in the basis
`b` with eigenvalues `l k` lies in `Good`, then some operator in `Good`, diagonal in `b`, has
eigenvalues `μ k` with `‖μ k‖ ≥ ‖l k k‖` for every `k`. Norms are `ℓ`-adic, through the fixed
isomorphism `ιℓ` from `ℂ` to `ℚ̄_ℓ`. -/
lemma New.Selmer.exists_diagonal_mem_norm_ge {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {Z : Type}
    [AddCommGroup Z] [Module ℂ Z] {m : ℕ} (b : Basis (Fin m) ℂ Z) {Good : Set (Module.End ℂ Z)}
    (h_comb : ∀ (G : Fin m → Module.End ℂ Z) (d : Fin m → PadicAlgCl ℓ),
      (∀ p : Fin m, G p ∈ Good) → (∀ p : Fin m, ‖d p‖ ≤ 1) →
        ∑ p : Fin m, ιℓ.symm (d p) • G p ∈ Good)
    (l : Fin m → Fin m → ℂ) (h_good : ∀ k : Fin m, Matrix.toLin b b (diagonal (l k)) ∈ Good) :
    ∃ μ : Fin m → ℂ, Matrix.toLin b b (diagonal μ) ∈ Good ∧
      ∀ k : Fin m, ‖ιℓ (l k k)‖ ≤ ‖ιℓ (μ k)‖ := by
  -- Take integral `d p` for which every `∑ p, l p k * d p` is as large as `l k k`. The operator
  -- with these eigenvalues is the combination of the given ones with coefficients `d p`.
  obtain ⟨d, hd_int, hd⟩ := exists_integral_combination_norm_ge fun p k ↦ ιℓ (l p k)
  let μ (k : Fin m) : ℂ := ∑ p : Fin m, ιℓ.symm (d p) * l p k
  have h_apply (e : Fin m → ℂ) (k : Fin m) : Matrix.toLin b b (diagonal e) (b k) = e k • b k :=
    (hasEigenvector_toLin_diagonal e k b).apply_eq_smul
  have h_sum : Matrix.toLin b b (diagonal μ) =
      ∑ p : Fin m, ιℓ.symm (d p) • Matrix.toLin b b (diagonal (l p)) := by
    refine b.ext fun k ↦ ?_
    simp only [h_apply, μ, LinearMap.sum_apply, LinearMap.smul_apply, smul_smul, Finset.sum_smul]
  have hμ (k : Fin m) : ιℓ (μ k) = ∑ p : Fin m, ιℓ (l p k) * d p := by simp [μ, mul_comm]
  exact ⟨μ, by simpa only [h_sum] using h_comb _ d h_good hd_int,
    fun k ↦ by simpa only [hμ] using hd k⟩

/-- Let `Λ` be an operator on a complex space `Z` of finite dimension `N`, and `ιℓ` the fixed
isomorphism from `ℂ` to `ℚ̄_ℓ`. If `c * ιℓ μ` has norm at least `ε` for every eigenvalue `μ` of
`Λ`, then `c ^ N * ιℓ (det Λ)` has norm at least `ε ^ N`. -/
lemma New.Selmer.pow_finrank_le_nnnorm_det {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {Z : Type}
    [AddCommGroup Z] [Module ℂ Z] [Module.Finite ℂ Z] (Λ : Module.End ℂ Z) (c : PadicAlgCl ℓ)
    {ε : NNReal} (h_eig : ∀ μ : ℂ, Λ.HasEigenvalue μ → ε ≤ ‖c * ιℓ μ‖₊) :
    ε ^ finrank ℂ Z ≤ ‖c ^ finrank ℂ Z * ιℓ (LinearMap.det Λ)‖₊ := by
  -- Over `ℂ` the determinant is the product of the roots of the characteristic polynomial, with
  -- multiplicity; these roots are the eigenvalues, and there are `finrank ℂ Z` of them.
  have h_card : Multiset.card Λ.charpoly.roots = finrank ℂ Z := by
    rw [IsAlgClosed.card_roots_eq_natDegree, LinearMap.charpoly_natDegree]
  have h_det : c ^ finrank ℂ Z * ιℓ (LinearMap.det Λ) =
      (Λ.charpoly.roots.map fun μ ↦ c * ιℓ μ).prod := by
    rw [Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _), map_multiset_prod,
      Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, h_card]
  have h_norm : ‖(Λ.charpoly.roots.map fun μ ↦ c * ιℓ μ).prod‖₊ =
      (Λ.charpoly.roots.map fun μ ↦ ‖c * ιℓ μ‖₊).prod := by
    simp
  rw [h_det, h_norm, ← h_card, ← Multiset.card_map fun μ ↦ ‖c * ιℓ μ‖₊]
  refine Multiset.pow_card_le_prod (Multiset.forall_mem_map_iff.2 fun μ hμ ↦ h_eig μ ?_)
  exact (Module.End.hasEigenvalue_iff_isRoot_charpoly Λ μ).2 (Polynomial.isRoot_of_mem_roots hμ)

end DeterminantBound

namespace New.Selmer

/-!
## The Hecke polynomial as a chain times an integral factor

Congruences are coefficientwise modulo the maximal ideal of the integers of ℚ̄_ℓ (norm < 1).
-/

section HeckeString

open Matrix Polynomial Fintype GaloisRep ComplexOrder IsUltrametricDist NormedField Patching

variable {ℓ : ℕ} [ThePrime ℓ]

/-- If `R` is monic and all coefficients of `Q * R` have norm less than one, then so do all
coefficients of `Q`. -/
lemma norm_coeff_lt_one_of_mul_monic {Q R : (PadicAlgCl ℓ)[X]} (hR : R.Monic)
    (h_lt : ∀ i : ℕ, ‖(Q * R).coeff i‖ < 1) (i : ℕ) :
    ‖Q.coeff i‖ < 1 := by
  obtain ⟨j, hj⟩ := exists_eq_supNorm (Q * R)
  calc ‖Q.coeff i‖ ≤ (Q * R).supNorm := norm_coeff_le_of_mul_monic hR (le_supNorm _) i
    _ = ‖(Q * R).coeff j‖ := hj
    _ < 1 := h_lt j

lemma norm_eval_one_lt_one {Q : (PadicAlgCl ℓ)[X]} (h_lt : ∀ i : ℕ, ‖Q.coeff i‖ < 1) :
    ‖Q.eval 1‖ < 1 := by
  obtain ⟨j, -, hj⟩ := exists_norm_finsetSum_le (Finset.range (Q.natDegree + 1)) Q.coeff
  simpa [eval_eq_sum_range] using hj.trans_lt (h_lt j)

/-- Let B be monic, C integral, AB ≡ C ≡ A'B coefficientwise modulo the maximal ideal of the
integers `intQpBar ℓ` of ℚ̄_ℓ, and ‖A'(1)‖ ≥ 1. Then A divides an integral polynomial e with
e(1) = 1. -/
lemma exists_integral_multiple_eval_one {A A' B C : (PadicAlgCl ℓ)[X]} (hB : B.Monic)
    (hC : ∀ i : ℕ, ‖C.coeff i‖ ≤ 1) (hAB : ∀ i : ℕ, ‖(A * B - C).coeff i‖ < 1)
    (hA'B : ∀ i : ℕ, ‖C.coeff i - (A' * B).coeff i‖ < 1) (hA'_one : 1 ≤ ‖eval 1 A'‖) :
    ∃ e : (intQpBar ℓ)[X], A ∣ e.map (intQpBar ℓ).subtype ∧ e.eval 1 = 1 := by
  -- Monic factors cancel in bounds on coefficients: `A` is integral and `A ≡ A'`, so `A(1)` has
  -- norm at least one, and `e = A / A(1)` is integral.
  have hAB_int (i : ℕ) : ‖(A * B).coeff i‖ ≤ 1 :=
    calc ‖(A * B).coeff i‖ = ‖(A * B - C).coeff i + C.coeff i‖ := by simp
      _ ≤ max ‖(A * B - C).coeff i‖ ‖C.coeff i‖ := norm_add_le_max _ _
      _ ≤ 1 := max_le (hAB i).le (hC i)
  have hA_int (i : ℕ) : ‖A.coeff i‖ ≤ 1 := norm_coeff_le_of_mul_monic hB hAB_int i
  have h_prod (i : ℕ) : ‖((A - A') * B).coeff i‖ < 1 :=
    calc ‖((A - A') * B).coeff i‖
        = ‖(A * B - C).coeff i + (C.coeff i - (A' * B).coeff i)‖ := by simp [sub_mul]
      _ ≤ max ‖(A * B - C).coeff i‖ ‖C.coeff i - (A' * B).coeff i‖ := norm_add_le_max _ _
      _ < 1 := max_lt (hAB i) (hA'B i)
  have h_diff_one : ‖(A' - A).eval 1‖ < 1 := by
    simpa [norm_sub_rev] using norm_eval_one_lt_one (norm_coeff_lt_one_of_mul_monic hB h_prod)
  have hA_one : 1 ≤ ‖A.eval 1‖ := by
    contrapose! hA'_one
    calc ‖A'.eval 1‖ = ‖(A' - A).eval 1 + A.eval 1‖ := by simp
      _ ≤ max ‖(A' - A).eval 1‖ ‖A.eval 1‖ := norm_add_le_max _ _
      _ < 1 := max_lt h_diff_one hA'_one
  have hA_ne : A.eval 1 ≠ 0 := norm_pos_iff.1 (one_pos.trans_le hA_one)
  obtain ⟨e, he⟩ : ∃ e : (intQpBar ℓ)[X],
      e.map (intQpBar ℓ).subtype = A * Polynomial.C (A.eval 1)⁻¹ := by
    rw [← mem_lifts, lifts_iff_coeff_lifts]
    intro i
    have h_int : ‖A.coeff i * (A.eval 1)⁻¹‖ ≤ 1 := by
      simpa [mul_inv_le_iff₀ (norm_pos_iff.2 hA_ne)] using (hA_int i).trans hA_one
    exact ⟨⟨_, h_int⟩, (coeff_mul_C ..).symm⟩
  have he_one : (intQpBar ℓ).subtype (e.eval 1) = 1 := by
    rw [← eval_one_map, he, eval_mul, eval_C, mul_inv_cancel₀ hA_ne]
  exact ⟨e, ⟨_, he⟩, Subtype.ext he_one⟩

/-- Let p be a nonzero polynomial over ℚ̄_ℓ, and let y^j − 1 have norm one for 1 ≤ j ≤ deg p. Then
for some i every root μ of p has ‖1 − y^i μ‖ ≥ 1, that is, y^i μ is not congruent to one modulo the
maximal ideal. -/
lemma exists_one_le_nnnorm_one_sub_pow_mul_root {p : (PadicAlgCl ℓ)[X]} (hp : p ≠ 0)
    {y : PadicAlgCl ℓ} (hy : ∀ j ∈ Set.Icc 1 p.natDegree, ‖y ^ j - 1‖ = 1) :
    ∃ i : ℕ, ∀ μ ∈ p.roots, 1 ≤ ‖1 - y ^ i * μ‖₊ := by
  -- Each root μ has y^i μ ≡ 1 for at most one i ≤ deg p, and there are at most deg p roots.
  by_contra! h_all
  choose μ h_root h_lt using h_all
  replace h_lt (i : ℕ) : valuation (1 - y ^ i * μ i) < 1 := h_lt i
  have h_ne (i j : Fin (p.natDegree + 1)) (hij : i < j) : μ i ≠ μ j := by
    intro h_eq
    -- `y^i μ` is a unit, so `y^j μ − y^i μ = y^i μ (y^(j−i) − 1)` is one too; but it is the
    -- difference of two numbers of norm < 1.
    have h_unit : valuation (y ^ (i : ℕ) * μ i) = 1 := by
      simpa using valuation.map_one_sub_of_lt (h_lt i)
    have h_step : valuation (y ^ (j - i : ℕ) - 1) = 1 := NNReal.eq (hy _ (by grind))
    have h_factor : 1 - y ^ (i : ℕ) * μ i - (1 - y ^ (j : ℕ) * μ j) =
        y ^ (i : ℕ) * μ i * (y ^ (j - i : ℕ) - 1) := by
      rw [← h_eq, ← pow_sub_mul_pow y (show (i : ℕ) ≤ j from hij.le)]
      ring
    exact (valuation.map_sub_lt (h_lt i) (h_lt j)).ne
      (by rw [h_factor, map_mul, h_unit, h_step, mul_one])
  exact hp <| eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (Function.Injective.of_lt_imp_ne h_ne)
    (fun i ↦ isRoot_of_mem_roots (h_root i)) (by simp)

/-- Let `P` be fixed parameters and `D` data for them, which determine a CM field E = `D.E`. Let
`AbsGal D` = Gal(Ω/E) be its absolute Galois group, with Ω an algebraic closure of E. Let T be a
continuous function from this group to n × n matrices over ℚ̄_ℓ. Let δ_i be a sequence of elements
of the group with T(δ_i) = y^i A, and let y^j − 1 have norm one for 1 ≤ j ≤ 4n + 2. Then for some i,
‖det(1 − T(φ))‖ ≥ 1 for all φ near δ_i. -/
lemma exists_eventually_one_le_norm_eval_charpoly {P : Parameters} {D : Data P} {n : Type*}
    [Fintype n] [DecidableEq n] {T : AbsGal D → Matrix n n (PadicAlgCl ℓ)} (hT : Continuous T)
    (δ : ℕ → AbsGal D) {y : PadicAlgCl ℓ} {A : Matrix n n (PadicAlgCl ℓ)}
    (hTδ : ∀ i : ℕ, T (δ i) = y ^ i • A) (hy : ∀ j ∈ Set.Icc 1 (4 * card n + 2), ‖y ^ j - 1‖ = 1) :
    ∃ i : ℕ, ∀ᶠ φ : AbsGal D in nhds (δ i), 1 ≤ ‖(T φ).charpoly.eval 1‖ := by
  -- Choose i with 1 ≢ y^i μ for the eigenvalues μ of A. The bound on det(1 − T(φ)) is open.
  obtain ⟨i, hi⟩ : ∃ i : ℕ, ∀ μ ∈ A.charpoly.roots, 1 ≤ ‖1 - y ^ i * μ‖₊ :=
    exists_one_le_nnnorm_one_sub_pow_mul_root (charpoly_monic A).ne_zero fun j hj ↦
      hy j (by grind [charpoly_natDegree_eq_dim])
  have h_det : (1 - T (δ i)).det = (A.charpoly.roots.map fun μ ↦ 1 - y ^ i * μ).prod := by
    have h_aeval := det_aeval_neg_eq_prod_roots A (1 + y ^ i • X : (PadicAlgCl ℓ)[X])
    simpa [hTδ, sub_eq_add_neg] using h_aeval
  have h_one_le : 1 ≤ valuation (1 - T (δ i)).det := by
    rw [h_det, map_multiset_prod, Multiset.map_map]
    exact Multiset.one_le_prod_map hi
  -- The open unit ball is closed, so its complement pulls back to a neighbourhood of δ i.
  have h_closed : IsClosed ((fun φ : AbsGal D ↦ (1 - T φ).det) ⁻¹' Metric.ball 0 1) :=
    (isClosed_ball 0 1).preimage (by fun_prop)
  use i
  filter_upwards [h_closed.compl_mem_nhds (by simpa using NNReal.coe_mono h_one_le)] with φ hφ
  simpa [eval_charpoly] using hφ

/-- Let M be an n × n matrix over ℚ̄_ℓ and u a number of norm one. Call two numbers congruent if
their difference has norm less than one, that is, lies in the maximal ideal. If the i-th
coefficients of H and of char M are congruent, then so are those of u^n·H(u⁻¹X) and char (uM). -/
lemma norm_coeff_comp_sub_charpoly_smul_lt_one {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n (PadicAlgCl ℓ)} {H : (PadicAlgCl ℓ)[X]} {u : PadicAlgCl ℓ} (hu : ‖u‖ = 1)
    {i : ℕ} (h_lt : ‖(M.charpoly - H).coeff i‖ < 1) :
    ‖(C (u ^ card n) * H.comp (C u⁻¹ * X) - (u • M).charpoly).coeff i‖ < 1 := by
  have hu_ne : u ≠ 0 := norm_pos_iff.1 (one_pos.trans_eq hu.symm)
  have h_smul : (u • M).charpoly.coeff i = u ^ card n * u⁻¹ ^ i * M.charpoly.coeff i := by
    rw [charpoly_smul_coeff]
    rcases le_or_gt i (card n) with hi | hi
    · rw [pow_sub₀ u hu_ne hi, inv_pow]
    · simp [coeff_eq_zero_of_natDegree_lt ((charpoly_natDegree_eq_dim M).trans_lt hi)]
  have h_coeff : (C (u ^ card n) * H.comp (C u⁻¹ * X) - (u • M).charpoly).coeff i =
      -(u ^ card n * u⁻¹ ^ i) * (M.charpoly - H).coeff i := by
    rw [coeff_sub, coeff_sub, coeff_C_mul, comp_C_mul_X_coeff, h_smul]
    ring
  simpa only [h_coeff, norm_mul, norm_neg, norm_pow, norm_inv, hu, inv_one, one_pow, one_mul]

/-- If s⁻¹ is an arithmetic Frobenius at a place `A` of `Ω` over w ∤ ℓ, that is, s is a geometric
one, then χ(s) = ι(X₀⁻¹), where X₀ = `O.charW.frobValue r w` and ι = `ιℓ` is the fixed isomorphism
from ℂ to ℚ̄_ℓ. -/
lemma normalizingAvatar_eq_of_isFrob [PadicIso ℓ] {P : Parameters} {D : Data P} {r n : Type}
    [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] (O : DescentPair D.E r n)
    {w : FinPlace D.E} {A : ClosurePlace} (hA : IsPlaceOver A w) (hℓ : ↑ℓ ∉ w.asIdeal)
    {s : AbsGal D} (hs_inv : IsFrob A w.q s⁻¹) :
    (normalizingAvatar O s).val = ιℓ (O.charW.frobValue r w)⁻¹ := by
  simpa using normalizingAvatar_eq_of_isFrob_inv (O := O) hA hℓ 1 (s := s) (by rwa [pow_one])

variable {P : Parameters} {D : Data P} {r n : Type} [Fintype n] [DecidableEq n] [PadicIso ℓ]
  [Fintype r] [DecidableEq r] [Nonempty n]

/-- Let `f` be a nonzero form on the definite space V of highest weight `(O.columnCount, O.detExp)`:
column numbers and a power of the determinant at each infinite place. Let `f` lie in the isotypic
space `x`, a space of forms with given Hecke eigenvalues at almost all places. Let
χ = `normalizingAvatar O` be the ℓ-adic character attached, via ιℓ, to the Hecke character of W.
Assume every g in Gal(Ω/E) has eigenvalue 1 on `normalisedRep O x.galRep`, the twist of `x.galRep`
by χ. Let w ∤ ℓ be a split place of norm q where `f` has Hecke polynomial S. Then each X₀q^i with
i < n − r is a root of S. Here X₀ = `O.charW.frobValue r w` is the inverse of χ at a geometric
Frobenius, read in ℂ. -/
lemma isRoot_hecke_chain {O : DescentPair D.E r n}
    {x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)}
    {f : (stdSpace D.E n).forms (O.columnCount, O.detExp)} (hf : f ∈ x.val) (hf_ne : f ≠ 0)
    (h_one : ∀ g : Gal(Ω/D.E), (normalisedRep O x.galRep g).val.charpoly.IsRoot 1)
    {w : FinPlace D.E} {hw : star w ≠ w} {S : ℂ[X]} {i : ℕ} (hℓ : ↑ℓ ∉ w.asIdeal)
    (hS : HasHeckePolyAt f.val w hw S) (hi : i < O.rankDiff) :
    S.IsRoot (O.charW.frobValue r w * w.q ^ i) := by
  -- A geometric Frobenius `s⁻¹` at `w` has eigenvalue one on the normalised representation, which
  -- makes `frobValue` a root of `S`; as `‖frobValue‖ ^ 2 = w.q ^ card r`, unitarity gives the whole
  -- chain (`Patching.isRoot_chain_of_norm`).
  have hA : IsPlaceOver (placeOver w) w := w.isPlaceOver_placeOver
  obtain ⟨s, hs⟩ : ∃ s : AbsGal D, IsFrob (placeOver w) w.q s := hA.exists_isFrob (AbsGal D)
  have hs_inv : IsFrob (placeOver w) w.q s⁻¹⁻¹ := by rwa [inv_inv]
  -- Local-global compatibility: the Hecke polynomial kills geometric Frobenius.
  have h_compat : IsCompatibleAt f.val (card n) w x.galRep (placeOver w) :=
    (sphericalCompat_std w).isCompatibleAt f.property (x.isEigenform hf hf_ne)
      (x.attached_galRep hf hf_ne) hS.1 hA
  have h_kill : aeval (x.galRep s⁻¹).val (S.map ιℓ.toRingHom) = 0 :=
    (h_compat.polyKillsAt hS (s := s⁻¹) hs_inv).1 (hA.valuation_natCast_eq_one_iff.2 hℓ)
  have h_kill_twist : aeval (normalisedRep O x.galRep s⁻¹).val
      ((S.map ιℓ.toRingHom).comp ((normalizingAvatar O s⁻¹).val⁻¹ • X)) = 0 := by
    simpa [aeval_comp, Units.smul_def] using h_kill
  have h_root : S.IsRoot (O.charW.frobValue r w) := by
    have h_root_twist : ((S.map ιℓ.toRingHom).comp ((normalizingAvatar O s⁻¹).val⁻¹ • X)).IsRoot
      1 :=
      isRoot_of_isRoot_charpoly h_kill_twist (h_one s⁻¹)
    rw [normalizingAvatar_eq_of_isFrob O hA hℓ hs_inv] at h_root_twist
    exact .of_map (by simpa using h_root_twist) ιℓ.toRingHom.injective
  have h_norm : ‖O.charW.frobValue r w‖ ^ 2 * w.q ^ O.rankDiff = w.q ^ card n := by
    simp [AutChar.frobValue, sq, ← mul_pow, ← pow_add, O.rank_lt.le]
  obtain ⟨h_sph, t, h_poly, h_eig⟩ := hasHeckePolyAt_iff_localFormRep.1 hS
  exact Patching.isRoot_chain_of_norm isUnitary_localFormRep h_sph hf_ne h_poly h_eig h_root h_norm
    hi

/-- Let `O` be a descent pair, `f` a nonzero form on V in the space `x` of forms of weight
`(O.columnCount, O.detExp)` with given Hecke eigenvalues, and let every g in Gal(Ω/E), Ω an
algebraic closure of ℚ, have the eigenvalue 1 on the twist of `x.galRep` by the ℓ-adic character
χ = `normalizingAvatar O`. Let σ = `y.frob` be a geometric Frobenius at a split place w = `y.place`,
w ∤ ℓ, of norm q, where `f` has Hecke polynomial H, and ι = `ιℓ` the fixed isomorphism from ℂ to
ℚ̄_ℓ. Then ∏_{i<n−r}(X − q^i) divides H(ι⁻¹(χ(σ))⁻¹·X). -/
lemma prod_X_sub_C_dvd_comp_of_hasHeckePolyAt {O : DescentPair D.E r n}
    {x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)}
    {f : (stdSpace D.E n).forms (O.columnCount, O.detExp)} (hf : f ∈ x.val) (hf_ne : f ≠ 0)
    (h_one : ∀ g : Gal(Ω/D.E), (normalisedRep O x.galRep g).val.charpoly.IsRoot 1)
    (y : FrobeniusDatum D.E) {hw : star y.place ≠ y.place} {H : ℂ[X]} (hℓ : ↑ℓ ∉ y.place.asIdeal)
    (hH : HasHeckePolyAt f.val y.place hw H) :
    ∏ i ∈ Finset.range O.rankDiff, (X - C (y.place.q ^ i : ℂ)) ∣
      H.comp (C (ιℓ.symm (normalizingAvatar O y.frob).val)⁻¹ * X) := by
  have h_chi : (normalizingAvatar O y.frob).val = ιℓ (O.charW.frobValue r y.place)⁻¹ :=
    normalizingAvatar_eq_of_isFrob O y.isPlaceOver hℓ y.isFrob_inv
  have h_inj : Function.Injective fun i : ℕ ↦ (y.place.q ^ i : ℂ) :=
    (pow_right_strictMono₀ (by simp)).injective
  rw [h_chi, RingEquiv.symm_apply_apply, inv_inv]
  refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C h_inj).set_pairwise _) fun i hi ↦ ?_
  have h_root : H.IsRoot (O.charW.frobValue r y.place * y.place.q ^ i) :=
    isRoot_hecke_chain hf hf_ne h_one hℓ hH (Finset.mem_range.1 hi)
  rw [dvd_iff_isRoot]
  simpa using h_root

/-- Let `O` be a descent pair, `f` a nonzero form on V in the space `x` of forms with given Hecke
eigenvalues, and u the twist of `x.galRep` by the ℓ-adic character χ = `normalizingAvatar O`. Assume
that all characteristic polynomials of u are integral and have the root 1. Write t = `O.rankDiff` (=
n − r), ι = `ιℓ` for the isomorphism from ℂ to ℚ̄_ℓ and c = `cyclotomicInv` for the inverse
cyclotomic character. The following holds for most geometric Frobenius elements φ = `y.frob`, at
places w = `y.place`: every nonempty open subset of Gal(Ω/E) has a nonempty open part in which it
holds for almost all w. If det (X − u(φ)) is congruent, coefficientwise modulo the maximal ideal, to
S · ∏_{i<t} (X − c(φ)^i) with ‖S(1)‖ ≥ 1, then the rescaled Hecke polynomial H_w(X₀X) of `x`,
X₀ = ι⁻¹(χ(φ))⁻¹, is the chain ∏_{i<t} (X − q_w^i) times a divisor of an ℓ-adically integral
polynomial e with e(1) = 1 (`HasRootChain`). -/
lemma eventually_exists_hasRootChain {O : DescentPair D.E r n}
    {x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp)}
    {f : (stdSpace D.E n).forms (O.columnCount, O.detExp)} (hf : f ∈ x.val) (hf_ne : f ≠ 0)
    (h_one : ∀ g : Gal(Ω/D.E), (normalisedRep O x.galRep g).val.charpoly.IsRoot 1)
    (h_charpoly_int : ∀ (g : Gal(Ω/D.E)) (i : ℕ),
      ‖(normalisedRep O x.galRep g).val.charpoly.coeff i‖ ≤ 1) :
    ∀ᶠ y : FrobeniusDatum D.E in mostFrobenii D.E, ∀ S : (PadicAlgCl ℓ)[X], 1 ≤ ‖eval 1 S‖ →
      -- the characteristic polynomial at Frobenius is congruent to `S` times the chain
      (∀ i : ℕ,
        ‖(normalisedRep O x.galRep y.frob).val.charpoly.coeff i -
          (S * ∏ j ∈ Finset.range O.rankDiff,
            (X - C (cyclotomicInv ℓ D.E (PadicAlgCl ℓ) y.frob ^ j))).coeff i‖ < 1) →
      ∃ e : EllAdicIntegers[X],
        HasRootChain (x.heckePolyAt y.place) (e.map (algebraMap EllAdicIntegers ℂ)) y.place.q
          (ιℓ.symm (normalizingAvatar O y.frob).val)⁻¹ O.rankDiff ∧
        e.eval 1 = 1 := by
  -- The product of the X − q^i, with image B under ι, divides the rescaled Hecke polynomial, with
  -- a quotient T. As `x.galRep` is attached to the Hecke polynomials,
  -- χ^n · ιT · B ≡ char (χ · `x.galRep`) ≡ S · B, where χ is the value of `normalizingAvatar`, and
  -- `exists_integral_multiple_eval_one` applies.
  filter_upwards [(x.attached_galRep hf hf_ne).eventually_norm_coeff_le one_half_pos,
    tendsto_place_mostFrobenii.eventually (x.isEigenform hf hf_ne).2,
    tendsto_place_mostFrobenii.eventually (eventually_notMem_star_notMem ℓ ∅)]
    with y h_att h_eig ⟨_hw_star, _hw_not_mem, hℓ⟩ S hS h_cong
  obtain ⟨hw, h_hecke⟩ := h_eig y.prime_q
  obtain ⟨T, hT⟩ : ∏ i ∈ Finset.range O.rankDiff, (X - C (y.place.q ^ i : ℂ)) ∣
      (x.heckePolyAt y.place).comp (C (ιℓ.symm (normalizingAvatar O y.frob).val)⁻¹ * X) :=
    prod_X_sub_C_dvd_comp_of_hasHeckePolyAt hf hf_ne h_one y hℓ h_hecke
  set B : (PadicAlgCl ℓ)[X] :=
    ∏ j ∈ Finset.range O.rankDiff, (X - C (cyclotomicInv ℓ D.E (PadicAlgCl ℓ) y.frob ^ j))
  let χ : PadicAlgCl ℓ := (normalizingAvatar O y.frob).val
  let H : (PadicAlgCl ℓ)[X] := (x.heckePolyAt y.place).map ιℓ.toRingHom
  -- The same factorisation after applying ι.
  have hB : (∏ i ∈ Finset.range O.rankDiff, (X - C (y.place.q ^ i : ℂ))).map ιℓ.toRingHom = B := by
    simp [B, cyclotomicInv_frob y hℓ, Polynomial.map_prod]
  have hT_map : T.map ιℓ.toRingHom * B = H.comp (C χ⁻¹ * X) := by
    rw [mul_comm, ← hB, ← Polynomial.map_mul, ← hT, Polynomial.map_comp]
    simp [H, χ]
  have hχ : ‖χ‖ = 1 := norm_eq_one_of_continuous (AlgHeckeChar.continuous_avatar _) _
  have h_twist : (normalisedRep O x.galRep y.frob).val = χ • (x.galRep y.frob).val := by
    simp [χ, Units.smul_def]
  have h_near (i : ℕ) : ‖(C (χ ^ card n) * T.map ιℓ.toRingHom * B -
      (normalisedRep O x.galRep y.frob).val.charpoly).coeff i‖ < 1 := by
    have h_half : ‖((x.galRep y.frob).val.charpoly - H).coeff i‖ ≤ 1 / 2 := h_att y.frob rfl i
    rw [mul_assoc, hT_map, h_twist]
    exact norm_coeff_comp_sub_charpoly_smul_lt_one hχ (h_half.trans_lt one_half_lt_one)
  obtain ⟨e, h_dvd, he_one⟩ : ∃ e : (intQpBar ℓ)[X],
      C (χ ^ card n) * T.map ιℓ.toRingHom ∣ e.map (intQpBar ℓ).subtype ∧ e.eval 1 = 1 :=
    exists_integral_multiple_eval_one (monic_prod_X_sub_C _ _) (h_charpoly_int y.frob) h_near
      h_cong hS
  -- Carry the divisibility back to ℂ along the inverse of ι.
  have h_back : T ∣ (e.map (intQpBar ℓ).subtype).map ιℓ.symm.toRingHom := by
    simpa [Polynomial.map_map] using
      Polynomial.map_dvd ιℓ.symm.toRingHom (dvd_of_mul_left_dvd h_dvd)
  rw [Polynomial.map_map] at h_back
  -- `EllAdicIntegers` is `intQpBar ℓ`, mapped to ℂ through the inverse of ι, by definition.
  exact ⟨e, ⟨T, hT, h_back⟩, he_one⟩

end HeckeString

/-!
## Hecke-stable subspaces of forms: orthogonal complements, eigenforms

Hecke-stable subspaces Z of the space `New.DescentPair.FormV` of forms on the definite space V of a
descent pair (`New.DescentPair`); `New.DescentPair.heckePolyOnForms` is the Hecke polynomial at a
split place as an operator.
-/

section HeckeStableSubspaces

open Patching LevelPlaces.LevelForm Submodule

/-- Let `O` be a descent pair over the CM field E = `D.E` of admissible data `D`, and `Z` a subspace
of `O.FormV`, the forms of the level and weight of `O` on its definite space, with their inner
product. For a split place w the operator `O.heckePolyOnForms` is the Hecke polynomial
∑ᵢ (−X)^i q^(i(i−1)/2) T_{w,i}, evaluated at the complex number `X`. If `Z` is stable under these
operators for all X at all split w off the places of `O` and their conjugates, then so is its
orthogonal complement. -/
lemma orthogonal_mem_invtSubmodule_heckePolyOnForms {P : Parameters} {D : Data P} {r n : Type}
    [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair D.E r n}
    {Z : Submodule ℂ O.FormV}
    (hZ_stable : ∀ (w : FinPlace D.E) (hw : star w ≠ w) (hS : w ∉ O.places.conjClosure) (X : ℂ),
      Z ∈ (O.heckePolyOnForms (w := w) hw hS X).invtSubmodule)
    (w : FinPlace D.E) (hw : star w ≠ w) (hS : w ∉ O.places.conjClosure) (X : ℂ) :
    Zᗮ ∈ (O.heckePolyOnForms (w := w) hw hS X).invtSubmodule := by
  -- The adjoint of a Hecke operator at `w` is a Hecke operator at `star w`, and it preserves `Z`.
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  refine fun y hy ↦ (mem_orthogonal Z _).2 fun z hz ↦ ?_
  have hS' : star w ∉ O.places.conjClosure := by simpa [Set.conjClosure, and_comm] using hS
  have h_adj : inner ℂ (O.heckePolyOnForms hw hS X y) z =
      inner ℂ y (O.heckePolyOnForms (star_injective.ne hw) hS' (star X) z) :=
    innerAt_heckePolyOnForms (.refl ℂ) y z hw hS hS' X
  rw [inner_eq_zero_symm, h_adj, inner_eq_zero_symm]
  exact (mem_orthogonal Z y).1 hy _ (hZ_stable (star w) (star_injective.ne hw) hS' (star X) hz)

/-- Let `O` be a descent pair over the CM field E = `D.E` of admissible data `D`, and `Z`, `N`
subspaces of `O.FormV`, the forms of the level and weight of `O` on its definite space
V = `stdSpace D.E n`. Let `Z` be stable under the Hecke polynomial operators `O.heckePolyOnForms`,
evaluated at any complex X, at all split places off the places of `O` and their conjugates. If every
form of `Z` that, viewed as a smooth form on V, is nonzero and lies in an isotypic space lies in
`N`, then `Z ≤ N`. -/
lemma le_of_isotypic_mem {P : Parameters} {D : Data P} {r n : Type} [Fintype r] [DecidableEq r]
    [Fintype n] [DecidableEq n] {O : DescentPair D.E r n} {Z N : Submodule ℂ O.FormV}
    (hZ_stable : ∀ (w : FinPlace D.E) (hw : star w ≠ w) (hS : w ∉ O.places.conjClosure) (X : ℂ),
      Z ∈ (O.heckePolyOnForms (w := w) hw hS X).invtSubmodule)
    (h_iso : ∀ x : Isotypic (stdSpace D.E n) (O.columnCount, O.detExp), ∀ v : O.FormV, v ∈ Z →
      v.toSmoothForm ∈ x.val ∧ v.toSmoothForm ≠ 0 → v ∈ N) : Z ≤ N := by
  classical
  -- View the forms as smooth forms. The image `Z'` of `Z` is spherical off the chosen places `S`
  -- and stable under the Hecke operators off `S` and its conjugate, so it is spanned by eigenforms;
  -- these lie in `N`.
  let S : Finset (FinPlace D.E) := Finset.univ.image O.placeAt
  have hS : (S : Set (FinPlace D.E)) = O.places := by simp [S]
  let Z' : Submodule ℂ ((stdSpace D.E n).forms (O.columnCount, O.detExp)) := Z.map toSmoothForm
  let τ : Representation ℂ _ ((stdSpace D.E n).forms (O.columnCount, O.detExp)) :=
    (stdSpace D.E n).formTranslation (O.columnCount, O.detExp)
  have h_sph : Z' ≤ levelSpace τ (stdLevel D.E n ⊓ Gf.trivialOn n S) := by
    -- An integral point `g` that is trivial at `S` lies in the level, so it fixes every form.
    rintro _ ⟨y, -, rfl⟩
    refine mem_levelSpace.2 fun ⟨g, hg⟩ ↦ ?_
    have h_level : g ∈ levelOf O.placeAt ⊥ := inf_trivialOn_le_levelOf (by rwa [hS] at hg)
    have h_fix : τ g (toSmoothForm y) = toSmoothForm y :=
      Subtype.ext (congrArg Subtype.val (y.algFormRep_eq_self_of_mem h_level))
    simpa using h_fix
  have h_stable (w : FinPlace D.E) (hw : star w ≠ w) (h_out : w ∉ S) (h_out' : star w ∉ S)
      (i : ℕ) : ∀ f ∈ Z', heckeSplit τ (w := w) hw i f ∈ Z' := by
    rintro _ ⟨y, hy, rfl⟩
    have h_off : w ∉ O.places.conjClosure := by simp [← hS, h_out, h_out']
    have h_poly (X : ℂ) : heckePolyOp τ hw X (toSmoothForm y) ∈ Z' :=
      ⟨O.heckePolyOnForms hw h_off X y, hZ_stable w hw h_off X hy, rfl⟩
    -- The operators sending `toSmoothForm y` into `Z'` form a subspace with all the Hecke
    -- polynomial operators in it, hence with every `heckeSplit` in it.
    exact heckeSplit_mem_of_heckePolyOp (Z'.comap (.applyₗ (toSmoothForm y))) h_poly i
  rw [← map_le_map_iff_of_injective (f := toSmoothForm) Subtype.val_injective]
  refine (le_span_isSphericalOff Z' h_sph h_stable).trans (span_le.2 ?_)
  rintro _ ⟨⟨v, hv, rfl⟩, Q, h_eig⟩
  obtain ⟨x, hx⟩ := exists_isotypic_of_isSphericalOff h_eig
  exact ⟨v, h_iso x v hv hx, rfl⟩

end HeckeStableSubspaces

end New.Selmer
