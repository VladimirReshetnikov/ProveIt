import Lib.GaloisRep.Main.Defs

/-!
# Free cocharacter weights force rank n and identify killing polynomials

A Galois representation that is only known to be killed, for most Frobenius elements (the filter
`New.mostFrobenii`), by monic polynomials of degree `n` is shown to have rank `n`, given that the
span of its image contains the diagonal matrices and that a one-parameter torus with `n` free
weights (`New.HasNoSmallRelations`) lies in the Zariski closure of a conjugate of the image of every
neighbourhood of `1`.

* `New.powMinor y m a`: a minor of order `m` of the matrix whose column `j < m` lists the entries of
  `y ^ j`. Over a field all of them vanish exactly when `1, y, …, y ^ (m - 1)` are linearly
  dependent.
* `New.exists_factor_charpoly`: over an integrally closed domain, if these minors all vanish, a
  factor of degree less than `m` of the characteristic polynomial of `y` kills `y`.
* `New.HasNoSmallRelations.inv_scalar_on_blocks`: if these minors vanish, with `m ≤ n + 1` and `c`
  surjective, for `diagonal (T ∘ e ∘ c) * x` over the Laurent polynomials, then `n < m` and on each
  fibre of `c` the block of `x⁻¹` is a scalar matrix.
* `New.card_eq_and_charpoly_eq`: the rank is `n` and the polynomials are the characteristic
  polynomials.

Notions from other files:
* `New.Ω`: the field `Ω` is an algebraic closure of `ℚ`: it has characteristic zero, is
  algebraically closed and is algebraic over `ℚ`.
* `New.HasNoSmallRelations e`: for `e : Fin n → ℤ`, distinct exponent vectors `α` of the same total
  degree at most `(n + 1) ^ 2` have distinct weights `∑ i, α i * e i`.
* `New.FrobeniusDatum E`: a place of degree one of `E` with a Frobenius element `frob` above it.
* `New.mostFrobenii E`: the filter of sets of such data that, inside every nonempty open set of
  `Gal(Ω/E)`, contain all data at almost all places whose Frobenius lies in a smaller nonempty open
  set.
* `T i`: the monomial of degree `i` in the Laurent polynomials `k[T;T⁻¹]`.

## Relation to the literature

Known result: Rank n and characteristic polynomials from Frobenius polynomial relations. Let a
continuous representation have image spanning the diagonal matrices, and let monic degree-n
polynomials kill it at most Frobenius elements. If a cocharacter with free (very different)
exponents constrains it, then its rank is n and the polynomials are its characteristic polynomials
at most Frobenius elements. This is one step inside the known construction of Galois representations
for definite unitary groups. In the literature, Frobenius polynomial relations on a dense set
determine a representation when the n-dimensional one is known and large. Related work:
Boston–Lenstra–Ribet 1991; Nekovář, Eichler–Shimura relations and semisimplicity, 2018;
Fayad–Nekovář 2019; Harris–Taylor 2001, VII.1.8.

See also `Lib.GaloisRep.Main.OddRank`.
-/

namespace New

open Matrix MvPolynomial Polynomial Finset Algebra Fintype Submodule Function ConjAct
  LaurentPolynomial Fin Filter

variable {k K N R S A : Type} [NormedField k] [Fintype N] [DecidableEq N] [CommRing R] [CommRing S]
  {m n : ℕ} {e : Fin n → ℤ}
  (y : Matrix N N R) [NormedField K] [NormedAlgebra K k] [CommRing A] [Algebra A R] [Algebra A S]

/-- The minor of order `m`, at the rows `a 0, …, a (m - 1)`, of the matrix with rows indexed by
`N × N` whose column `j < m` lists the entries of the square matrix `y ^ j`: its entry at `(i, j)`
is the entry of `y ^ j` at the place `a i`. -/
noncomputable abbrev powMinor (m : ℕ) (a : Fin m → N × N) : R :=
  (of (flip (fun j : Fin m ↦ uncurry (y ^ j.1)) ∘ a)).det

@[simp]
lemma map_powMinor (a : Fin m → N × N) (φ : R →ₐ[A] S) :
    φ (powMinor y m a) = powMinor (φ.mapMatrix y) m a := by
  have h_pow (j : ℕ) : y.map φ ^ j = (y ^ j).map φ := (map_pow φ.mapMatrix y j).symm
  rw [powMinor, powMinor, φ.map_det]
  congr 1
  ext i j
  simp [h_pow, flip, uncurry]

/-- Let `y` be a square matrix over an integrally closed domain `R`. If all minors `powMinor y m a`
of its first `m` powers vanish, then `y.charpoly = p * q` with `p` of degree less than `m` and
`p(y) = 0`. -/
lemma exists_factor_charpoly [IsDomain R] [IsIntegrallyClosed R]
    (h_minor : ∀ a : Fin m → N × N, powMinor y m a = 0) :
    ∃ p q : R[X], y.charpoly = p * q ∧ p.natDegree < m ∧ p.aeval y = 0 := by
  -- Over the fraction field the first `m` powers of `y` are dependent.
  let F : Type := FractionRing R
  let z : Matrix N N F := (ofId R F).mapMatrix y
  have h_lt : (minpoly F z).natDegree < m := by
    by_contra! h_le
    have hz_minor (a : Fin m → N × N) : powMinor z m a = 0 := by
      rw [← map_powMinor y a (ofId R F), h_minor a, map_zero]
    have h_pow : LinearIndependent F fun j : Fin m ↦ z ^ (j : ℕ) :=
      (linearIndependent_pow z).comp (castLE h_le) (castLE_injective h_le)
    exact det_eval_eq_zero_iff_not_linearIndependent.mp hz_minor
      (h_pow.of_comp (LinearEquiv.curry (R := F) (M := F) (V := N) (V₂ := N)).toLinearMap)
  -- By Gauss's lemma the minimal polynomial comes from a monic factor `p` of `y.charpoly`.
  have h_monic : (minpoly F z).Monic := minpoly.monic z.isIntegral
  have h_dvd : minpoly F z ∣ y.charpoly.map (algebraMap R F) :=
    z.minpoly_dvd_charpoly.trans (charpoly_map y (algebraMap R F)).dvd
  have h_lifts : minpoly F z ∈ lifts (algebraMap R F) := by
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd F y.charpoly_monic h_dvd
    exact (mem_lifts _).mpr ⟨g, by simpa [h_monic.leadingCoeff] using hg⟩
  obtain ⟨p, hp, hp_deg, hp_monic⟩ := lifts_and_natDegree_eq_and_monic h_lifts h_monic
  obtain ⟨q, hq⟩ : p ∣ y.charpoly :=
    (map_dvd_map (algebraMap R F) (IsFractionRing.injective R F) hp_monic).mp (by rwa [hp])
  -- The image of `p(y)` over `F` is `p(z)`, a value of the minimal polynomial of `z`.
  have hz_root : (ofId R F).mapMatrix (p.aeval y) = 0 := by
    rw [← aeval_algHom_apply, ← Polynomial.aeval_map_algebraMap F, hp, minpoly.aeval]
  exact ⟨p, q, hq, by lia, Matrix.map_injective (IsFractionRing.injective R F)
    (by simpa [ofId] using hz_root)⟩

/-- Let the weights `e : Fin n → ℤ` be free (`HasNoSmallRelations e`: distinct exponent vectors of
one total degree at most `(n + 1) ^ 2` have distinct weights `∑ i, α i * e i`), let `c : N → Fin n`,
let `x` be an invertible matrix over `k` and let `m ≤ n + 1`. If all minors `powMinor` of order `m`
of the product of the diagonal matrix with entries `T (e (c a))` and `x` over `k[T;T⁻¹]` vanish,
then so do those of the product of the diagonal matrix with entries `X (c a)` and `x` over the
polynomials in the variables `X i`. -/
private lemma powMinor_diagonal_X_mul_eq_zero {c : N → Fin n} (he : HasNoSmallRelations e)
    {x : GL N k} (hm_le : m ≤ n + 1)
    (h_vanish : ∀ a : Fin m → N × N,
      powMinor (diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C) m a = 0)
    (a : Fin m → N × N) :
    powMinor (diagonal (X ∘ c) * (x : Matrix N N k).map MvPolynomial.C) m a = 0 := by
  set y : Matrix N N (MvPolynomial (Fin n) k) :=
    diagonal (X ∘ c) * (x : Matrix N N k).map MvPolynomial.C
  -- Each entry of `y ^ j` is homogeneous of degree `j`.
  have hy (j : ℕ) : ∀ a b : N, ((y ^ j) a b).IsHomogeneous j := by
    induction j with
    | zero => simp [← totalDegree_zero_iff_isHomogeneous, Matrix.one_apply, apply_ite]
    | succ j ih =>
      simp_all [y, pow_add, mul_apply, diagonal, mul_comm (X _), isHomogeneous_C_mul_X,
        IsHomogeneous.mul, IsHomogeneous.sum]
  -- The substitution `X i ↦ T (e i)` sends the minor to zero.
  let ψ : MvPolynomial (Fin n) k →ₐ[k] k[T;T⁻¹] :=
    AddMonoidAlgebra.mapDomainAlgHom k k (Finsupp.weight e)
  have hψ_X (i : Fin n) : ψ (X i) = T (e i) := by
    simp [ψ, MvPolynomial.X, ← single_eq_monomial, Finsupp.weight_single]
  have h_subst : ψ.mapMatrix y =
      diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C := by
    ext i j
    simp [y, mul_apply, diagonal_apply, hψ_X, LaurentPolynomial.algebraMap_apply]
  have h_zero : ψ (powMinor y m a) = 0 := by rw [map_powMinor, h_subst, h_vanish a]
  -- The monomials of the minor have one degree `≤ (n + 1) ^ 2`, so by freeness the substitution
  -- keeps them apart.
  have h_hom : (powMinor y m a).IsHomogeneous (∑ i : Fin m, (i : ℕ)) := by
    -- In the Leibniz formula each product `∏ i, (y ^ i) (a (σ i))` has degree `∑ i, i`.
    rw [powMinor, det_apply']
    refine IsHomogeneous.sum (h := fun σ _ ↦ ?_)
    rw [← map_intCast (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)]
    exact (IsHomogeneous.prod (h := fun (i : Fin m) _ ↦ hy i (a (σ i)).fst (a (σ i)).snd)).C_mul _
  have h_deg : ∑ i : Fin m, (i : ℕ) ≤ (n + 1) ^ 2 := by
    grw [isLt, ← hm_le]
    simp [sq]
  have h_inj : Set.InjOn (Finsupp.weight e) (powMinor y m a).support :=
    (he (∑ i : Fin m, (i : ℕ)) h_deg).mono
      ((homogeneousSubmodule_eq_finsupp_supported (Fin n) k (∑ i : Fin m, (i : ℕ))).le h_hom)
  -- As `ψ` is injective on the monomials of the minor, the minor is zero.
  have h_support : (ψ (powMinor y m a)).coeff.support =
      (powMinor y m a).support.image (Finsupp.weight e) :=
    Finsupp.mapDomain_support_of_injOn _ h_inj
  rw [h_zero] at h_support
  simpa using h_support.symm

/-- Let the weights `e : Fin n → ℤ` be free (`HasNoSmallRelations e`: distinct exponent vectors of
one total degree at most `(n + 1) ^ 2` have distinct weights `∑ i, α i * e i`), let `c : N → Fin n`
be onto, let `x` be an invertible matrix over `k`, let `m ≤ n + 1`, and let `y` be the product, over
the Laurent polynomials `k[T;T⁻¹]`, of the diagonal matrix with entries `T (e (c a))` and `x`.
Suppose every `powMinor y m a` vanishes, where `powMinor y m a` is the `m × m` minor at rows
`a 0, …, a (m - 1)` of the matrix with rows indexed by `N × N` whose column `j < m` lists the
entries of `y ^ j`. Then `n < m`, and for `a ≠ b` with `c a = c b` the inverse `x⁻¹` has entry `0`
at `(a, b)` and equal entries at `(a, a)` and `(b, b)`. -/
lemma HasNoSmallRelations.inv_scalar_on_blocks {c : N → Fin n} (he : HasNoSmallRelations e)
    (hc : Surjective c) {x : GL N k} (hm_le : m ≤ n + 1)
    (h_vanish : ∀ a : Fin m → N × N,
      powMinor (diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C) m a = 0) :
    n < m ∧
      ∀ {a b : N}, c a = c b → a ≠ b → x⁻¹ a b = 0 ∧ x⁻¹ a a = x⁻¹ b b := by
  -- Replace `T (e i)` by variables `X i`. The minors still vanish, so a factor `p` of the
  -- characteristic polynomial of the resulting matrix `y` has degree `< m` and kills `y`.
  -- Its constant term is divisible by every `X i`, which forces the degree `n` and the monomial
  -- `∏ i, X i`; the coefficient of this monomial in `p(y) x⁻¹ = 0` gives the entries of `x⁻¹`.
  let y : Matrix N N (MvPolynomial (Fin n) k) :=
    diagonal (X ∘ c) * (x : Matrix N N k).map MvPolynomial.C
  obtain ⟨p, q, hq, hp_deg, hp_root⟩ :=
    exists_factor_charpoly y (powMinor_diagonal_X_mul_eq_zero he hm_le h_vanish)
  -- As `det y ≠ 0`, the constant term of `p` contains a monomial `α`.
  have h_det : y.det ≠ 0 := by simpa [y, prod_eq_zero_iff] using (x.map _).det_ne_zero
  obtain ⟨hp_const, hq_const⟩ : p.coeff 0 ≠ 0 ∧ q.coeff 0 ≠ 0 := by
    simpa [det_eq_sign_charpoly_coeff, hq] using h_det
  obtain ⟨α, hα⟩ := ne_zero_iff.mp hp_const
  -- In its own variable and the `X i` together, `y.charpoly` has total degree at most `card N`,
  -- its degree in its own variable.
  have h_total : ((optionEquivLeft k (Fin n)).symm y.charpoly).totalDegree ≤ card N := by
    simp [charpoly, det_apply, y, charmatrix, diagonal_apply, apply_ite]
    -- In the Leibniz formula each of the `card N` factors has total degree at most one.
    show MvPolynomial.totalDegree (∑ σ : Equiv.Perm N, Equiv.Perm.sign σ • ∏ i : N,
        ((if σ i = i then MvPolynomial.X none else 0) -
          MvPolynomial.X (some (c (σ i))) * MvPolynomial.C ((x : Matrix N N k) (σ i) i))) ≤ card N
    grw (transparency := .default) [totalDegree_finsetSum, totalDegree_smul_le,
      totalDegree_finsetProd, totalDegree_sub, totalDegree_mul]
    simp [ite_apply, apply_ite]
  set Φ : (MvPolynomial (Fin n) k)[X] ≃ₐ[k] MvPolynomial (Option (Fin n)) k :=
    (optionEquivLeft k (Fin n)).symm with hΦ
  have hp_ne : Φ p ≠ 0 := by aesop
  have hq_ne : Φ q ≠ 0 := by aesop
  -- Total degrees add, that of `α` is at most that of `p`, and that of `q` is at least
  -- `q.natDegree`; so `α` has degree at most `p.natDegree`.
  have hα_p : ∑ i, α i ≤ (Φ p).totalDegree := calc
    ∑ i, α i ≤ (p.coeff 0).totalDegree := by
      simpa [α.sum_fintype] using le_totalDegree (mem_support_iff.mpr hα)
    _ ≤ (Φ p).totalDegree := by
      simpa [hΦ] using totalDegree_coeff_optionEquivLeft_le (p := Φ p) (i := 0)
  have hq_le : q.natDegree ≤ (Φ q).totalDegree := by
    simpa [hΦ, ← natDegree_optionEquivLeft] using degreeOf_le_totalDegree (Φ q) none
  have hα_le : ∑ i, α i ≤ p.natDegree := by
    have h_add : (Φ p).totalDegree + (Φ q).totalDegree ≤ p.natDegree + q.natDegree := by
      rw [← totalDegree_mul_of_isDomain hp_ne hq_ne, ← map_mul, ← hq]
      grw [h_total, ← y.charpoly_natDegree_eq_dim, hq, natDegree_mul_le]
    lia
  -- Write `0 = p(y) = y * (r(y) * y + p₁) + p₀` with `r = p.divX.divX`. Row `a` of `y` is
  -- divisible by `X (c a)`, so `p₀` is, and every variable occurs in `α`.
  have hp_split : p = Polynomial.X * (p.divX.divX * Polynomial.X + Polynomial.C (p.divX.coeff 0)) +
      Polynomial.C (p.coeff 0) := by rw [p.divX.divX_mul_X_add, p.X_mul_divX_add]
  have hα_pos : 1 ≤ ⇑α := by
    refine hc.forall.mpr fun a ↦ Nat.pos_of_ne_zero fun hα_zero ↦ hα ?_
    -- If `α` missed the variable `X (c a)`, only `p₀` would contribute to the coefficient of `α`.
    have h_coeff : ((p.aeval y) a a).coeff α = 0 := by simp [hp_root]
    rw [hp_split] at h_coeff
    simpa [y, algebraMap, comp_def, mul_assoc, coeff_X_mul', hα_zero] using h_coeff
  -- Now `n ≤ ∑ i, α i ≤ p.natDegree < m ≤ n + 1`, so each variable occurs once.
  have h_card : n ≤ ∑ i, α i := by simpa using sum_mono hα_pos
  have hα_one : ⇑α = 1 := by
    by_contra h_ne
    have : n < ∑ i, α i := by simpa using sum_strictMono (hα_pos.lt_of_ne' h_ne)
    lia
  refine ⟨by lia, fun {a b} hab hne ↦ ?_⟩
  -- The entry `(a, b)` of `y * r(y) * y * x⁻¹` is divisible by `X (c a) * X (c b)`, so it does not
  -- contain `α` if `c a = c b`; the term `y * p₁ * x⁻¹` is diagonal and depends only on `c a`;
  -- the last term is `p₀ * x⁻¹`, and `α` occurs in `p₀`.
  have h_entry (a b : N) : ((p.aeval y * (x : Matrix N N k)⁻¹.map MvPolynomial.C :
      Matrix N N (MvPolynomial (Fin n) k)) a b).coeff α = 0 := by simp [hp_root]
  rw [hp_split] at h_entry
  -- Two passes normalize the coefficient equation (they use `mul_assoc` in opposite directions);
  -- its normal form is unreadable, so the three entries used are stated just below.
  simp [y, add_mul, mul_add, algebraMap, map_add, comp_def, mul_assoc, coeff_X_mul'] at h_entry
  simp [← mul_assoc, coeff_mul_X', mul_comm (p.coeff _), hα_one] at h_entry
  have h_ab : (x : Matrix N N k)⁻¹ a b = 0 ∨ (p.coeff 0).coeff α = 0 := by
    simpa [hab, hne] using h_entry a b
  have h_diag (a' : N) (ha' : c a' = c b) : (MvPolynomial.X (c b) * p.coeff 1).coeff α +
      (x : Matrix N N k)⁻¹ a' a' * (p.coeff 0).coeff α = 0 := by
    simpa [ha'] using h_entry a' a'
  rw [Matrix.coe_units_inv]
  exact ⟨h_ab.resolve_right hα,
    mul_right_cancel₀ hα (by linear_combination h_diag a hab - h_diag b rfl)⟩

/-- Let the weights `e : Fin n → ℤ` be free, let `c : N → Fin n` be onto, let `x` be an invertible
matrix over `k` and let `m ≤ n + 1`. If all minors `powMinor` of order `m` of the product of the
diagonal matrix with entries `T (e (c a))` and `x` over `k[T;T⁻¹]` vanish, then `n < m`. -/
private lemma HasNoSmallRelations.lt_of_powMinor_eq_zero {c : N → Fin n}
    (he : HasNoSmallRelations e) (hc : Surjective c) {x : GL N k} (hm_le : m ≤ n + 1)
    (h_vanish : ∀ a : Fin m → N × N,
      powMinor (diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C) m a = 0) :
    n < m :=
  (he.inv_scalar_on_blocks hc hm_le h_vanish).left

/-- Let the weights `e : Fin n → ℤ` be free, let `c : N → Fin n` be onto, let `x` be an invertible
matrix over `k` and let `m ≤ n + 1`. If all minors `powMinor` of order `m` of the product of the
diagonal matrix with entries `T (e (c a))` and `x` over `k[T;T⁻¹]` vanish, then for `a ≠ b` with
`c a = c b` the inverse `x⁻¹` has entry `0` at `(a, b)` and equal entries at `(a, a)` and `(b, b)`.
-/
private lemma HasNoSmallRelations.inv_apply_eq_zero_and_eq_of_powMinor_eq_zero {c : N → Fin n}
    (he : HasNoSmallRelations e) (hc : Surjective c) {x : GL N k} (hm_le : m ≤ n + 1)
    (h_vanish : ∀ a : Fin m → N × N,
      powMinor (diagonal (T ∘ e ∘ c) * (x : Matrix N N k).map LaurentPolynomial.C) m a = 0)
    {a b : N} (hab : c a = c b) (hne : a ≠ b) : x⁻¹ a b = 0 ∧ x⁻¹ a a = x⁻¹ b b :=
  (he.inv_scalar_on_blocks hc hm_le h_vanish).2 hab hne

/-- If a nonzero polynomial `p` of degree less than `m` kills the matrix `M` over `K`, then all
minors `powMinor (φ M) m a` vanish, for any `K`-algebra map `φ` into the matrices over `k`. -/
private lemma powMinor_eq_zero_of_aeval_eq_zero (φ : Matrix N N K →ₐ[K] Matrix N N k)
    {M : Matrix N N K} {p : K[X]} (hp : p ≠ 0) (h_root : p.aeval M = 0)
    (h_deg : p.natDegree < m) : powMinor (φ M) m = 0 := by
  -- The coefficients of `p` give a relation among the first `m` powers of `φ M`.
  have h_sum : ∑ i : Fin m, p.coeff i • φ M ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ p.coeff i • φ M ^ i), ← aeval_eq_sum_range' h_deg,
      aeval_algHom_apply, h_root, map_zero]
  have h_dep : ¬LinearIndependent K fun i : Fin m ↦ uncurry (φ M ^ (i : ℕ)) := by
    refine not_linearIndependent_iff.mpr
      ⟨fun i ↦ p.coeff i, funext fun ⟨a, b⟩ ↦ ?_, ⟨p.natDegree, h_deg⟩, by simpa using hp⟩
    simpa [uncurry, Matrix.sum_apply] using congrFun₂ h_sum a b
  exact funext (det_eval_eq_zero_iff_not_linearIndependent.mpr fun h_ind ↦
    h_dep (h_ind.restrict_scalars' K))

/-- Let `N` have `n ≥ 1` elements and let a monic polynomial `P` of degree `n` kill the matrix `M`
over `K`. If some minor `powMinor (φ M) n a` is nonzero, for a `K`-algebra map `φ` into the
matrices over `k`, then `P` is the characteristic polynomial of `M`: otherwise `M.charpoly - P`
would be a nonzero polynomial of degree less than `n` that kills `M`. -/
private lemma charpoly_eq_of_powMinor_ne_zero [NeZero n] (φ : Matrix N N K →ₐ[K] Matrix N N k)
    (hN : card N = n) {M : Matrix N N K} {P : K[X]} (h_root : P.aeval M = 0)
    (h_monic : P.IsMonicOfDegree n) (h_minor : powMinor (φ M) n ≠ 0) : M.charpoly = P := by
  have h_char : M.charpoly.IsMonicOfDegree n :=
    ⟨by rw [charpoly_natDegree_eq_dim, hN], charpoly_monic M⟩
  by_contra hne
  have h_sub_root : (M.charpoly - P).aeval M = 0 := by simp [h_root, aeval_self_charpoly]
  exact h_minor (powMinor_eq_zero_of_aeval_eq_zero φ (sub_ne_zero.mpr hne) h_sub_root
    (h_char.natDegree_sub_lt NeZero.out h_monic))

/-- Free weights `e : Fin n → ℤ` are pairwise distinct: apply freeness to the exponent vectors of
degree one. -/
private lemma HasNoSmallRelations.injective (he : HasNoSmallRelations e) : e.Injective := by
  intro i j h_eq
  have h_deg (i : Fin n) : Finsupp.single i 1 ∈ {α : Fin n →₀ ℕ | Finsupp.degree α = 1} := by simp
  exact Finsupp.single_left_injective one_ne_zero
    (he 1 (Nat.one_le_pow 2 (n + 1) n.succ_pos) (h_deg i) (h_deg j)
      (by simpa [Finsupp.weight_single] using h_eq))

/-- Let `e : Fin n → ℤ` be injective, `κ : N → ℤ` and `l : Fin n → N` with `κ (l i) = e i`. If all
minors of order `n + 1` of the first `n + 1` powers of the diagonal matrix with entries `T (κ j)`
vanish, then every `κ j` is one of the `e i`: otherwise the minor at the diagonal places
`j, l 0, …, l (n - 1)` would be a Vandermonde determinant of distinct monomials. -/
private lemma exists_eq_of_powMinor_diagonal_eq_zero (he_inj : e.Injective) {κ : N → ℤ}
    {l : Fin n → N} (hl : ∀ i : Fin n, κ (l i) = e i)
    (h_minor : ∀ a : Fin (n + 1) → N × N,
      powMinor (diagonal (T ∘ κ) : Matrix N N k[T;T⁻¹]) (n + 1) a = 0)
    (j : N) : ∃ i : Fin n, e i = κ j := by
  let a : Fin (n + 1) → N := cons j l
  obtain ⟨i, i', h_T_eq, h_ne⟩ : ∃ i i', (T (κ (a i)) : k[T;T⁻¹]) = T (κ (a i')) ∧ i ≠ i' := by
    apply det_vandermonde_eq_zero_iff.mp
    simpa [powMinor, diagonal_pow, flip_def, uncurry, vandermonde, comp_def] using
      h_minor (Function.diag ∘ a)
  -- `T` is unfolded to compare monomials; `single_eq_C_mul_T` would fold it back, a loop.
  have hκ_eq : κ (a i) = κ (a i') := by
    simpa [T, AddMonoidAlgebra.single_inj, -single_eq_C_mul_T] using h_T_eq
  -- The equal weights are at `j` and some `l i`, or at two `l i`, which `e` injective rules out.
  cases i using Fin.cases <;> cases i' using Fin.cases
  case zero.zero => exact absurd rfl h_ne
  case zero.succ i' => exact ⟨i', by simpa [a, hl] using hκ_eq.symm⟩
  case succ.zero i => exact ⟨i, by simpa [a, hl] using hκ_eq⟩
  case succ.succ i i' =>
    have h_e_eq : e i = e i' := by simpa [a, hl] using hκ_eq
    exact absurd (congrArg Fin.succ (he_inj h_e_eq)) h_ne

/-- Let `Q` be an invertible matrix over `k`, let `φ` send a matrix `M` over `K` to `Q * M * Q⁻¹`
over `k`, and let the `K`-subspace `V` contain every diagonal matrix. Then the matrices `φ x`,
`x ∈ V`, do not all have entry `0` at `(a, b)` and equal entries at `(a, a)` and `(b, b)`: for the
diagonal units `Eₜₜ` this would make each `Q a t * Q⁻¹ t a` zero, while their sum over `t` is
`1`. -/
private lemma not_forall_conj_entries_of_diagonal_mem (Q : GL N k)
    {φ : Matrix N N K →ₐ[K] Matrix N N k}
    (hφ : ∀ M : Matrix N N K,
      φ M = (Q : Matrix N N k) * (M.map (algebraMap K k) * (Q : Matrix N N k)⁻¹))
    {V : Submodule K (Matrix N N K)} (h_diag : ∀ v : N → K, diagonal v ∈ V) (a b : N) :
    ¬∀ x ∈ V, φ x a b = 0 ∧ φ x a a = φ x b b := by
  intro h_block
  have h_unit (t : N) : Q a t * (Q : Matrix N N k)⁻¹ t a = 0 := by
    obtain ⟨h_off, h_diag_eq⟩ := h_block (diagonal (Pi.single t 1)) (h_diag (Pi.single t 1))
    have h_off' : (Q : Matrix N N k) a t = 0 ∨ (Q : Matrix N N k)⁻¹ t b = 0 := by
      simpa [hφ, mul_apply, diagonal, apply_ite, Pi.single_apply] using h_off
    have h_diag' : (Q : Matrix N N k) a t * (Q : Matrix N N k)⁻¹ t a =
        (Q : Matrix N N k) b t * (Q : Matrix N N k)⁻¹ t b := by
      simpa [hφ, mul_apply, diagonal, apply_ite, Pi.single_apply] using h_diag_eq
    rcases h_off' with h_Q | h_Qinv
    · rw [h_Q, zero_mul]
    · rw [h_diag', h_Qinv, mul_zero]
  simpa [mul_apply, h_unit] using congrFun₂ Q.val_inv a a

/-- Let `E` be a number field inside `Ω` (`EmbeddedNumberField E`), and let `p` be a property of the
elements of `Gal(Ω/E)`. If every nonempty open set `V` contains a nonempty open set on which `p`
holds, then `p` holds at the Frobenius elements of most Frobenius data. -/
private lemma eventually_mostFrobenii_of_open {E : Type} [Field E] [EmbeddedNumberField E]
    {p : Gal(Ω/E) → Prop}
    (h : ∀ V : Set Gal(Ω/E), IsOpen V → V.Nonempty →
      ∃ O ⊆ V, IsOpen O ∧ O.Nonempty ∧ ∀ g ∈ O, p g) :
    ∀ᶠ y : FrobeniusDatum E in mostFrobenii E, p y.frob := by
  intro V hV hV_ne
  obtain ⟨O, hOV, hO, hO_ne, h_O⟩ := h V hV hV_ne
  refine ⟨O, hOV, hO, hO_ne, .of_forall ?_⟩
  rintro - - s - - - hs_O
  exact h_O s hs_O

/-- Let `e : Fin n → ℤ` be injective and let every `e i` be a value of `κ : N → ℤ`. If all minors
of order `n + 1` of the powers of `diagonal (T ∘ κ)` vanish, then `κ = e ∘ c` for an onto `c`. -/
private lemma exists_surjective_comp_eq_of_powMinor_diagonal_eq_zero (he_inj : e.Injective)
    {κ : N → ℤ} (hκ : ∀ i : Fin n, e i ∈ Set.range κ)
    (h_minor : ∀ a : Fin (n + 1) → N × N,
      powMinor (diagonal (T ∘ κ) : Matrix N N k[T;T⁻¹]) (n + 1) a = 0) :
    ∃ c : N → Fin n, Surjective c ∧ e ∘ c = κ := by
  choose l hl using hκ
  choose c hc using exists_eq_of_powMinor_diagonal_eq_zero he_inj hl h_minor
  exact ⟨c, fun i ↦ ⟨l i, he_inj ((hc (l i)).trans (hl i))⟩, funext hc⟩

omit [Fintype N] [DecidableEq N] in
/-- The matrix of variables `X (i, j)`, evaluated at the entries of a matrix `M` over `k`, is
`M`. -/
private lemma mvPolynomialX_map_eval_uncurry (M : Matrix N N k) :
    (mvPolynomialX N N k).map (MvPolynomial.eval (uncurry M)) = M :=
  mvPolynomialX_map_eval₂ (RingHom.id k) M

omit [Fintype N] [DecidableEq N] in
/-- The matrix of variables `X (i, j)`, evaluated at the entries of a matrix `M` over a
`k`-algebra `S`, is `M`. -/
private lemma mvPolynomialX_map_aeval_uncurry {S : Type} [CommRing S] [Algebra k S]
    (M : Matrix N N S) : (mvPolynomialX N N k).map (MvPolynomial.aeval (uncurry M)) = M :=
  mvPolynomialX_map_eval₂ (algebraMap k S) M

/-- Let `E` be a number field inside `Ω`, a fixed algebraic closure of `ℚ`, let `r` be a continuous
representation of `Gal(Ω/E)` on `K ^ N`, and let `k` be a normed field over `K`. Suppose:
* the span of the image of `r` contains every diagonal matrix;
* for most Frobenius data `v` (the filter `mostFrobenii E`) the polynomial `P v` is monic of degree
  `n ≥ 1` and kills `r v.frob`;
* the free integers `e i` (`HasNoSmallRelations e`: distinct exponent vectors of one total degree at
  most `(n + 1) ^ 2` have distinct weights) all occur among the integers `κ j`;
* for an invertible matrix `Q` over `k`, every polynomial in the entries that vanishes at `Q * r g`
  for all `g` near `1` also vanishes at `diagonal (T ∘ κ) * Q` over `k[T;T⁻¹]`.

Then `N` has `n` elements and `P v` is the characteristic polynomial of `r v.frob` for most
Frobenius data `v`. -/
lemma card_eq_and_charpoly_eq [NeZero n] {E : Type} [Field E] [NumberField E] [Algebra E Ω]
    (r : Gal(Ω/E) →* GL N K) (hr : Continuous r)
    (h_span : ∀ v : N → K, diagonal v ∈ span K (Set.range fun g : Gal(Ω/E) ↦ (r g : Matrix N N K)))
    {P : FrobeniusDatum E → K[X]}
    (hP : ∀ᶠ v : FrobeniusDatum E in mostFrobenii E,
      (P v).aeval (r v.frob : Matrix N N K) = 0 ∧ (P v).IsMonicOfDegree n)
    (Q : GL N k) (κ : N → ℤ) (he : HasNoSmallRelations e) (hκ : ∀ i : Fin n, e i ∈ Set.range κ)
    (h_torus : ∀ h : MvPolynomial (N × N) k,
      (∀ᶠ g : Gal(Ω/E) in nhds 1,
        h.aeval ((Q : Matrix N N k) * (r g : Matrix N N K).map (algebraMap K k)).uncurry = 0) →
      h.aeval (diagonal (T ∘ κ) * (Q : Matrix N N k).map LaurentPolynomial.C).uncurry = 0) :
    Fintype.card N = n ∧
      ∀ᶠ v : FrobeniusDatum E in mostFrobenii E, (r v.frob : Matrix N N K).charpoly = P v := by
  -- Work with the conjugate `φ (r g) = Q * r g * Q⁻¹` over `k` and the minors of its powers.
  let φ : Matrix N N K →ₐ[K] Matrix N N k :=
    (MulSemiringAction.toAlgHom K (Matrix N N k) (toConjAct Q)).comp (ofId K k).mapMatrix
  have h_φ (M : Matrix N N K) :
      φ M = (Q : Matrix N N k) * (M.map (algebraMap K k) * (Q : Matrix N N k)⁻¹) := by
    simp [φ, units_smul_def, mul_assoc, ofId]
  let ρ (g : Gal(Ω/E)) : GL N k := Units.map φ (r g)
  have h_closed (m : ℕ) : IsClosed {g : Gal(Ω/E) | powMinor (φ (r g)) m = 0} := by
    refine isClosed_eq ?_ continuous_zero
    simp only [h_φ]
    fun_prop [flip]
  -- Minors that vanish near `x` vanish on the translate of the torus: apply `h_torus` to the
  -- polynomial `Y ↦ powMinor (Y * Q⁻¹ * ρ x) m a`.
  have h_near {m : ℕ} (x : Gal(Ω/E)) (h : ∀ᶠ g : Gal(Ω/E) in nhds x, powMinor (φ (r g)) m = 0)
      (a : Fin m → N × N) :
      powMinor (diagonal (T ∘ κ) * (ρ x : Matrix N N k).map LaurentPolynomial.C) m a = 0 := by
    set M : Matrix N N (MvPolynomial (N × N) k) :=
      mvPolynomialX N N k * ((Q⁻¹ * ρ x : GL N k) : Matrix N N k).map MvPolynomial.C
    rw [← map_mul_right_nhds_one x, eventually_map] at h
    have h_poly : (powMinor M m a).aeval
        (diagonal (T ∘ κ) * (Q : Matrix N N k).map LaurentPolynomial.C).uncurry = 0 :=
      h_torus (powMinor M m a) <| h.mono fun g hg ↦ by
        simpa [M, φ, ρ, mvPolynomialX_map_eval_uncurry, units_smul_def, mul_assoc, ofId,
          comp_def] using congrFun hg a
    simp only [M, map_powMinor, AlgHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_map, comp_def,
      mvPolynomialX_map_aeval_uncurry, MvPolynomial.aeval_C] at h_poly
    simpa [mul_assoc, ← Matrix.map_mul, LaurentPolynomial.algebraMap_apply, comp_def] using h_poly
  -- The minors of order `n + 1` vanish at most Frobenius elements, hence everywhere.
  have h_all (g : Gal(Ω/E)) : powMinor (φ (r g)) (n + 1) = 0 := by
    refine (h_closed (n + 1)).closure_subset (dense_of_mostFrobenii (hP.mono ?_) g)
    intro v ⟨h_root, h_monic⟩
    have h_deg : (P v).natDegree < n + 1 := by simp [h_monic.natDegree_eq]
    exact powMinor_eq_zero_of_aeval_eq_zero φ h_monic.ne_zero h_root h_deg
  have h_top (x : Gal(Ω/E)) : ∀ a : Fin (n + 1) → N × N,
      powMinor (diagonal (T ∘ κ) * (ρ x : Matrix N N k).map LaurentPolynomial.C) (n + 1) a = 0 :=
    h_near x (.of_forall h_all)
  -- The weights `κ` are exactly the `e i`: write `κ = e ∘ c` with `c` onto.
  obtain ⟨c, hc_surj, rfl⟩ := exists_surjective_comp_eq_of_powMinor_diagonal_eq_zero
    (HasNoSmallRelations.injective he) hκ fun a ↦ by simpa [ρ] using h_top 1 a
  -- If `c a = c b` with `a ≠ b`, then by
  -- `HasNoSmallRelations.inv_apply_eq_zero_and_eq_of_powMinor_eq_zero` all `φ (r g)`, and so all
  -- elements of their span, have entry `0` at `(a, b)` and equal entries at `(a, a)`, `(b, b)`.
  have hc_inj : Injective c := by
    intro a b hab
    by_contra hne
    refine not_forall_conj_entries_of_diagonal_mem Q h_φ h_span a b fun x hx ↦ ?_
    refine span_induction (p := fun x _ ↦ φ x a b = 0 ∧ φ x a a = φ x b b) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨g, rfl⟩
      simpa [ρ] using
        he.inv_apply_eq_zero_and_eq_of_powMinor_eq_zero hc_surj le_rfl (h_top g⁻¹) hab hne
    all_goals simp +contextual
  have hN : card N = n := by simpa using card_of_bijective ⟨hc_inj, hc_surj⟩
  -- The minors of order `n` do not all vanish on a nonempty open set `V`, since
  -- `HasNoSmallRelations.lt_of_powMinor_eq_zero` would give `n < n`; so `V` meets the open set
  -- where they do not.
  have h_most : ∀ᶠ v : FrobeniusDatum E in mostFrobenii E, powMinor (φ (r v.frob)) n ≠ 0 := by
    refine eventually_mostFrobenii_of_open (p := fun g ↦ powMinor (φ (r g)) n ≠ 0) ?_
    rintro V hV ⟨x, hx⟩
    set Z : Set Gal(Ω/E) := {g | powMinor (φ (r g)) n = 0}
    have hV_not_sub : ¬V ⊆ Z := fun h_sub ↦ lt_irrefl n <| he.lt_of_powMinor_eq_zero hc_surj
      n.le_succ (h_near x (mem_nhds_iff.mpr ⟨V, h_sub, hV, hx⟩))
    exact ⟨V \ Z, Set.sdiff_subset, hV.sdiff (h_closed n), Set.sdiff_nonempty.mpr hV_not_sub,
      fun _ ⟨_, hg_Z⟩ ↦ hg_Z⟩
  refine ⟨hN, ?_⟩
  filter_upwards [hP, h_most] with v ⟨h_root, h_monic⟩ hv
  exact charpoly_eq_of_powMinor_ne_zero φ hN h_root h_monic hv

end New
