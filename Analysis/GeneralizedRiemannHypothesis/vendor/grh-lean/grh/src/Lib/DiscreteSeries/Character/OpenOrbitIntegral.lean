import Lib.DiscreteSeries.Character.WeylCharacterFormula

/-!
# Orbital integrals of discrete series coefficients and Weyl characters of U(n)

This file begins the computation of the orbital integrals of the discrete series coefficient
`New.HCParam.dsCoeff l` of `G = U(diag ε)` over the compact torus. Here `l = 2λ` is the parameter,
and `ε` is implicit in its type. If `l` has a gap then, at a point `x` of the torus with
`diag ε * x` accretive (`A` accretive: `A + Aᴴ` positive definite), the orbital integral is, up to a
constant of modulus one, a multiple of Weyl's character of `U(n)` of highest weight `λ - ρ`, minus
an error given by an integral over the unitary matrices outside the open orbit `G B`. Here `B` is
the group of invertible matrices that are upper triangular for `l`, that is, `b i j = 0` whenever
`l j < l i`; they are lower triangular when the coordinates are listed with `λ` decreasing. If `o`
reverses the order of `l`, the error is small at `diag(t ^ o i)` for small `t = 2⁻¹ ^ s`, so a
Laurent polynomial that is a multiple of it has no monomial of low level.

## Main definitions and results

* `New.le_norm_weightMinors_twoPowDiagConj`: for unitary `u`, if `f` decreases along `l` by steps of
  at least `|m|` and `h ≤ |l i - l j|`, a lower bound for `New.weightMinors l` at `u* diag(2^f) u`
  by its value at `diag(2^f)` and the entry `u i j`.
* `New.Orbital.orbital_eq_char_sub_offOrbitIntegral`: the formula for the orbital integral described
  above, with the error `New.Orbital.offOrbitIntegral`.
* `New.Orbital.coeff_eq_zero_of_low_level`: if `l` has a gap and `o` reverses its order, a Laurent
  polynomial that is a multiple of this error has no monomial of low level, by the bound
  `New.Orbital.exists_norm_offOrbitIntegral_le`.

Notions from other files:
* `New.HCParam.HasGap`: `l = 2λ` has distinct entries of the parity of `card n - 1`, and those of
  `λ` with different signs `ε` differ by at least `h`.
* `New.paramAddRho`: The integer vector `λ + ρ`, for ρ the half sum of the roots positive for `l`.
* `New.HCParam.dsCoeff`: The function c_λ on complex matrices given by Flensted-Jensen's integral
  `New.HCParam.flenstedJensen`; on K = U(diag ε) ∩ U(n) it is m_Λ with Λ = λ + ρ − 2ρ_c.
* `New.diagTorus`: For a tuple t of complex numbers of modulus one, the diagonal matrix diag(t) as
  an element of U(diag ε); `New.diagTorusK x` is diag(x) as an element of `maxCompactU 1`, which is
  U(n).
* `New.Orbital.torusEval`: For a tuple x of unit complex numbers, the algebra homomorphism from
  Laurent polynomials to ℂ sending the monomial of exponent ν to ∏ x_a^{ν_a}.

## Relation to the literature

This is part of the known computation of the discrete series character on the compact Cartan
subgroup by orbital integrals, see `Lib.DiscreteSeries.Character.FormalDegree`.
-/

/-!
## Principal minors of conjugated diagonal matrices

Conventions: `New.weightMinors l g` is the product over `t ∈ ℤ` of the principal minors
`New.principalMinor` of `g` on `{i | t ≤ l i}`, those with `t ≤ 0` divided by `det g`.
-/

section SectorBound

open Matrix Finset Complex ComplexOrder

namespace New

variable {n : Type _} [Fintype n] [DecidableEq n] (u : GL n ℂ) (f : n → ℤ)

/-- The matrix `u* diag(2^f) u`. For unitary `u` it is a positive definite matrix with eigenvalues
`2 ^ (f i)`. -/
@[simp]
noncomputable abbrev twoPowDiagConj : Matrix n n ℂ :=
  (u : Matrix n n ℂ)ᴴ * diagonal (fun k : n ↦ (2 : ℂ) ^ f k) * u

/-- For every invertible `u`, the matrix `u* diag(2^f) u` is positive semidefinite. -/
lemma posSemidef_twoPowDiagConj : (twoPowDiagConj u f).PosSemidef := by
  simp [zpow_nonneg, PosSemidef.conjTranspose_mul_mul_same]

/-- The norms of the principal minors of `u* diag(2^f) u` increase with the exponents `f`. -/
lemma norm_principalMinor_twoPowDiagConj_mono {f g : n → ℤ} (hfg : f ≤ g) (p : n → Prop)
    [DecidablePred p] :
    ‖principalMinor (twoPowDiagConj u f) p‖ ≤ ‖principalMinor (twoPowDiagConj u g) p‖ := by
  have h_diff : (twoPowDiagConj u g - twoPowDiagConj u f).PosSemidef := by
    simp [← sub_mul, ← mul_sub, hfg _, PosSemidef.conjTranspose_mul_mul_same]
  exact norm_det_le_norm_det_of_posSemidef ((posSemidef_twoPowDiagConj u f).submatrix _)
    (h_diff.submatrix _)

/-- For unitary `u`, the determinant of `u* diag(2^f) u` is that of `diag(2^f)`. -/
lemma det_twoPowDiagConj (hu : uᴴ = u.val⁻¹) :
    (twoPowDiagConj u f).det = (twoPowDiagConj 1 f).det := by
  simp [hu, det_conj', -det_mul]

/-- For unitary `u`, the inverse of `u* diag(2^f) u` is `u* diag(2^(-f)) u`. -/
lemma inv_twoPowDiagConj (hu : uᴴ = u.val⁻¹) :
    (twoPowDiagConj u f)⁻¹ = twoPowDiagConj u (-f) :=
  inv_eq_left_inv (by simp [mul_assoc, hu, ← mul_assoc (diagonal _), zpow_ne_zero])

lemma det_twoPowDiagConj_ne_zero : (twoPowDiagConj u f).det ≠ 0 := by
  simp [GeneralLinearGroup.det_ne_zero, prod_eq_zero_iff, zpow_ne_zero]

/-- Let `u` be unitary, let `f a + |m| ≤ f c` whenever `l c < l a`, let `h ≤ |l i - l j|` and
`l j ≤ l i`, and let `t` exceed some value of `l`. The minor of `u* diag(2^f) u` on `{k | t ≤ l k}`
is at least that of `diag(2^f)`, times `|u i j|² 2^m` if this set separates `i` from `j` with
`l i - h < t ≤ l i`. -/
lemma norm_principalMinor_mul_gain_le (h : ℕ) (u : GL n ℂ) (l f : n → ℤ) (i j : n) (m : ℤ) {t : ℤ}
    (hu : uᴴ = u.val⁻¹) (hf : ∀ a c : n, l c < l a → f a + |m| ≤ f c)
    (h_gap : h ≤ |l i - l j|) (hij : l j ≤ l i) (ht : ∃ a : n, l a < t) :
    (‖principalMinor (twoPowDiagConj 1 f) (t ≤ l ·)‖ *
        if t ∈ Ioc (l i - h) (l i) then ‖u i j‖ ^ 2 * 2 ^ m else 1) ≤
      ‖principalMinor (twoPowDiagConj u f) (t ≤ l ·)‖ := by
  -- truncate `f` at its least value `f c` outside the minor; inside it `f ≤ f c - |m|`
  obtain ⟨c, hc⟩ := exists_min_image ({k | l k < t} : Finset n) f (ht.imp (by simp))
  have inside (k : n) : l c < l k → f k + |m| ≤ f c := hf k c
  let g : n → ℤ := f ⊓ fun _ : n ↦ f c
  -- `q` is `{j}` if `l i - h < t ≤ l i` and empty otherwise; `p` is the rest outside the minor
  let q (k : n) : Prop := t ∈ Ioc (l i - h) (l i) ∧ k = j
  let p (k : n) : Prop := l k < t ∧ ¬q k
  have gain : (if t ∈ Ioc (l i - h) (l i) then ‖u i j‖ ^ 2 * 2 ^ m else 1) ≤
      (∏ k : n, if q k then (2 : ℝ) ^ f c else 1) *
        ‖principalMinor (twoPowDiagConj u g)⁻¹ q‖ := by
    grw [inv_twoPowDiagConj u g hu, ← re_le_norm]
    split_ifs with hsep
    · -- the `(j, j)` entry of the inverse is at least its term `‖u i j‖ ^ 2 * 2 ^ (-g i)`,
      -- and `m ≤ f c - g i` because `i` lies inside the minor
      have h_entry : principalMinor (twoPowDiagConj u (-g)) (· = j) =
          ((∑ k : n, ‖u k j‖ ^ 2 * 2 ^ (-g k) : ℝ) : ℂ) := by
        simp [principalMinor, default, toSquareBlockProp, mul_apply, diagonal, ← conj_mul',
          mul_right_comm]
      have h_exp : m ≤ f c + -g i := by grind [Pi.inf_apply, inside i]
      simp only [q, hsep, true_and, Fintype.prod_ite_eq', h_entry, ofReal_re]
      grw [← single_le_sum (fun _ _ ↦ by positivity) (mem_univ i), mul_left_comm,
        ← zpow_add₀ two_ne_zero, ← zpow_le_zpow_right₀ one_le_two h_exp]
    · simp only [q, hsep, false_and, ite_false, prod_const_one, one_mul]
      simp [principalMinor]
  -- Jacobi: the minor of the inverse on `q` is the minor on the complement over the determinant.
  -- Fischer: split the complement into `p` and `{k | t ≤ l k}`. Then use `g ≤ f c` and `g ≤ f`.
  have jacobi : ‖principalMinor (twoPowDiagConj u g)⁻¹ q‖ ≤
      ‖principalMinor (twoPowDiagConj u fun _ ↦ f c) p‖ *
        ‖principalMinor (twoPowDiagConj u f) (t ≤ l ·)‖ / ‖(twoPowDiagConj 1 g).det‖ := by
    grw [jacobi_complementary_minor (det_twoPowDiagConj_ne_zero u g), norm_div,
      fischer_inequality (posSemidef_twoPowDiagConj u g) p (t ≤ l ·) (by grind) (by grind),
      norm_principalMinor_twoPowDiagConj_mono u (f := g) (g := fun _ ↦ f c) inf_le_right p,
      norm_principalMinor_twoPowDiagConj_mono u (f := g) (g := f) inf_le_left (t ≤ l ·),
      det_twoPowDiagConj u g hu]
  -- `u` is unitary, so the remaining factors are products of powers of `2`; they cancel index by
  -- index, as `g` is `f` inside the minor and `f c` outside
  have cancel : ‖principalMinor (twoPowDiagConj 1 f) (t ≤ l ·)‖ *
      (∏ k : n, if q k then (2 : ℝ) ^ f c else 1) *
      ‖principalMinor (twoPowDiagConj u fun _ ↦ f c) p‖ / ‖(twoPowDiagConj 1 g).det‖ = 1 :=
    calc _ = ∏ k : n, (if t ≤ l k then (2 : ℝ) ^ f k else 1) * (if q k then 2 ^ f c else 1) *
          (if p k then 2 ^ f c else 1) / 2 ^ g k := by
          simp [g, principalMinor_eq_det, ← diagonal_one, ← smul_eq_mul_diagonal, hu,
            ← diagonal_smul, div_eq_inv_mul, ← mul_assoc, ← prod_inv_distrib, ← prod_mul_distrib,
            sub_ite, apply_ite norm]
      _ = 1 := prod_eq_one (by grind [zpow_ne_zero, Pi.inf_apply])
  grw [gain, jacobi]
  linear_combination ‖principalMinor (twoPowDiagConj u f) (t ≤ l ·)‖ * cancel

/-- Let `u` be unitary, let `f a + |m| ≤ f c` whenever `l c < l a`, and let the natural number `h`
be at most `|l i - l j|`. Then `|m_l(D)| (|u i j|² 2^m) ^ h ≤ |m_l(u* D u)|`, where `D = diag(2^f)`
and `m_l = New.weightMinors l` is the product of principal minors of weight `l`. -/
lemma le_norm_weightMinors_twoPowDiagConj (h : ℕ) (u : GL n ℂ) (l f : n → ℤ) (i j : n) (m : ℤ)
    (hu : uᴴ = u.val⁻¹) (hf : ∀ a c : n, l c < l a → f a + |m| ≤ f c) (h_gap : h ≤ |l i - l j|) :
    ‖weightMinors l (twoPowDiagConj 1 f)‖ * (‖u i j‖ ^ 2 * 2 ^ m) ^ h ≤
      ‖weightMinors l (twoPowDiagConj u f)‖ := by
  -- `weightMinors l` is a power of the determinant times the minors on `{k | t ≤ l k}`. Each minor
  -- of `twoPowDiagConj u f` is at least that of `twoPowDiagConj 1 f`; for `l j ≤ l i`, the `h`
  -- minors with `l i - h < t ≤ l i` contain `i` but not `j`, and gain the factor
  -- `‖u i j‖ ^ 2 * 2 ^ m`.
  -- passing to inverses replaces `l`, `f` by `-l`, `-f` (`weightMinors_neg`)
  wlog hij : l j ≤ l i generalizing l f with h_case
  · have h_neg (v : GL n ℂ) (hv : vᴴ = v.val⁻¹) :
        weightMinors (-l) (twoPowDiagConj v (-f)) = weightMinors l (twoPowDiagConj v f) := by
      rw [weightMinors_neg (det_twoPowDiagConj_ne_zero v _), inv_twoPowDiagConj v _ hv, neg_neg]
    rw [← h_neg u hu, ← h_neg 1 (by simp)]
    exact h_case (-l) (-f) (fun a c hac ↦ by grind [hf c a (neg_lt_neg_iff.1 hac), Pi.neg_apply])
      (by grind [Pi.neg_apply]) (by grind [Pi.neg_apply])
  -- all values of `l` lie in `[l a, b]`
  obtain ⟨a, ha⟩ := exists_min_image univ l ⟨i, mem_univ i⟩
  obtain ⟨b, hb⟩ := Finite.exists_le l
  have card_eq : h = #(Ioc (l a) b ∩ Ioc (l i - h) (l i)) := by grind [Ioc_inter_Ioc, Int.card_Ioc]
  have expand (v : GL n ℂ) (hv : vᴴ = v.val⁻¹) :
      ‖weightMinors l (twoPowDiagConj v f)‖ = ‖(twoPowDiagConj 1 f).det ^ l a‖ *
        ∏ t ∈ Ioc (l a) b, ‖principalMinor (twoPowDiagConj v f) (t ≤ l ·)‖ := by
    simp (disch := simp [det_twoPowDiagConj v f hv, ha, hb, prod_eq_zero_iff, zpow_ne_zero]) only
      [weightMinors_eq_det_zpow_mul_prod _ (l a) b, det_twoPowDiagConj v f hv, norm_mul, norm_prod]
  -- expand both sides; the powers of the determinant agree, so compare the minors for each `t`
  rw [expand u hu, expand 1 (by simp), card_eq, ← prod_const, ← prod_ite_mem, mul_assoc,
    ← prod_mul_distrib]
  gcongr with t ht
  exact norm_principalMinor_mul_gain_le h u l f i j m hu hf h_gap hij ⟨a, (mem_Ioc.1 ht).1⟩

end New

end SectorBound

/-!
## The orbital integral as a Weyl character minus an off-orbit error

The level of an exponent `γ` for `o : n → ℤ` is `o ⬝ᵥ γ`.
-/

section OrbitalOpenOrbit

namespace New.Orbital

open Matrix MeasureTheory Finset Complex DiscreteSeries ComplexOrder Norms.L2Operator Filter
  AddMonoidAlgebra

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {l : HCParam (n := n) ε} {h : ℕ}

/-- For `l = 2λ` and `J = diag ε`, the integral of `m_{-(λ-ρ)}(kᴴ J k) / m_{-(λ+ρ)}(kᴴ A k)` over
the `k` in `U(n)` outside `New.openOrbit ε l` (the open orbit `G B`), for the Haar
measure of mass one, where `m` is `New.weightMinors`. -/
noncomputable def offOrbitIntegral (l : HCParam (n := n) ε) (A : Matrix n n ℂ) : ℂ :=
  ∫ k : USign (1 : n → ℤˣ) in {k : USign (1 : n → ℤˣ) | (k : Matrix n n ℂ) ∈ openOrbit ε l}ᶜ,
    weightMinors (-l.compactForm.lowestKType) ((k : Matrix n n ℂ)ᴴ * signMatrix ε * k) /
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * A * k)

omit [DecidableEq n] in
/-- For `l = 2λ` with a gap (see `HCParam.HasGap`), the weight
`-l.compactForm.lowestKType = -(λ - ρ)` is dominant for `U(n)` when the coordinates are listed with
`l` increasing: it is antitone along `l`, as `IsKDominant` asks with all signs `1`. -/
lemma isKDominant_neg_compactForm_lowestKType (hg : l.HasGap h) :
    IsKDominant 1 l (-l.compactForm.lowestKType) := by
  simpa [lowestKType_neg hg.signs_one] using hg.signs_one.neg.isKDominant_lowestKType

/-- The orbital integral as an integral over `G = U(diag ε)`: let `l = 2λ` have gap `h` (distinct
entries congruent to `card n - 1` mod 2, with `|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`), and let `x`
lie on the torus with `A = J x` accretive (`J = diag ε`). If the integrand
`m_{-(λ-ρ)}(gᴴ J g) / m_{-(λ+ρ)}(gᴴ A g)` is integrable, then `σ ∫_G c_λ(g⁻¹ x g) dg` equals its
integral over `G`. Here `ρ` is the half sum of roots positive for `l`, `m_w = weightMinors w` is the
product of principal minors of weight `w`, `c_λ = l.dsCoeff` is `g ↦ Ξ(a, a⁻¹g)` with `a` the
block-diagonal part of `g` and `Ξ` the normalised integral `flenstedJensen`, and
`σ = m_{-(λ-ρ) - Λ}(J)` with `Λ = l.lowestKType = λ + ρ - 2ρ_c`. -/
lemma sign_mul_orbital_eq_integral_weightMinors_div (hg : l.HasGap h) (x : n → Circle)
    (hA : (signMatrix ε * diagTorus ε x).IsAccretive)
    (h_int : Integrable fun g : USign ε ↦
      weightMinors (-l.compactForm.lowestKType) ((g : Matrix n n ℂ)ᴴ * signMatrix ε * g) /
        weightMinors (-paramAddRho l) ((g : Matrix n n ℂ)ᴴ * (signMatrix ε * diagTorus ε x) * g)) :
    weightMinors (-l.compactForm.lowestKType - l.lowestKType) (signMatrix ε) *
        ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε x * g :) =
      ∫ g : USign ε,
        weightMinors (-l.compactForm.lowestKType) ((g : Matrix n n ℂ)ᴴ * signMatrix ε * g) /
          weightMinors (-paramAddRho l)
            ((g : Matrix n n ℂ)ᴴ * (signMatrix ε * diagTorus ε x) * g) := by
  -- Expand `dsCoeff` as an integral over `K` and absorb `k` into `g` by invariance.
  let F (y : Matrix n n ℂ) : ℂ :=
    weightMinors (-l.compactForm.lowestKType) (yᴴ * signMatrix ε * y) /
      weightMinors (-paramAddRho l) (yᴴ * (signMatrix ε * diagTorus ε x) * y)
  let w (k : maxCompactU ε) : ℂ :=
    ofReal (‖weightMinors l.lowestKType k‖ ^ 2 / l.lowestKType.kTypeNormSq)
  have expand (g : USign ε) :
      weightMinors (-l.compactForm.lowestKType - l.lowestKType) (signMatrix ε) *
        l.dsCoeff (g⁻¹ * diagTorus ε x * g :) = ∫ k, w k * F (g * k : USign ε) ∂haarK ε := by
    have h_acc : ((signMatrix ε)⁻¹ * (g⁻¹ * diagTorus ε x * g :)).IsAccretive := by
      simpa [mul_assoc, U.inv_coe_eq_mul_conjTranspose_mul, IsHermitianInvolution.det_ne_zero] using
        hA.conjTranspose_mul_mul (k := g) (GeneralLinearGroup.det_ne_zero _)
    -- `dsCoeff` may be computed with any block diagonal `a` (here `J`) making `a⁻¹ * g` accretive
    rw [dsCoeff_eq_flenstedJensen hg (mem_blockDiagAlg_iff_commute.2 rfl) h_acc, flenstedJensen,
      ← integral_div, ← integral_const_mul]
    congr with k
    -- the numerator of `F (g * k)` is constant, as `(g * k)ᴴ J (g * k) = J`
    simp only [w, F, mem_U.1 (g * k).2]
    push_cast
    simp [U.inv_coe_eq_mul_conjTranspose_mul, mul_assoc, signMatrix, field, mul_conj', zpow_sub₀,
      prod_eq_zero_iff,
      GeneralLinearGroup.det_ne_zero]
  calc _ = ∫ g : USign ε, ∫ k, w k * F (g * k : USign ε) ∂haarK ε := by
        simp_rw [← integral_const_mul, expand]
    -- exchange the integrals; right translation by `k` preserves the measure of `G`
    _ = ∫ k, ∫ g : USign ε, w k * F g ∂volume ∂haarK ε :=
        integral_integral_skew_product (T := fun (k : maxCompactU ε) (g : USign ε) ↦ g * k)
          (f := fun z ↦ w z.1 * F z.2) (fun k ↦ map_mul_right_eq_self _ k.1)
          ((integrable_of_compactSpace (f := w)
            (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero]))).mul_prod h_int)
    -- `w` has integral one
    _ = ∫ g : USign ε, F g := by
        simp [-ofReal_pow, w, integral_complex_ofReal, (kTypeNormSq_pos _).ne',
          integral_const_mul, integral_mul_const, integral_div]

/-- Schur orthogonality for the coefficient `m_Λ = weightMinors Λ` on `U(n)`, where `l` has gap `h`
and `Λ = l.compactForm.lowestKType = λ - ρ` (`l.compactForm` is `l` with all signs `1`; this is not
the `Λ` of `dsCoeff`): for invertible `a` the integral of `m_Λ(u⁻¹ a) m_Λ(u)` is `N m_Λ(a)`, with
`N = ∫ |m_Λ(u)|² du` the number `Λ.kTypeNormSq`. -/
lemma integral_weightMinors_inv_mul_mul_weightMinors (hg : l.HasGap h) (a : Matrix n n ℂ)
    (ha : a.det ≠ 0) :
    ∫ u : maxCompactU (1 : n → ℤˣ),
        weightMinors l.compactForm.lowestKType ((u : Matrix n n ℂ)⁻¹ * a) *
          weightMinors l.compactForm.lowestKType (u : Matrix n n ℂ) ∂haarK 1 =
      l.compactForm.lowestKType.kTypeNormSq * weightMinors l.compactForm.lowestKType a := by
  have dom := isKDominant_neg_compactForm_lowestKType hg
  -- the function `g ↦ m_{-Λ}(a⁻¹ g)` is holomorphic of weight `-Λ`
  have h_hol : IsHolOfWeight 1 l (fun _ : Unit ↦ -l.compactForm.lowestKType)
      (fun g : Unit → USign 1 ↦ ∏ τ, weightMinors (-l.compactForm.lowestKType) (a⁻¹ * g τ)) 1 :=
    isHolOfWeight_weightMinors hg.injective a⁻¹ (fun _ ↦ dom) (by simpa)
  simpa [-ofReal_pow, weightMinors_unitary_inv, kTypeNormSq, weightMinors_neg, ha,
    GeneralLinearGroup.det_ne_zero, Matrix.mul_inv_rev] using
    h_hol.integral_mul_conj_weightMinors hg.injective dom h_hol.continuous

/-- Let `l = 2λ` have gap `h` (distinct entries congruent to `card n - 1` mod 2, with
`|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`), and let `x` be on the torus with `A = J x` accretive
(`J = diag ε`). Then the integral of `m_{-(λ-ρ)}(kᴴ J k) / m_{-(λ+ρ)}(kᴴ A k)` over `U(n)` (Haar
measure `haarK 1` of mass one) is `N · χ(x)`, where `χ` is the character of highest weight `λ - ρ`
and `N = ∫ |m_{λ-ρ}(k)|² dk` over `U(n)`. Here `m_w = weightMinors w` is the product over integers
`t` of the principal minor on `{i | t ≤ w i}`, each factor with `t ≤ 0` divided by the
determinant. -/
lemma kTypeNormSq_mul_kTypeChar_eq_integral (hg : l.HasGap h) (x : n → Circle)
    (hA : (signMatrix ε * diagTorus ε x).IsAccretive) :
    l.compactForm.lowestKType.kTypeNormSq * l.compactForm.lowestKType.kTypeChar (diagTorusK x) =
      ∫ k : maxCompactU (1 : n → ℤˣ),
        weightMinors (-l.compactForm.lowestKType) ((k : Matrix n n ℂ)ᴴ * signMatrix ε * k) /
          weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * (signMatrix ε * diagTorus ε x) * k)
        ∂haarK 1 := by
  -- Write the minors in `kTypeChar` as Flensted-Jensen integrals `∫ Φ (y, k) dk / N`.
  let K : Subgroup (USign (1 : n → ℤˣ)) := maxCompactU 1
  set Λ : HCParam (1 : n → ℤˣ) := l.compactForm.lowestKType
  set A : Matrix n n ℂ := signMatrix ε * diagTorus ε x
  let Φ (z : K × K) : ℂ :=
    weightMinors Λ (z.1⁻¹ * (signMatrix ε)⁻¹ * z.1 * z.2) * starRingEnd ℂ (weightMinors Λ z.2) /
      weightMinors (-paramAddRho l) ((z.2 : Matrix n n ℂ)ᴴ * (z.1⁻¹ * A * z.1) * z.2)
  have Φ_int : Integrable Φ ((haarK 1).prod (haarK 1)) := integrable_of_compactSpace <| by
    fun_prop (disch := simp (disch := simp [*, GeneralLinearGroup.det_ne_zero]) [A,
      maxCompactU.coe_inv, GeneralLinearGroup.det_ne_zero, IsHermitianInvolution.det_ne_zero])
  have expand (y : K) :
      weightMinors Λ (y⁻¹ * diagTorusK x * y).1 = (∫ k, Φ (y, k) ∂haarK 1) / Λ.kTypeNormSq := by
    -- split `y⁻¹ x y = a * z` with `a = y⁻¹ J⁻¹ y` and `z = y⁻¹ A y` accretive
    let a : Matrix n n ℂ := y⁻¹ * (signMatrix ε)⁻¹ * y
    have split : a⁻¹ * ((y⁻¹ * diagTorusK x * y : K) : Matrix n n ℂ) = y⁻¹ * A * y := by
      simp [a, A, diagTorus, mul_assoc, Matrix.mul_inv_rev, IsHermitianInvolution.det_ne_zero]
    have h_acc : (a⁻¹ * ((y⁻¹ * diagTorusK x * y : K) : Matrix n n ℂ)).IsAccretive := by
      rw [split]
      simp [maxCompactU.coe_inv, hA, GeneralLinearGroup.det_ne_zero]
    rw [← dsCoeff_of_mem_maxCompactU hg.signs_one (Subtype.prop _),
      dsCoeff_eq_flenstedJensen hg.signs_one (by simp) h_acc, split, flenstedJensen]
  -- After the substitution `(y, k) = (v * u, u⁻¹)` the denominator no longer depends on `u`,
  -- and the integral over `u` is a Schur orthogonality relation.
  have inner (v : K) : ∫ u, Φ (v * u, u⁻¹) ∂haarK 1 = Λ.kTypeNormSq *
      (weightMinors (-Λ) ((v : Matrix n n ℂ)ᴴ * signMatrix ε * v) /
        weightMinors (-paramAddRho l) ((v : Matrix n n ℂ)ᴴ * A * v)) := by
    let a : Matrix n n ℂ := (v : Matrix n n ℂ)⁻¹ * (signMatrix ε)⁻¹ * v
    have h_Φ (u : K) : Φ (v * u, u⁻¹) = weightMinors Λ ((u : Matrix n n ℂ)⁻¹ * a) *
        weightMinors Λ u / weightMinors (-paramAddRho l) ((v : Matrix n n ℂ)ᴴ * A * v) := by
      simp [Φ, a, weightMinors_unitary_inv, mul_assoc, ↓← maxCompactU.coe_inv,
        GeneralLinearGroup.det_ne_zero, Matrix.mul_inv_rev]
    simp [h_Φ, Λ, integral_weightMinors_inv_mul_mul_weightMinors hg, integral_div, a, mul_assoc,
      weightMinors_neg, mul_div_assoc (ofReal _), GeneralLinearGroup.det_ne_zero,
      IsHermitianInvolution.det_ne_zero, Matrix.mul_inv_rev, ↓← maxCompactU.coe_inv]
  -- the substitution is a shear followed by a swap, so it preserves the product measure
  have swap :
      ∫ y, ∫ k, Φ (y, k) ∂haarK 1 ∂haarK 1 = ∫ v, ∫ u, Φ (v * u, u⁻¹) ∂haarK 1 ∂haarK 1 :=
    (integral_integral Φ_int).trans (((measurePreserving_mul_prod_inv (haarK 1) (haarK 1)).comp
      Measure.measurePreserving_swap).fubini Φ_int).2.symm
  simp only [HCParam.kTypeChar, ContinuousMap.coe_mk, expand, integral_div, swap, inner]
  -- cancel the squared norm `N` from `N * ((N * ∫ …) / N / N)`
  have hN : (Λ.kTypeNormSq : ℂ) ≠ 0 := by simp [(kTypeNormSq_pos _).ne']
  rw [integral_const_mul, mul_div_cancel_left₀ _ hN, mul_div_cancel₀ _ hN]

/-- For injective `l`, a weight `w` antitone along `l` (`IsKDominant 1 l w`), an invertible `b`
upper triangular for `l`, and invertible `y`, `M`: replacing `y` by `y b` multiplies
`m_w(yᴴ M y)` by `|∏ k, b k k ^ w k| ^ 2`, where `m_w = weightMinors w`. -/
lemma weightMinors_conjTranspose_mul_mul_borel (hl : l.Injective) {w : n → ℤ}
    (hw : IsKDominant 1 l w) (y : GL n ℂ) {b M : Matrix n n ℂ} (hb : IsBorelMatrix l b)
    (hM_det : M.det ≠ 0) :
    weightMinors w (((y : Matrix n n ℂ) * b)ᴴ * M * (y * b)) =
      ‖diagChar w b‖ ^ 2 * weightMinors w ((y : Matrix n n ℂ)ᴴ * M * y) := by
  have hb' : IsBorelMatrix (-l) bᴴ := by simp_all [IsBorelMatrix, BlockTriangular]
  have h_conj : diagChar w bᴴ * diagChar w b = ‖diagChar w b‖ ^ 2 := by
    simp [diagChar, ↓← conj_mul']
  calc _ = diagChar w bᴴ * (weightMinors w ((y : Matrix n n ℂ)ᴴ * M * y) * diagChar w b) := by
        simp [mul_assoc bᴴ, ← mul_assoc _ (y : Matrix n n ℂ), hb, hb', hM_det, hb.2,
          GeneralLinearGroup.det_ne_zero, hw.weightMinors_oppBorel_mul (ε := 1) hl,
          hw.weightMinors_mul_borel (ε := 1) hl]
    _ = _ := by linear_combination weightMinors w ((y : Matrix n n ℂ)ᴴ * M * y) * h_conj

/-- For injective `l` and invertible `b` upper triangular for `l`, the quotient of
`diagChar w b = ∏ k, b k k ^ w k` at the weights `-l.compactForm.lowestKType` and `-paramAddRho l`
(these are `-(λ - ρ)` and `-(λ + ρ)` for a parameter `l = 2λ`) is its value at
`twoRho l ⊤ = 2ρ`, the sum of the roots that are positive for `l`. -/
lemma diagChar_div_diagChar_eq_twoRho (hl : l.Injective) {b : Matrix n n ℂ}
    (hb : IsBorelMatrix l b) :
    diagChar (-l.compactForm.lowestKType) b / diagChar (-paramAddRho l) b =
      diagChar (twoRho l ⊤) b := by
  simp only [diagChar, ← prod_div_distrib, ← zpow_sub₀ (hb.diag_ne_zero hl _)]
  simp [HCParam.lowestKType, twoRho, paramAddRho]

/-- The orbital integral is the part of Weyl's character over the open orbit. For `l = 2λ` of gap
`h` there is `σ` of modulus one such that, at every point `x` of the torus with `J x` accretive
(`J = diag ε`), `σ ∫_G c_λ(g⁻¹ x g) dg` is `N · χ(x)` minus `offOrbitIntegral l (J x)`. Here `c_λ`
is `l.dsCoeff`, `χ` is the character of `U(n)` of highest weight
`l.compactForm.lowestKType = λ - ρ`, and `N = ∫ |weightMinors (λ - ρ) k|² dk` over `U(n)`, with
`weightMinors ν` the product of principal minors of weight `ν`. Also, `offOrbitIntegral l A` is the
integral of `weightMinors_{-(λ-ρ)}(kᴴ J k) / weightMinors_{-(λ+ρ)}(kᴴ A k)` over the `k ∈ U(n)`
outside `openOrbit ε l`. -/
lemma orbital_eq_char_sub_offOrbitIntegral (hg : l.HasGap h) :
    ∃ σ : ℂ, ‖σ‖ = 1 ∧ ∀ x : n → Circle, (signMatrix ε * diagTorus ε x).IsAccretive →
      σ * ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε x * g :) =
        l.compactForm.lowestKType.kTypeNormSq * l.compactForm.lowestKType.kTypeChar (diagTorusK x) -
          offOrbitIntegral l (signMatrix ε * diagTorus ε x) := by
  -- Both sides are compared with integrals of `F y = m_{-Λ}(yᴴ J y) / m_{-μ}(yᴴ A y)`, where
  -- `J = signMatrix ε`, `A = J x`, `Λ = l.compactForm.lowestKType`, `μ = paramAddRho l`: over `G`
  -- it gives `σ` times the orbital integral, over `U(n)` it gives `Λ.kTypeNormSq * Λ.kTypeChar x`,
  -- and by `integral_eq_sub_setIntegral_compl_openOrbit` the two differ by `offOrbitIntegral`.
  refine ⟨weightMinors (-l.compactForm.lowestKType - l.lowestKType) (signMatrix ε),
    by simp [signMatrix, abs_unit_intCast], fun x hx ↦ ?_⟩
  let F (y : Matrix n n ℂ) : ℂ :=
    weightMinors (-l.compactForm.lowestKType) (yᴴ * signMatrix ε * y) /
      weightMinors (-paramAddRho l) (yᴴ * (signMatrix ε * diagTorus ε x) * y)
  -- Triangular `b` acts on both minors by a character; the quotient is that of `μ - Λ = 2ρ`.
  have F_mul (y : GL n ℂ) (b : Matrix n n ℂ) (hb : IsBorelMatrix l b) :
      F (y * b) = ‖diagChar (twoRho l ⊤) b‖ ^ 2 * F y := by
    unfold F
    rw [weightMinors_conjTranspose_mul_mul_borel hg.injective
        (isKDominant_neg_compactForm_lowestKType hg) y hb (IsHermitianInvolution.det_ne_zero _),
      weightMinors_conjTranspose_mul_mul_borel hg.injective hg.isKDominant_neg_paramAddRho y hb
        hx.det_ne_zero, ← diagChar_div_diagChar_eq_twoRho hg.injective hb]
    simp [div_pow, div_mul_div_comm]
  have F_cont : Continuous (F · : GL n ℂ → ℂ) := by
    -- both arguments are invertible, and the denominator is a minor of an accretive matrix
    unfold F
    fun_prop (disch := simp (disch := simp [*, GeneralLinearGroup.det_ne_zero])
      [GeneralLinearGroup.det_ne_zero, IsHermitianInvolution.det_ne_zero])
  obtain ⟨F_int, F_orbit⟩ : Integrable (fun g : USign ε ↦ F g) ∧ ∫ g : USign ε, F g =
      (∫ k : USign (1 : n → ℤˣ), F k) - offOrbitIntegral l (signMatrix ε * diagTorus ε x) :=
    integral_eq_sub_setIntegral_compl_openOrbit hg.injective ε
      (fun y b hb ↦ by simpa using F_mul y b hb) F_cont
  -- For the signs `1` the group `K` is all of `U(n)`, with the same measure.
  have h_meas : MeasurePreserving (maxCompactU (1 : n → ℤˣ)).subtype (haarK 1) volume :=
    MonoidHom.measurePreserving (by fun_prop) (by simp [mem_maxCompactU, Function.Surjective])
      (by simp)
  have K_eq_U : ∫ k : maxCompactU (1 : n → ℤˣ), F k ∂haarK 1 = ∫ k : USign (1 : n → ℤˣ), F k :=
    h_meas.hasLaw.integral_comp (F_cont.comp continuous_subtype_val).aestronglyMeasurable
  rw [sign_mul_orbital_eq_integral_weightMinors_div hg x hx F_int,
    kTypeNormSq_mul_kTypeChar_eq_integral hg x hx, F_orbit, K_eq_U]

attribute [local fun_prop] AnalyticAt.fun_zpow

/-- The integral `offOrbitIntegral l A` over the unitary matrices outside the open orbit is
complex analytic in the matrix `A` at every accretive `A` (one with `A + Aᴴ` positive definite). -/
lemma analyticAt_offOrbitIntegral {A : Matrix n n ℂ} (hA : A.IsAccretive) :
    AnalyticAt ℂ (offOrbitIntegral l) A := by
  refine (isAnalyticFamily_of_differentiable ?_).analyticAt_integral _
  -- the integrand is continuous in `k` and differentiable in `z`, as `z` near `A` is accretive
  filter_upwards [hA.setOf_mem_nhds] with z (hz : z.IsAccretive) k
  constructor <;> fun_prop (disch := simp [hz, GeneralLinearGroup.det_ne_zero,
    IsHermitianInvolution.det_ne_zero, IsAccretive.det_ne_zero])

/-- Let `P`, `Q` be Laurent polynomials with `P(x) = Q(x) * offOrbitIntegral l (J x)` at the points
`x` of the torus with `J x` accretive, where `J = signMatrix ε`, evaluation at `x` is `torusEval x`,
and `offOrbitIntegral l A` is the integral of `m_{-(λ-ρ)}(kᴴ J k) / m_{-(λ+ρ)}(kᴴ A k)` over the
`k ∈ U(n)` outside `openOrbit ε l`, with `l = 2λ`, `ρ` the half sum of roots positive for `l`, and
`m = weightMinors`. Then for real `z > 0` (written `0 < z` in the order of `ℂ`) and every integer
vector `f`, this identity holds at `x = ε * z ^ f`, by analytic continuation from `|z| = 1`. At that
point `J x = diag (z ^ f)`, and `weightMinors γ J` is the monomial of exponent `γ` at `ε`. -/
lemma eq_mul_offOrbitIntegral_of_pos {P Q : ℂ[n → ℤ]}
    (hP : ∀ x : n → Circle, (signMatrix ε * diagTorus ε x).IsAccretive →
      torusEval x P = torusEval x Q * offOrbitIntegral l (signMatrix ε * diagTorus ε x))
    (f : n → ℤ) {z : ℂ} (hz : 0 < z) :
    ∑ γ ∈ P.coeff.support, P.coeff γ * weightMinors γ (signMatrix ε) * z ^ (f ⬝ᵥ γ) =
      (∑ γ ∈ Q.coeff.support, Q.coeff γ * weightMinors γ (signMatrix ε) * z ^ (f ⬝ᵥ γ)) *
        offOrbitIntegral l (diagonal fun i : n ↦ z ^ f i) := by
  -- `T R z` is the value of `R` at `x = ε * z ^ f`, and `D z = signMatrix ε * x`
  let T (R : ℂ[n → ℤ]) (z : ℂ) : ℂ :=
    ∑ γ ∈ R.coeff.support, R.coeff γ * weightMinors γ (signMatrix ε) * z ^ (f ⬝ᵥ γ)
  let D (z : ℂ) : Matrix n n ℂ := diagonal (z ^ f ·)
  have D_acc {z : ℂ} (hz : 0 < z) : (D z).IsAccretive :=
    (PosDef.diagonal fun _ ↦ zpow_pos hz _).isAccretive
  have on_circle (θ : ℝ) (hθ : (D (circleMap 0 1 θ)).IsAccretive) : T P (circleMap 0 1 θ) =
      T Q (circleMap 0 1 θ) * offOrbitIntegral l (D (circleMap 0 1 θ)) := by
    let x : n → Circle := fun i ↦
      ⟨ε i * circleMap 0 1 θ ^ f i, by simp [Submonoid.unitSphere, abs_unit_intCast]⟩
    have hD : signMatrix ε * diagTorus ε x = D (circleMap 0 1 θ) := by
      simp [x, D, signMatrix, diagTorus, ← mul_assoc, ← Int.cast_mul]
    have eval_eq (R : ℂ[n → ℤ]) : torusEval x R = T R (circleMap 0 1 θ) := by
      simp [x, T, torusEval, signMatrix, dotProduct, lift_apply', mul_assoc, mul_zpow,
        prod_mul_distrib, Finsupp.sum, zpow_sum_of_ne_zero, _root_.zpow_mul]
    simpa only [eval_eq, hD] using hP x (by rwa [hD])
  have h_start : 0 < circleMap 0 1 0 := by simp [circleMap]
  have D_cont : ContinuousWithinAt (D ∘ circleMap 0 1) {0}ᶜ 0 := by fun_prop (disch := simp)
  have acc_near : ∀ᶠ θ : ℝ in nhdsWithin 0 {0}ᶜ, (D (circleMap 0 1 θ)).IsAccretive :=
    D_cont.tendsto.eventually (D_acc h_start).setOf_mem_nhds
  -- the circle tends to `1` without meeting it, as its derivative there is not zero
  have near_one : ∃ᶠ z : ℂ in nhdsWithin (circleMap 0 1 0) {circleMap 0 1 0}ᶜ,
      T P z = T Q z * offOrbitIntegral l (D z) :=
    ((hasDerivAt_circleMap 0 1 0).tendsto_nhdsNE (by simp)).frequently
      (acc_near.frequently.mono on_circle)
  have T_an (R : ℂ[n → ℤ]) : AnalyticOnNhd ℂ (T R) (Set.Ioi 0) := fun z (hz : 0 < z) ↦ by
    fun_prop (disch := simp [hz.ne'])
  have D_an {z : ℂ} (hz : 0 < z) : AnalyticAt ℂ D z :=
    ((diagonalLinearMap n ℂ ℂ).toContinuousLinearMap.analyticAt _).comp
      (f := fun z i ↦ z ^ f i) (.pi (by fun_prop (disch := simp [hz.ne'])))
  have rhs_an : AnalyticOnNhd ℂ (fun z ↦ T Q z * offOrbitIntegral l (D z)) (Set.Ioi 0) :=
    fun z hz ↦ (T_an Q z hz).mul ((analyticAt_offOrbitIntegral (D_acc hz)).comp (D_an hz))
  exact (T_an P).eqOn_of_preconnected_of_frequently_eq rhs_an (convex_Ioi _).isPreconnected
    h_start near_one hz

/-- For every parameter `l` and natural number `h` there is `r > 0` such that every unitary matrix
`k` outside the open orbit `openOrbit ε l` has an entry `k i j` between opposite signs
(`ε i ≠ ε j`) with `r |weightMinors (-Λ) (kᴴ J k)| < |k i j| ^ (2 h)`. Here `J = signMatrix ε` and
`Λ = l.compactForm.lowestKType`, so that the minor is the numerator of the integrand of
`offOrbitIntegral`. -/
lemma exists_entry_large_outside_orbit (l : HCParam (n := n) ε) (h : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ k : USign (1 : n → ℤˣ), (k : Matrix n n ℂ) ∉ openOrbit ε l →
      ∃ i j : n, ε i ≠ ε j ∧
        r * ‖weightMinors (-l.compactForm.lowestKType) ((k : Matrix n n ℂ)ᴴ * signMatrix ε * k)‖ <
          ‖(k : Matrix n n ℂ) i j‖ ^ (2 * h) := by
  have compact : IsCompact {k : USign (1 : n → ℤˣ) | (k : Matrix n n ℂ) ∈ openOrbit ε l}ᶜ :=
    ((isOpen_openOrbit ε l).preimage (by fun_prop)).isClosed_compl.isCompact
  -- the strict inequality holds for `(r, k')` near `(0, k)`, so by compactness for small `r > 0`
  refine (compact.eventually_forall_of_forall_eventually fun k hk ↦ ?_).exists_gt (a := 0)
  -- a unitary matrix with no nonzero entry between opposite signs lies in `G`, hence in `G B`
  obtain ⟨i, j, hij, hne⟩ : ∃ i j : n, ε i ≠ ε j ∧ (k : Matrix n n ℂ) i j ≠ 0 := by
    by_contra! h_block
    rw [← mem_blockDiagAlg, mem_blockDiagAlg_iff_commute] at h_block
    have h_unitary : (k : Matrix n n ℂ)ᴴ * k = 1 := by simpa [U] using k.prop
    exact hk ⟨⟨k, by simp [U, h_block.right_comm, h_unitary]⟩, 1,
      by simp [IsBorelMatrix, blockTriangular_one]⟩
  -- at `r = 0` the left side vanishes and the right side does not
  refine (ContinuousAt.eventually_lt ?_ (by fun_prop) (by simp [hne])).mono
    fun _ h_lt ↦ ⟨i, j, hij, h_lt⟩
  fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero, IsHermitianInvolution.det_ne_zero])

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `l = 2λ` have gap `h`: its entries are distinct, of the parity of `card n - 1`, and those
with opposite signs `ε` differ by at least `2 h`. Let `o` strictly reverse the order of `l`. Then
for every integer vector `e`, as `s → ∞`, `offOrbitIntegral l A` is `O(2⁻¹ ^ (s L))` at
`A = diag(2⁻¹ ^ (s o + e))`, where `L = o ⬝ᵥ paramAddRho l + h` and `paramAddRho l = λ + ρ`. Here
`offOrbitIntegral l A` is the integral of `m_{-(λ-ρ)}(kᴴ J k) / m_{-(λ+ρ)}(kᴴ A k)` over the
`k ∈ U(n)` outside `New.openOrbit ε l`, with `J = diag ε` and `m = weightMinors`. -/
lemma exists_norm_offOrbitIntegral_le (hg : l.HasGap h) {o : n → ℤ}
    (ho : ∀ i j : n, l j < l i → o i < o j) (e : n → ℤ) :
    ∃ c : ℝ, ∀ᶠ s : ℕ in atTop, ‖offOrbitIntegral l (diagonal fun i : n ↦ 2⁻¹ ^ (s • o + e) i)‖ ≤
      c * 2⁻¹ ^ (s * (o ⬝ᵥ paramAddRho l + h)) := by
  obtain ⟨r, hr, large⟩ := exists_entry_large_outside_orbit l h
  obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ i : n, 2 * |e i| ≤ C := Finite.exists_le _
  refine ⟨2 ^ (C * h - e ⬝ᵥ paramAddRho l) / r, ?_⟩
  filter_upwards [eventually_gt_atTop C.toNat] with s hs
  set A : Matrix n n ℂ := diagonal fun i : n ↦ 2⁻¹ ^ (s • o + e) i
  set μ : n → ℤ := paramAddRho l with hμ
  -- the measure has mass at most one, so it is enough to bound the integrand at each `k`
  suffices h_point : ∀ k : USign (1 : n → ℤˣ), (k : Matrix n n ℂ) ∉ openOrbit ε l →
      ‖weightMinors (-l.compactForm.lowestKType) ((k : Matrix n n ℂ)ᴴ * signMatrix ε * k) /
          weightMinors (-μ) ((k : Matrix n n ℂ)ᴴ * A * k)‖ ≤
        2 ^ (C * h - e ⬝ᵥ μ) / r * 2⁻¹ ^ (s * (o ⬝ᵥ μ + h)) from
    (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) h_point).trans
      (mul_le_of_le_one_right (by positivity) measureReal_le_one)
  intro k hk
  obtain ⟨i, j, hij, entry⟩ := large k hk
  -- the entries of `s o` are at least `s` apart, and `e` changes each gap by at most `C`
  have steps (a c : n) (hac : (-μ) c < (-μ) a) : (-(s • o + e)) a + |s - C| ≤ (-(s • o + e)) c := by
    have o_lt : o c + 1 ≤ o a := ho c a (by simpa [hμ, hg.paramAddRho_lt_iff] using hac)
    have o_step : s * (o c + 1) ≤ s * o a := by gcongr
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, Int.nsmul_eq_mul]
    grind
  have apart : (h : ℤ) ≤ |(-μ) i - (-μ) j| := by grind [paramAddRho, hg.gap i j hij, Pi.neg_apply]
  have diag_eq : ‖weightMinors (-μ) (twoPowDiagConj 1 (-(s • o + e)))‖ =
      2 ^ (s * (o ⬝ᵥ μ) + e ⬝ᵥ μ) := by
    simp [dotProduct, zpow_add₀, _root_.zpow_mul, mul_zpow, prod_mul_distrib, zpow_sum_of_ne_zero,
      zpow_ne_zero]
  have denom : 2 ^ (s * (o ⬝ᵥ μ) + e ⬝ᵥ μ) * (‖(k : Matrix n n ℂ) i j‖ ^ 2 * 2 ^ (s - C)) ^ h ≤
      ‖weightMinors (-μ) ((k : Matrix n n ℂ)ᴴ * A * k)‖ := by
    simpa [A, ← diag_eq] using le_norm_weightMinors_twoPowDiagConj h k (-μ) (-(s • o + e))
      i j (s - C) (by simp [U.inv_coe_eq_mul_conjTranspose_mul]) steps apart
  -- `entry` bounds the numerator above and `denom` bounds the denominator below
  refine (norm_div _ _).trans_le (div_le_of_le_mul₀ (by positivity) (by positivity) ?_)
  calc ‖weightMinors (-l.compactForm.lowestKType) ((k : Matrix n n ℂ)ᴴ * signMatrix ε * k)‖
      ≤ ‖(k : Matrix n n ℂ) i j‖ ^ (2 * h) / r := (le_div_iff₀' hr).2 entry.le
    _ = 2 ^ (C * h - e ⬝ᵥ μ) / r * 2⁻¹ ^ (s * (o ⬝ᵥ μ + h)) *
          (2 ^ (s * (o ⬝ᵥ μ) + e ⬝ᵥ μ) * (‖(k : Matrix n n ℂ) i j‖ ^ 2 * 2 ^ (s - C)) ^ h) := by
        simp [field, pow_mul, mul_pow, div_pow, zpow_add₀, zpow_sub₀, _root_.zpow_mul]
    _ ≤ _ := by gcongr

/-- Let `l = 2λ` have gap `h`: its entries are distinct, congruent to `card n - 1` mod 2, and
`|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`. Let `P`, `Q` be Laurent polynomials with
`P(x) = Q(x) · offOrbitIntegral l (J x)` at every torus point `x` where `J x` is accretive
(`J = diag ε`); here `offOrbitIntegral l A` is the integral of
`m_{-(λ-ρ)}(kᴴ J k) / m_{-(λ+ρ)}(kᴴ A k)` over the `k ∈ U(n)` outside `New.openOrbit ε l`, with
`m = weightMinors`. If `o` strictly reverses the order of `l` (`l j < l i` implies `o i < o j`) and
`o ⬝ᵥ γ < o ⬝ᵥ paramAddRho l + o ⬝ᵥ β + h` for every exponent `β` of `Q` (`paramAddRho l = λ + ρ`),
then the coefficient of `x^γ` in `P` is zero. -/
lemma coeff_eq_zero_of_low_level (hg : l.HasGap h) {P Q : ℂ[n → ℤ]}
    (hP : ∀ x : n → Circle, (signMatrix ε * diagTorus ε x).IsAccretive →
      torusEval x P = torusEval x Q * offOrbitIntegral l (signMatrix ε * diagTorus ε x))
    {o : n → ℤ} (ho : ∀ i j : n, l j < l i → o i < o j) (γ : n → ℤ)
    (hQ : ∀ β : n → ℤ, Q.coeff β ≠ 0 → o ⬝ᵥ γ < o ⬝ᵥ paramAddRho l + o ⬝ᵥ β + h) :
    P.coeff γ = 0 := by
  -- Let `β` be an exponent of `P` of least level `o ⬝ᵥ β`, and put `x = ε * t ^ o * 2⁻¹ ^ e`. As
  -- `t → 0` the right side of the continued identity `hP` is of smaller order than
  -- `t ^ (o ⬝ᵥ β)`, so the part of `P` of least level vanishes at `ε * 2⁻¹ ^ e`, for every `e`.
  by_contra hγ
  obtain ⟨β, hβ, β_min⟩ : ∃ β ∈ P.coeff.support, ∀ δ ∈ P.coeff.support, o ⬝ᵥ β ≤ o ⬝ᵥ δ :=
    P.coeff.support.exists_min_image (o ⬝ᵥ ·) ⟨γ, by simpa⟩
  let L : ℤ := o ⬝ᵥ paramAddRho l + h
  -- `S e R m t` is the value of `t ^ (m - o ⬝ᵥ β) * R` at `x = ε * t ^ o * 2⁻¹ ^ e`
  let S (e : n → ℤ) (R : ℂ[n → ℤ]) (m : ℤ) (t : ℂ) : ℂ := ∑ γ ∈ R.coeff.support,
    R.coeff γ * weightMinors γ (signMatrix ε) * t ^ (o ⬝ᵥ γ - (o ⬝ᵥ β - m)) * 2⁻¹ ^ (e ⬝ᵥ γ)
  have lowest_zero (e : n → ℤ) : S e P 0 0 = 0 := by
    obtain ⟨c, decay⟩ := exists_norm_offOrbitIntegral_le hg ho e
    -- at `t = 2⁻¹ ^ s` the bound `O(t ^ L)` for `offOrbitIntegral` makes up for the shift by `L`
    have le_small : ∀ᶠ s : ℕ in atTop,
        ‖S e P 0 ((1 / 2) ^ s : ℝ)‖ ≤ ‖S e Q L ((1 / 2) ^ s : ℝ)‖ * c := by
      filter_upwards [decay] with s hs
      have S_eq (R : ℂ[n → ℤ]) (m : ℤ) : S e R m (2⁻¹ ^ s) = 2⁻¹ ^ (s * (m - o ⬝ᵥ β)) *
          ∑ γ ∈ R.coeff.support,
            R.coeff γ * weightMinors γ (signMatrix ε) * 2⁻¹ ^ ((s • o + e) ⬝ᵥ γ) := by
        -- the powers of `2⁻¹ ^ s` add up
        simp [S, mul_sum, smul_dotProduct, -nsmul_eq_mul, Int.nsmul_eq_mul, zpow_sub₀,
          _root_.zpow_mul, zpow_add₀]
        grind
      have eq_mul : S e P 0 (2⁻¹ ^ s) = S e Q L (2⁻¹ ^ s) / 2⁻¹ ^ (s * L) *
          offOrbitIntegral l (diagonal (2⁻¹ ^ (s • o + e) ·)) := by
        rw [S_eq, S_eq, eq_mul_offOrbitIntegral_of_pos hP _ (by simp)]
        simp [field, _root_.zpow_mul, zpow_sub₀]
      push_cast
      grw [one_div, eq_mul, norm_mul, hs]
      simp [L, field]
    -- `o ⬝ᵥ β` is the least level in `P`, and by `hQ` the levels in `Q` exceed `o ⬝ᵥ β - L`: both
    -- sums are polynomials in `t`, so the inequality passes to `t = 0`, where that of `Q` vanishes
    have closed : IsClosed {t : ℝ | ‖S e P 0 t‖ ≤ ‖S e Q L t‖ * c} := by
      refine isClosed_le ?_ ?_ <;> fun_prop (disch := grind)
    have Q_zero : S e Q L 0 = 0 := sum_eq_zero (by grind [_root_.zero_zpow_eq])
    simpa [Q_zero] using closed.mem_of_tendsto summable_geometric_two.tendsto_atTop_zero le_small
  -- the characters `e ↦ 2⁻¹ ^ (e ⬝ᵥ γ)` are distinct, hence independent, so `P.coeff β = 0`
  let χ (γ : n → ℤ) : Multiplicative (n → ℤ) →* ℂ :=
    { toFun e := 2⁻¹ ^ (e.toAdd ⬝ᵥ γ), map_one' := by simp, map_mul' := by simp [zpow_add₀] }
  have χ_inj : χ.Injective := fun a b hab ↦ funext fun i ↦ by
    simpa [χ] using congr_arg (fun φ ↦ ‖φ (.ofAdd (Pi.single i 1))‖) hab
  -- the surviving terms at `t = 0` are those of level `o ⬝ᵥ β`
  have sum_zero : ∑ γ ∈ P.coeff.support,
      (P.coeff γ * weightMinors γ (signMatrix ε) * 0 ^ (o ⬝ᵥ γ - o ⬝ᵥ β)) • ⇑(χ γ) = 0 :=
    funext fun e ↦ by simpa [S, χ] using lowest_zero e.toAdd
  have coeff_zero : P.coeff β * weightMinors β (signMatrix ε) = 0 := by
    simpa using linearIndependent_iff'.1 ((linearIndependent_monoidHom _ ℂ).comp χ χ_inj) _ _
      sum_zero β hβ
  simp [Finsupp.mem_support_iff.1 hβ, signMatrix, prod_eq_zero_iff, zpow_ne_zero] at coeff_zero

end New.Orbital

end OrbitalOpenOrbit
