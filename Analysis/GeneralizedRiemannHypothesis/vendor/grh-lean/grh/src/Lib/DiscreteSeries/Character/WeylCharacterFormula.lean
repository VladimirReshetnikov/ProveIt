import Lib.GLn.SchurModule.SchurOrthogonality
import Lib.General.LinearAlgebra.Eigenvalues

/-!
# Laurent polynomials on the torus and Weyl's character and dimension formulas

Let `ε : n → ℤˣ` be a family of signs and `K = New.maxCompactU ε` the group of unitary matrices in
the unitary group of `New.signMatrix ε`. Its Weyl group consists of the permutations `w` with
`ε ∘ w = ε`. Laurent polynomials are the elements of `ℂ[n → ℤ]`; they are evaluated on the diagonal
torus by `New.Orbital.torusEval`.

## Main definitions and results

* `New.HCParam.rootProd l r`: the product `∏ (x_a - x_b)` over the pairs with `r (ε a) (ε b)` and
  `l b < l a`, where `r` is `Eq` for the compact roots and `Ne` for the noncompact roots.
  `New.Orbital.rootProd_mem_leadingMonomials` finds its top monomial, whose exponent
  `New.HCParam.lowerCount l r a` counts such `b`.
* `New.Orbital.alternant`, `New.Orbital.IsWeylAntisymm`: the alternants `∑ sgn(w) x ^ (μ ∘ w)` over
  the Weyl group, and functions of the exponent that are antisymmetric.
* `New.HCParam.kTypeChar`: the average over conjugation of the matrix coefficient
  `New.weightMinors ν` (a product of principal minors), divided by `New.HCParam.kTypeNormSq ν`.
* `New.Orbital.weyl_character_kTypeChar`, `New.Orbital.weyl_denominator`: Weyl's character and
  denominator formulas for `K`. The first joins
  `New.Orbital.exists_kTypeChar_diagTorusK_eq_torusEval` (the character is a Laurent polynomial) and
  `New.Orbital.torusEval_rootProd_mul_kTypeChar_eq_alternant` (the formula).
* `New.weyl_dimension_formula`: Weyl's dimension formula for `U(n)`.
* `New.Variety.trace_weylRep`: Weyl's character formula at a tuple `g` of invertible matrices with
  distinct eigenvalues, reduced to the diagonal case `New.weyl_character` by conjugation.

Notions from other files:
* `New.HCParam ε`: integer vectors `n → ℤ`, used as weights and as doubled parameters `l = 2λ`.
* `New.HCParam.lowestKType`: the integer vector `Λ = λ + ρ - 2ρ_c` for a parameter `l = 2λ`, the
  highest weight of the lowest `K`-type. With all signs `1` one has `ρ_c = ρ`.
* `New.weylRep κ e`: the representation of `∏_τ GL(n_τ)` sending `g` to `∏_τ det(g_τ) ^ e_τ` times
  the Schur matrix `New.schur κ g`.

## Relation to the literature

Known result: Weyl character formula for U(n) and products of unitary groups. Here the formula for
`K` is deduced from the one for Schur modules at diagonal matrices (`New.weyl_character`): by
Schur's lemma, normalised means over conjugation of products of principal minors are traces of
twisted Schur modules. The dimension formula is obtained by a limit at 1, and the formula for
`∏_τ GL_a(ℂ)` at elements with distinct eigenvalues by diagonalisation. Source: H. Weyl, The
Classical Groups (1939), ch. VII; Fulton and Harris, Representation Theory (1991), Lectures 24-25.

See also `Lib.DiscreteSeries.Character.FormalDegree`.
-/

noncomputable section

namespace New.Orbital

/-!
## Laurent polynomials on the torus, Weyl denominators and alternants

`New.IsKDominant ε (-l) ν` says `ν j ≤ ν i` if `ε i = ε j` and `l j < l i`. `δ` is
`New.HCParam.lowerCount l Eq`, the top exponent of the product over the compact roots.
-/

section LaurentAlternants

open Matrix Finset Int AddMonoidAlgebra UnitAddTorus AddCircle Equiv Function HCParam

variable {n : Type} [Fintype n] [DecidableEq n]

/-- For a tuple `x` of unit complex numbers, the algebra homomorphism from Laurent polynomials to
`ℂ` sending the monomial of exponent `γ` to `∏ x_a ^ γ_a`. -/
def torusEval (x : n → Circle) : ℂ[n → ℤ] →ₐ[ℂ] ℂ :=
  lift ℂ ℂ (n → ℤ)
    { toFun (γ : Multiplicative (n → ℤ)) := ∏ a : n, (x a : ℂ) ^ γ.toAdd a
      map_one' := by simp
      map_mul' := by simp [zpow_add₀, prod_mul_distrib] }

omit [DecidableEq n] in
/-- The value of a Laurent polynomial `P` at `x` is the sum over the exponents `γ` of the
coefficient at `γ` times the monomial `∏ x_a ^ γ_a`. -/
lemma torusEval_eq_sum (x : n → Circle) (P : ℂ[n → ℤ]) :
    torusEval x P = P.coeff.sum fun (γ : n → ℤ) (c : ℂ) ↦ c * ∏ a : n, (x a : ℂ) ^ γ a := by
  simp [torusEval, lift_apply']

/-- The finite set of pairs of indices `(a, b)` with `ε a = 1` and `ε b = -1`. -/
def oppositePairs (ε : n → ℤˣ) : Finset (n × n) :=
  univ.filter (ε · = 1) ×ˢ univ.filter (ε · ≠ 1)

omit [DecidableEq n] in
lemma mem_oppositePairs {ε : n → ℤˣ} {p : n × n} :
    p ∈ oppositePairs ε ↔ ε p.1 = 1 ∧ ε p.2 ≠ 1 := by
  simp [oppositePairs]

/-- The Laurent polynomial `∑ sgn(w) x ^ (l ∘ w)`, summed over the permutations `w` that preserve
the signs `ε` (the Weyl group of `K`). -/
def alternant (ε : n → ℤˣ) (l : n → ℤ) : ℂ[n → ℤ] :=
  ∑ w : Perm n, if ε ∘ w = ε then AddMonoidAlgebra.single (l ∘ w) w.sign else 0

/-- The function `t` on `ℤⁿ` is antisymmetric under the Weyl group of `K`:
`t (γ ∘ w) = sgn(w) t γ` for the permutations `w` preserving the signs `ε`. -/
def IsWeylAntisymm (ε : n → ℤˣ) (t : (n → ℤ) → ℂ) : Prop :=
  ∀ w : Perm n, ε ∘ w = ε → ∀ γ : n → ℤ, t (γ ∘ w) = w.sign * t γ

/-- The monoid of pairs `(a, P)`, where `P` is a Laurent polynomial with coefficient `1` at `x ^ a`,
all exponents `γ` of `P` are nonnegative, and every `γ` other than `a` has a lower level:
`l ⬝ᵥ γ < l ⬝ᵥ a`. -/
def leadingMonomials (l : n → ℤ) : Submonoid (Multiplicative (n → ℤ) × ℂ[n → ℤ]) where
  carrier :=
    {p : Multiplicative (n → ℤ) × ℂ[n → ℤ] |
      p.2.coeff p.1.toAdd = 1 ∧
      ∀ γ : n → ℤ, p.2.coeff γ ≠ 0 → 0 ≤ γ ∧ (γ = p.1.toAdd ∨ l ⬝ᵥ γ < l ⬝ᵥ p.1.toAdd)}
  mul_mem' {a b} := by
    -- An exponent of the product is a sum of exponents of the factors. Levels add, so the sum of
    -- the two top exponents arises in one way only and every other sum has a lower level.
    have h_supp (γ : n → ℤ) (hγ : (a.2 * b.2).coeff γ ≠ 0) :
        ∃ y : n → ℤ, a.2.coeff y ≠ 0 ∧ ∃ z : n → ℤ, b.2.coeff z ≠ 0 ∧ y + z = γ := by
      simpa [mem_add] using a.2.support_coeff_mul_subset b.2 (Finsupp.mem_support_iff.2 hγ)
    simp
    grind [UniqueAdd, add_nonneg, coeff_mul_add_of_uniqueAdd, dotProduct_add,
      dotProduct_add l a.1.toAdd b.1.toAdd]
  one_mem' := by simp [← Finsupp.mem_support_iff]

omit [DecidableEq n] in
lemma mem_leadingMonomials_iff (l : n → ℤ) {a : n → ℤ} {P : ℂ[n → ℤ]} :
    (Multiplicative.ofAdd a, P) ∈ leadingMonomials l ↔
      P.coeff a = 1 ∧ ∀ γ : n → ℤ, P.coeff γ ≠ 0 → 0 ≤ γ ∧ (γ = a ∨ l ⬝ᵥ γ < l ⬝ᵥ a) :=
  Iff.rfl

/-- If `l b < l a`, then `x_a` is the monomial of highest level `l ⬝ᵥ γ` of the binomial
`x_a - x_b`. -/
lemma single_sub_single_mem_leadingMonomials (l : n → ℤ) {a b : n} (h_lt : l b < l a) :
    (Multiplicative.ofAdd (Pi.single a 1),
      (.single (Pi.single a 1) 1 - .single (Pi.single b 1) 1 : ℂ[n → ℤ])) ∈ leadingMonomials l := by
  have h_level : l ⬝ᵥ Pi.single b 1 < l ⬝ᵥ Pi.single a 1 := by simpa using h_lt
  refine (mem_leadingMonomials_iff l).2
    ⟨by simp [ne_of_apply_ne (l ⬝ᵥ ·) h_level.ne], fun γ hγ ↦ ?_⟩
  obtain rfl | rfl : γ = Pi.single a 1 ∨ γ = Pi.single b 1 := by
    contrapose! hγ
    simp [hγ.1.symm, hγ.2.symm]
  · exact ⟨Pi.single_nonneg.2 zero_le_one, .inl rfl⟩
  · exact ⟨Pi.single_nonneg.2 zero_le_one, .inr h_level⟩

variable {ε : n → ℤˣ} (l : HCParam ε) (r : ℤˣ → ℤˣ → Prop) [DecidableRel r]
  {ν : n → ℤ} {P Q : ℂ[n → ℤ]} (w : Perm n)

/-- The Laurent polynomial `∏ (x_a - x_b)` over the pairs `(a, b)` with `r (ε a) (ε b)` and
`l b < l a`. It is a partial Weyl denominator (Vandermonde product) for the order given by `l`. -/
def _root_.New.HCParam.rootProd : ℂ[n → ℤ] :=
  ∏ a : n, ∏ b : n with r (ε a) (ε b) ∧ l b < l a,
    (.single (Pi.single a 1) 1 - .single (Pi.single b 1) 1)

/-- The number of `b` with `r (ε a) (ε b)` and `l b < l a`. As a function of `a`, it is the exponent
of the product of the first terms `x_a` of the factors of `New.HCParam.rootProd l r`. -/
def _root_.New.HCParam.lowerCount (a : n) : ℤ := (#{b : n | r (ε a) (ε b) ∧ l b < l a} : ℤ)

omit [DecidableEq n] in
lemma _root_.New.HCParam.lowerCount_nonneg (a : n) : 0 ≤ l.lowerCount r a :=
  Nat.cast_nonneg _

omit [DecidableEq n] in
lemma _root_.New.HCParam.lowerCount_le_card (a : n) : l.lowerCount r a ≤ Fintype.card n :=
  Nat.cast_le.2 (card_le_univ _)

/-! ### Top monomials, alternants and class functions -/

/-- Let the level `o` keep the strict order of `l`. Then `l.rootProd r`, the product of
`x_a - x_b` over `r (ε a) (ε b)` and `l b < l a`, is a polynomial whose only monomial of highest
level `o ⬝ᵥ γ` has exponent `l.lowerCount r` (the number of such `b`) and coefficient `1`. -/
lemma rootProd_mem_leadingMonomials (o : n → ℤ) (h_order : ∀ a b : n, l b < l a → o b < o a) :
    (Multiplicative.ofAdd (l.lowerCount r), l.rootProd r) ∈ leadingMonomials o := by
  -- `l.rootProd r` is a product of binomials `x_a - x_b` with `o b < o a`, each with top monomial
  -- `x_a`. The exponents of the `x_a` add up to `l.lowerCount r`, and `leadingMonomials o` is
  -- closed under products.
  have h_exponent : l.lowerCount r =
      ∑ a : n, ∑ b : n with r (ε a) (ε b) ∧ l b < l a, (Pi.single a 1 : n → ℤ) := by
    simp [pi_eq_sum_univ' (l.lowerCount r), lowerCount]
  rw [h_exponent, rootProd]
  simp_rw [ofAdd_sum, prod_mk_prod]
  refine prod_mem fun a _ ↦ prod_mem fun b hb ↦ ?_
  obtain ⟨-, -, h_lt⟩ := mem_filter.1 hb
  exact single_sub_single_mem_leadingMonomials o (h_order a b h_lt)

/-- The value at `x` of `l.rootProd r` is the product of `x a - x b` over the pairs with
`r (ε a) (ε b)` and `l b < l a`. -/
lemma torusEval_rootProd (x : n → Circle) :
    torusEval x (l.rootProd r) =
      ∏ a : n, ∏ b : n with r (ε a) (ε b) ∧ l b < l a, (x a - x b : ℂ) := by
  simp [torusEval, rootProd, Pi.single_apply]

/-- The product `l.rootProd r` of binomials `x_a - x_b` with `l b < l a` does not vanish at a point
of the torus with distinct coordinates. -/
lemma torusEval_rootProd_ne_zero {x : n → Circle} (hx : Injective x) :
    torusEval x (l.rootProd r) ≠ 0 := by
  -- The value is a product of differences `x a - x b` with `l b < l a`, so `a ≠ b`.
  rw [torusEval_rootProd]
  exact prod_ne_zero_iff.2 fun a _ ↦ prod_ne_zero_iff.2 fun b hb ↦
    sub_ne_zero.2 (Circle.coe_injective.ne (hx.ne (by grind)))

/-- The coefficient of `x ^ γ` in the alternant of `ν` is the sum of the signs of the permutations
`w` that preserve `ε` and satisfy `ν ∘ w = γ`. -/
lemma alternant_apply (γ : n → ℤ) :
    (alternant ε ν).coeff γ = ∑ w : Perm n, if ε ∘ w = ε ∧ ν ∘ w = γ then (w.sign : ℂ) else 0 := by
  simp [alternant, ite_and, Finsupp.single_apply, sum_ite]

/-- At a point `x` of the torus, the alternant of `ν` is the determinant of the matrix with
`(a, b)` entry `x a ^ ν b` if `ε a = ε b` and `0` otherwise. -/
lemma torusEval_alternant (x : n → Circle) :
    torusEval x (alternant ε ν) =
      det (Matrix.of fun a b : n ↦ if ε a = ε b then (x a : ℂ) ^ ν b else 0) := by
  calc torusEval x (alternant ε ν)
    _ = ∑ w : Perm n, if ε ∘ w = ε then (w.sign : ℂ) * ∏ a : n, (x a : ℂ) ^ ν (w a) else 0 := by
      simp [alternant, torusEval, apply_ite (lift ℂ ℂ (n → ℤ) _)]
    _ = ∑ w : Perm n, (w.sign : ℂ) * ∏ a : n, if ε a = ε (w a) then (x a : ℂ) ^ ν (w a) else 0 := by
      simp [prod_ite_zero, funext_iff, eq_comm]
    _ = _ := by simp [← det_transpose (Matrix.of _), det_apply']

section

omit [DecidableEq n]

@[fun_prop]
lemma continuous_torusEval : Continuous fun x : n → Circle ↦ torusEval x P := by continuity

/-- A Laurent polynomial is determined by its values on the torus. -/
lemma eq_of_torusEval_eq (h_eval : ∀ x : n → Circle, torusEval x P = torusEval x Q) : P = Q := by
  -- On the unit torus the monomials are the characters `mFourier`, which are orthonormal in `L²`,
  -- hence linearly independent.
  have h_indep : LinearIndependent ℂ (mFourier (d := n)) :=
    orthonormal_mFourier.linearIndependent.of_comp _
  have h_value (R : ℂ[n → ℤ]) (t : UnitAddTorus n) :
      Finsupp.linearCombination ℂ mFourier R.coeff t = torusEval (fun a ↦ (t a).toCircle) R := by
    simp [torusEval_eq_sum, Finsupp.sum, Finsupp.linearCombination, mFourier, toCircle_zsmul]
  exact ext (h_indep (ContinuousMap.ext fun t ↦ by rw [h_value, h_value, h_eval]))

/-- Weierstrass approximation on a torus: Laurent polynomials are uniformly dense in the
continuous complex functions on (S¹)ⁿ. -/
lemma denseRange_torusEval :
    DenseRange fun P : ℂ[n → ℤ] ↦ ContinuousMap.mk fun x : n → Circle ↦ torusEval x P := by
  -- Transport the density of the span of the characters `mFourier` on `UnitAddTorus n` along
  -- the homeomorphism with `n → Circle`.
  let φ : UnitAddTorus n ≃ₜ (n → Circle) := .piCongrRight fun _ ↦ homeomorphCircle (by simp)
  let Φ : C(UnitAddTorus n, ℂ) ≃ₜ C(n → Circle, ℂ) := φ.arrowCongr (.refl ℂ)
  -- The characters `mFourier` span a dense subspace.
  refine (Φ.isDenseEmbedding.dense_image.2 fun _ ↦ span_mFourier_closure_eq_top.ge ⟨⟩).mono ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  -- The combination of characters with coefficients `c` becomes the Laurent polynomial `⟨c⟩`.
  refine ⟨⟨c⟩, ContinuousMap.ext fun x ↦ ?_⟩
  obtain ⟨t, rfl⟩ := φ.surjective x
  have h_apply (g : C(UnitAddTorus n, ℂ)) : Φ g (φ t) = g t := by simp [Φ, Homeomorph.arrowCongr]
  rw [h_apply]
  simp [φ, homeomorphCircle_apply, torusEval_eq_sum, Finsupp.sum, mFourier, toCircle_zsmul]

/-- Permuting the coordinates of the point is the same as permuting the exponents of `P`. -/
lemma torusEval_comp_perm (x : n → Circle) :
    torusEval (x ∘ w) P = torusEval x ⟨P.coeff.equivMapDomain (w.arrowCongr 1)⟩ := by
  have h_monomial (γ : n → ℤ) : ∏ a : n, (x (w a) : ℂ) ^ γ a = ∏ a : n, (x a : ℂ) ^ γ (w.symm a) :=
    Fintype.prod_equiv w _ _ (by simp)
  simp [torusEval_eq_sum, h_monomial]

/-- Permuting the variables by `w` multiplies the values of `P` on the torus by `c` exactly when
permuting the exponents by `w` multiplies the coefficients of `P` by `c`. -/
lemma torusEval_comp_eq_mul_iff {c : ℂ} :
    (∀ x : n → Circle, torusEval (x ∘ w) P = c * torusEval x P) ↔
      ∀ ν : n → ℤ, P.coeff (ν ∘ w) = c * P.coeff ν := by
  -- Both sides say that `P` with its exponents permuted by `w` is `c • P`: the left side by
  -- `torusEval_comp_perm` and `eq_of_torusEval_eq`, the right side coefficient by coefficient.
  let P' : ℂ[n → ℤ] := ⟨P.coeff.equivMapDomain (w.arrowCongr 1)⟩
  have h_coeff (ν : n → ℤ) : P'.coeff ν = P.coeff (ν ∘ w) := rfl
  calc (∀ x : n → Circle, torusEval (x ∘ w) P = c * torusEval x P)
    _ ↔ ∀ x : n → Circle, torusEval x P' = torusEval x (c • P) := by simp [torusEval_comp_perm, P']
    _ ↔ P' = c • P := ⟨eq_of_torusEval_eq, fun h _ ↦ by rw [h]⟩
    _ ↔ ∀ ν : n → ℤ, P.coeff (ν ∘ w) = c * P.coeff ν := by
      simp [← coeff_inj, Finsupp.ext_iff, h_coeff]

end

/-- Alternants are antisymmetric under the Weyl group of `K`: the coefficient of `x ^ γ` in
`alternant ε ν` is antisymmetric as a function of `γ`. -/
lemma isWeylAntisymm_alternant : IsWeylAntisymm ε (alternant ε ν).coeff := by
  -- By `torusEval_comp_eq_mul_iff` it is enough to permute `x`. This permutes the rows of the
  -- determinant in `torusEval_alternant`, which multiplies it by `w.sign`.
  intro w hw
  refine (torusEval_comp_eq_mul_iff w).1 fun x ↦ ?_
  rw [torusEval_alternant, torusEval_alternant, ← det_permute]
  congr with a b
  simp [show ε (w a) = ε a from congrFun hw a]

/-- Let `K = maxCompactU ε`, and let `diagTorusK x` be the diagonal matrix with entries `x`. If `f`
on the torus and `d` on `K` satisfy `d (y * diagTorusK x * y⁻¹) = f x` for all `y` and `x`, then `f`
is invariant under every permutation `w` of the coordinates that preserves the signs `ε`. -/
lemma apply_comp_perm_of_conj_invariant {w : Perm n} (x : n → Circle) (hw : ε ∘ w = ε)
    {d : maxCompactU ε → ℂ} {f : (n → Circle) → ℂ}
    (h_inv : ∀ (y : maxCompactU ε) (x : n → Circle), d (y * diagTorusK x * y⁻¹) = f x) :
    f (x ∘ w) = f x := by
  -- The permutation matrix `y` of `w` lies in `maxCompactU ε` and conjugates `diagTorusK (x ∘ w)`
  -- to `diagTorusK x`.
  let g : GL n ℂ := permMatrixHom.toHomUnits w
  have hw_apply (a : n) : ε (w a) = ε a := congrFun hw a
  have h_form : (g : Matrix n n ℂ)ᴴ * signMatrix ε * g = signMatrix ε := by
    simp [g, ← Matrix.ext_iff, signMatrix, diagonal, Matrix.mul_apply, sum_ite, hw_apply]
  have h_unitary : (g : Matrix n n ℂ)ᴴ * 1 * g = 1 := by
    simp [g, ← Matrix.ext_iff, Matrix.mul_apply, sum_ite, Matrix.one_apply]
  let y : maxCompactU ε := ⟨⟨g, h_form⟩, h_unitary⟩
  have h_conj : y * diagTorusK (x ∘ w) * y⁻¹ = diagTorusK x := by
    ext
    simp [y, g, diagTorus, ← map_inv, diagonal, Matrix.mul_apply, sum_ite]
  rw [← h_inv y, h_conj, ← h_inv 1, one_mul, inv_one, mul_one]

/-- For injective `l`, the product `l.rootProd Ne` of `x a - x b` over `ε a ≠ ε b` and `l b < l a`
(the positive noncompact roots) is, up to a sign that does not depend on `x`, the product of
`x a - x b` over the pairs `oppositePairs ε` with `ε a = 1`, `ε b = -1`. -/
lemma torusEval_rootProd_noncompact {l : HCParam ε} (hl : l.Injective) (x : n → Circle) :
    torusEval x (l.rootProd Ne) =
      (∏ p ∈ oppositePairs ε, if l p.2 < l p.1 then 1 else -1) *
        ∏ p ∈ oppositePairs ε, (x p.1 - x p.2 : ℂ) := by
  -- A pair `(a, b)` with `ε a ≠ ε b` and `l b < l a` lies in `oppositePairs ε` or does so after a
  -- swap, and the swap changes the sign of `x a - x b`.
  let roots : Finset (n × n) := {p | ε p.1 ≠ ε p.2 ∧ l p.2 < l p.1}
  have h_opp (a b : n) : ε a ≠ ε b ↔ (ε a = 1 ↔ ε b ≠ 1) := by
    grind [units_eq_one_or (ε a), units_eq_one_or (ε b)]
  calc torusEval x (l.rootProd Ne)
    _ = ∏ p ∈ roots, (x p.1 - x p.2 : ℂ) :=
      (torusEval_rootProd l _ x).trans (prod_finset_product' roots univ _ (by simp [roots])).symm
    _ = ∏ p ∈ oppositePairs ε, (if l p.2 < l p.1 then 1 else -1) * (x p.1 - x p.2 : ℂ) := by
      refine prod_nbij' (fun p ↦ if ε p.1 = 1 then p else p.swap)
        (fun p ↦ if l p.2 < l p.1 then p else p.swap) ?_ ?_ ?_ ?_ ?_
      -- Each of the five conditions is a case split on the signs and on the order of `l a`, `l b`.
      all_goals
        rintro ⟨a, b⟩
        grind [mem_oppositePairs]
    _ = _ := prod_mul_distrib

/-- For injective `l`, the values of the product `l.rootProd Ne` over the positive noncompact roots
are invariant under the permutations `w` of the coordinates that preserve the signs `ε`. -/
lemma torusEval_rootProd_noncompact_comp {l : HCParam ε} {w : Perm n} (hl : l.Injective)
    (hw : ε ∘ w = ε) (x : n → Circle) :
    torusEval (x ∘ w) (l.rootProd Ne) = torusEval x (l.rootProd Ne) := by
  -- In the formula `torusEval_rootProd_noncompact` the signs do not depend on `x`, and `w` permutes
  -- the pairs of `oppositePairs ε`.
  have hw_apply (a : n) : ε (w a) = ε a := congrFun hw a
  have h_perm : ∏ p ∈ oppositePairs ε, ((x ∘ w) p.1 - (x ∘ w) p.2 : ℂ) =
      ∏ p ∈ oppositePairs ε, (x p.1 - x p.2 : ℂ) :=
    prod_equiv (w.prodCongr w) (by simp [mem_oppositePairs, hw_apply]) (by simp)
  rw [torusEval_rootProd_noncompact hl, torusEval_rootProd_noncompact hl, h_perm]

/-! ### Antisymmetric functions and dominant weights -/

/-- Let `l` be injective and let `δ = l.lowerCount Eq` count, at `a`, the `b` with `ε a = ε b` and
`l b < l a`. For weights `ν` and `ν'` that are monotone in `l` on each class of `ε` (dominant), the
coefficient of the alternant of `ν + δ` at `ν' + δ` is `1` if `ν' = ν` and `0` otherwise. -/
lemma alternant_coeff_of_isKDominant {l : HCParam ε} {ν ν' : n → ℤ} (hl : l.Injective)
    (hν : IsKDominant ε (-l) ν) (hν' : IsKDominant ε (-l) ν') :
    (alternant ε (ν + l.lowerCount Eq)).coeff (ν' + l.lowerCount Eq) = if ν' = ν then 1 else 0 := by
  -- Both `ν + δ` and `ν' + δ` are strictly dominant, so `(ν + δ) ∘ w = ν' + δ` forces `w = 1`.
  set δ : n → ℤ := l.lowerCount Eq
  have h_strict {μ : n → ℤ} {i j : n} (hμ : IsKDominant ε (-l) μ) (hε : ε i = ε j)
      (hji : l j < l i) : (μ + δ) j < (μ + δ) i := by
    -- `δ j < δ i`: the indices below `j` are below `i`, and `j` is below `i` but not below itself.
    exact add_lt_add_of_le_of_lt (hμ i j hε (neg_lt_neg hji)) (ofNat_lt.2 (card_lt_card
      ((ssubset_iff_of_subset (by grind)).2 ⟨j, by simp [hε, hji], by simp⟩)))
  rw [alternant_apply, sum_eq_single 1 (fun w _ h_ne ↦ ite_eq_right ?_) (by simp)]
  · simp [comm]
  rintro ⟨hw, h_eq⟩
  -- Let `i` be the moved index of largest `l`, and `w j = i`; `w i` and `j` are moved too.
  obtain ⟨i, hi, h_max⟩ := w.support.exists_max_image l
    (nonempty_of_ne_empty (mt Perm.support_eq_empty_iff.1 h_ne))
  obtain ⟨j, hj⟩ := w.surjective i
  have hwi_ne : w i ≠ i := Perm.mem_support.1 hi
  have hwi : l (w i) < l i :=
    (h_max (w i) (Perm.apply_mem_support.2 hi)).lt_of_ne (hl.ne hwi_ne)
  have hji : l j < l i := (h_max j (by grind [Perm.mem_support])).lt_of_ne (hl.ne (by grind))
  apply lt_irrefl ((ν' + δ) i)
  calc (ν' + δ) i = (ν + δ) (w i) := (congrFun h_eq i).symm
    _ < (ν + δ) i := h_strict hν (congrFun hw i).symm hwi
    _ = (ν' + δ) j := by rw [← h_eq, Function.comp_apply, hj]
    _ < (ν' + δ) i := h_strict hν' (by simpa [hj] using congrFun hw j) hji

/-- Let `l` be injective. Every exponent `γ` can be sorted by a permutation `w` that preserves the
signs `ε`: the exponent `γ ∘ w` is monotone in `l` on each class of `ε`. -/
lemma exists_perm_comp_eq_and_apply_le_apply {l : HCParam ε} (hl : l.Injective) (γ : n → ℤ) :
    ∃ w : Perm n, ε ∘ w = ε ∧ ∀ a b : n, ε a = ε b → l a ≤ l b → γ (w a) ≤ γ (w b) := by
  -- Order the indices by `l` and let `w` make `γ ∘ w` lexicographically least. An inversion
  -- could be removed by a swap, which makes `γ ∘ w` smaller.
  let : LinearOrder n := LinearOrder.lift' l hl
  obtain ⟨w, hw, h_min⟩ := exists_min_image {w : Perm n | ε ∘ w = ε} (fun w ↦ toLex (γ ∘ w))
    ⟨1, by simp⟩
  simp only [mem_filter_univ] at hw h_min
  refine ⟨w, hw, fun a b hε hab ↦ not_lt.1 fun h_lt ↦ ?_⟩
  have h_swap : ε ∘ ⇑(w * swap a b) = ε := by
    rw [Perm.coe_mul, ← comp_assoc, hw, comp_swap_eq_update]
    simp [hε]
  exact (h_min _ h_swap).not_gt (Pi.lex_desc (f := γ ∘ w) hab h_lt)

omit [DecidableEq n] in
/-- Let `l` be injective and `γ` strictly monotone in `l` on each class of `ε`. Then
`γ - l.lowerCount Eq` is still monotone in `l` on each class (dominant); here `l.lowerCount Eq a`
counts the `b` with `ε a = ε b` and `l b < l a`. -/
lemma isKDominant_sub_lowerCount {l : HCParam ε} (hl : l.Injective) {γ : n → ℤ}
    (h_strict : ∀ a b : n, ε a = ε b → l a < l b → γ a < γ b) :
    IsKDominant ε (-l) (γ - l.lowerCount Eq) := by
  classical
  intro i j hε hji
  -- The indices `b` of the class with `l j ≤ l b < l i` have distinct values `γ b` in
  -- `[γ j, γ i)`, so there are at most `γ i - γ j` of them.
  let below (a : n) : Finset n := {b | ε a = ε b ∧ l b < l a}
  replace hji : l j < l i := by simpa using hji
  have h_maps : Set.MapsTo γ ↑(below i \ below j) ↑(Ico (γ j) (γ i)) := fun _ ↦ by grind
  have h_injOn : Set.InjOn γ ↑(below i \ below j) := fun _ ↦ by grind
  have h_card : #(below i \ below j) ≤ #(Ico (γ j) (γ i)) :=
    card_le_card_of_injOn γ h_maps h_injOn
  have h_sdiff : (#(below i \ below j) : ℤ) = #(below i) - #(below j) := cast_card_sdiff (by grind)
  have h_Ico : (#(Ico (γ j) (γ i)) : ℤ) = γ i - γ j :=
    card_Ico_of_le _ _ (h_strict j i hε.symm hji).le
  change γ j - #(below j) ≤ γ i - #(below i)
  lia

/-- Let `l` be injective and let `l.lowerCount Eq a` count the `b` with `ε a = ε b` and `l b < l a`.
For every exponent `γ` there are an integer `s` and a weight `ν`, monotone in `l` on each class of
`ε` (dominant), such that `t γ = s * t (ν + l.lowerCount Eq)` for every function `t` that is
antisymmetric under the permutations preserving `ε`. -/
lemma exists_sign_isKDominant {l : HCParam ε} (hl : l.Injective) (γ : n → ℤ) :
    ∃ (s : ℤ) (ν : n → ℤ), IsKDominant ε (-l) ν ∧
      ∀ t : (n → ℤ) → ℂ, IsWeylAntisymm ε t → t γ = s * t (ν + l.lowerCount Eq) := by
  by_cases! h_inj : ∃ i j : n, ε i = ε j ∧ γ i = γ j ∧ i ≠ j
  · -- An odd element of the Weyl group fixes `γ`, so `t γ = -t γ`.
    obtain ⟨i, j, hε, hγ, hij⟩ := h_inj
    refine ⟨0, 0, by simp [IsKDominant], fun t ht ↦ ?_⟩
    have h_neg : t γ = -t γ := by
      simpa [show γ ∘ swap i j = γ from funext (apply_swap_eq_self hγ), hij] using
        ht (swap i j) (funext (apply_swap_eq_self hε)) γ
    simpa using self_eq_neg.1 h_neg
  -- Otherwise `γ` is injective on each class of `ε`, and sorting makes it strictly monotone.
  obtain ⟨w, hw, h_mono⟩ := exists_perm_comp_eq_and_apply_le_apply hl γ
  have h_strict (a b : n) (hε : ε a = ε b) (hab : l a < l b) : (γ ∘ w) a < (γ ∘ w) b := by
    refine (h_mono a b hε hab.le).lt_of_ne fun h_eq ↦ hab.ne (congrArg l (w.injective ?_))
    exact h_inj (w a) (w b) ((congrFun hw a).trans (hε.trans (congrFun hw b).symm)) h_eq
  refine ⟨w.sign, γ ∘ w - l.lowerCount Eq, isKDominant_sub_lowerCount hl h_strict, fun t ht ↦ ?_⟩
  rw [sub_add_cancel, ht w hw]
  simp [← mul_assoc, ← cast_mul]

end LaurentAlternants

/-! ## Characters of K-types and Weyl's character formula for K -/

section WeylCharacterK

open Matrix Finset Complex DiscreteSeries Equiv HCParam BlockTriangular

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {l ν : HCParam (n := n) ε}

/-- The continuous function `g ↦ (∫ y, New.weightMinors ν (y⁻¹ g y)) / ∫ k, |New.weightMinors ν k|²`
on `K`, for Haar measure of mass one. It is defined for every `ν`. If `l` is injective and `ν` is
dominant for the order of `l`, it is the character of highest weight `ν` on the torus (see
`New.Orbital.weyl_character_kTypeChar`). -/
noncomputable def _root_.New.HCParam.kTypeChar (ν : HCParam ε) : C(maxCompactU ε, ℂ) where
  toFun g := (∫ y : maxCompactU ε, weightMinors ν (y⁻¹ * g * y).1 ∂haarK ε) / ν.kTypeNormSq
  continuous_toFun := by
    -- an integral over the compact group `maxCompactU ε` depends continuously on the parameter `g`
    rw [← (haarK ε).restrict_univ]
    exact (continuous_parametric_integral_of_continuous (by fun_prop (disch :=
      simp [GeneralLinearGroup.det_ne_zero]))
        isCompact_univ).div_const _

/-- Given unitary matrices `g τ` on the blocks `{i | ε i = τ}`, there is an element `y` of `K` whose
matrix is the block diagonal matrix of the `g τ`, reindexed by `n`. Its diagonal blocks are the
`g τ`. -/
lemma exists_maxCompactU_of_blocks
    (g : ∀ τ : ℤˣ, Matrix {i : n // ε i = τ} {i : n // ε i = τ} ℂ)
    (h : ∀ τ : ℤˣ, (g τ)ᴴ * g τ = 1) :
    ∃ y : maxCompactU ε,
      (y : Matrix n n ℂ) = reindex (sigmaFiberEquiv ε) (sigmaFiberEquiv ε) (blockDiagonal' g) ∧
        (y : Matrix n n ℂ).toSquareBlock ε = g := by
  let e : (Σ τ : ℤˣ, {i : n // ε i = τ}) ≃ n := sigmaFiberEquiv ε
  let y : Matrix n n ℂ := reindex e e (blockDiagonal' g)
  have h_block : y ∈ blockDiagAlg ε :=
    mem_blockDiagAlg.2 (by simp +contextual [y, e, sigmaFiberEquiv, blockDiagonal'_apply_ne])
  -- `y` is unitary and commutes with `signMatrix ε`, so it preserves the form
  have h_unitary : yᴴ * y = 1 := by simp [y, ← blockDiagonal'_mul, h, ← Pi.one_def]
  have h_form : yᴴ * signMatrix ε * y = signMatrix ε := by
    rw [Commute.right_comm (h_block _ rfl), h_unitary, one_mul]
  refine ⟨⟨U.of IsHermitianInvolution.isUnit y h_form, mem_maxCompactU.2 h_block⟩, rfl, ?_⟩
  change (y.submatrix e e).blockDiag' = g
  simp [y]

omit [DecidableEq n] in
/-- Let `q τ` enumerate the block `{i | ε i = τ}` by increasing `l`, and let `ν` be dominant:
`ν j ≤ ν i` if `ε i = ε j` and `l j < l i`. Then on each block, read by decreasing `l`, the weight
`ν` is a constant `e τ` plus the partition `New.diagramWeight` of `κ`: its value at `(τ, k)` is the
sum of `κ τ h` for `k < h < N τ`, where `N τ = rankAt _ τ` is the size of the block. -/
lemma exists_eq_const_add_partition (hν : IsKDominant ε (-l) ν)
    (q : ∀ τ : ℤˣ, Fin (Fintype.card {i : n // ε i = τ}) ≃ {i : n // ε i = τ})
    (hq : ∀ (τ : ℤˣ) (a b : Fin (Fintype.card {i : n // ε i = τ})),
      l (q τ a) < l (q τ b) ↔ a < b) :
    ∃ (κ : ℤˣ → ℕ → ℕ) (e : ℤˣ → ℤ),
      ∀ (τ : ℤˣ) (k : ℕ) (hk : k < Fintype.card {i : n // ε i = τ}),
        ν (q τ (Fin.rev ⟨k, hk⟩)) =
          e τ + diagramWeight (rankAt fun τ : ℤˣ ↦ {i : n // ε i = τ}) κ (τ, k) := by
  -- `g τ` lists the values of `ν` on the block, and `κ τ` their successive differences.
  let g (τ : ℤˣ) (k : ℕ) : ℤ := (List.ofFn fun i ↦ ν (q τ i.rev)).getD k 0
  let κ (τ : ℤˣ) (k : ℕ) : ℕ := (g τ (k - 1) - g τ k).toNat
  let μ : ℤˣ × ℕ →₀ ℕ := diagramWeight (rankAt fun τ : ℤˣ ↦ {i : n // ε i = τ}) κ
  -- `μ (τ, k)` is the sum of the later differences, which telescopes by induction on `k`.
  refine ⟨κ, fun τ ↦ g τ 0 - μ (τ, 0), fun τ k hk ↦ ?_⟩
  have h_value (j : ℕ) (hj : j < Fintype.card {i : n // ε i = τ}) :
      g τ j = ν (q τ (Fin.rev ⟨j, hj⟩)) := by simp [g, hj]
  rw [← h_value k hk]
  induction k with
  | zero => ring
  | succ k ih =>
    have hk' : k < Fintype.card {i : n // ε i = τ} := by omega
    have h_sign : ε (q τ (Fin.rev ⟨k + 1, hk⟩)) = ε (q τ (Fin.rev ⟨k, hk'⟩)) :=
      (q τ _).2.trans (q τ _).2.symm
    have h_lt : l (q τ (Fin.rev ⟨k + 1, hk⟩)) < l (q τ (Fin.rev ⟨k, hk'⟩)) :=
      (hq τ _ _).2 (Fin.rev_lt_rev.2 k.lt_succ_self)
    have h_antitone : g τ (k + 1) ≤ g τ k := by
      simpa [h_value, hk, hk'] using hν _ _ h_sign.symm (neg_lt_neg h_lt)
    have h_succ : μ (τ, k) = μ (τ, k + 1) + κ τ (k + 1) := by
      simp [μ, GL.diagramWeight_eq_succ_add _ τ k, rankAt, hk]
    have h_step : (μ (τ, k) : ℤ) = μ (τ, k + 1) + (g τ k - g τ (k + 1)) := by
      simp [h_succ, κ, h_antitone]
    linarith [ih hk']

/-- On an element `k` of `K`, which is block diagonal for `ε`, the function `New.weightMinors ν`
(the product of determinant powers and principal minors with highest weight `ν`) is the product of
the same functions on the diagonal blocks of `k`. -/
lemma prod_weightMinors_toSquareBlock (k : maxCompactU ε) :
    ∏ τ : ℤˣ, weightMinors (fun i : {i : n // ε i = τ} ↦ ν i)
        ((k : Matrix n n ℂ).toSquareBlock ε τ) = weightMinors ν (k : Matrix n n ℂ) := by
  set A : Matrix n n ℂ := (k : Matrix n n ℂ)
  have h_tri : A.BlockTriangular ε :=
    fun i j hij ↦ mem_blockDiagAlg.1 (mem_maxCompactU.1 k.2) i j hij.ne'
  have h_det : A.det = ∏ τ : ℤˣ, (A.toSquareBlock ε τ).det := h_tri.det_fintype
  have h_ne (τ : ℤˣ) : (A.toSquareBlock ε τ).det ≠ 0 :=
    prod_ne_zero_iff.1 (h_det.symm.trans_ne k.1.1.det_ne_zero) τ (mem_univ τ)
  -- each minor of `A` is the product of the corresponding minors of the blocks
  have h_minor (t : ℤ) : principalMinor A (t ≤ ν ·) =
      ∏ τ : ℤˣ, principalMinor (A.toSquareBlock ε τ) (fun i ↦ t ≤ ν i.1) := by
    have h_minor_tri :
        (1 - diagonal (fun i : n ↦ if t ≤ ν i then (1 : ℂ) else 0) * (1 - A)).BlockTriangular ε :=
      blockTriangular_one.sub ((blockTriangular_diagonal _).mul (blockTriangular_one.sub h_tri))
    simp only [principalMinor_eq_det, h_minor_tri.det_fintype]
    congr! 2 with τ
    ext i j
    simp [toSquareBlock_def, Matrix.one_apply, Subtype.ext_iff]
  let N : ℤ := ∑ j : n, |ν j|
  have h_bounds : ∀ i : n, -N ≤ ν i ∧ ν i ≤ N := neg_sum_abs_le_and_le_sum_abs ν
  calc ∏ τ : ℤˣ, weightMinors (fun i : {i : n // ε i = τ} ↦ ν i) (A.toSquareBlock ε τ)
    _ = (∏ τ : ℤˣ, (A.toSquareBlock ε τ).det) ^ (-N) *
          ∏ t ∈ Ioc (-N) N, ∏ τ : ℤˣ,
            principalMinor (A.toSquareBlock ε τ) (fun i ↦ t ≤ ν i.1) := by
      simp_rw [weightMinors_eq_det_zpow_mul_prod (h_ne _) _ _ (h_bounds ·.1), prod_mul_distrib,
        prod_zpow]
      rw [prod_comm]
    _ = A.det ^ (-N) * ∏ t ∈ Ioc (-N) N, principalMinor A (t ≤ ν ·) := by simp_rw [h_det, h_minor]
    _ = weightMinors ν A :=
      (weightMinors_eq_det_zpow_mul_prod k.1.1.det_ne_zero _ _ h_bounds).symm

/-- Suppose that, with respect to numberings `p τ` of the blocks `{i | ε i = τ}`, the weight `ν` is
a constant `e τ` plus the partition `New.diagramWeight` of `κ` (whose `k`th part is the sum of the
`κ τ h` with `k < h < #block`). Here `New.HCParam.kTypeChar ν` is the function `g ↦ (∫ y,
weightMinors ν (y⁻¹ g y)) / ∫ k, |weightMinors ν k|²` on `K = U(diag ε) ∩ U(n)`, for Haar measure of
mass one; for dominant `ν` it is the character of highest weight `ν`. The claim is that at the
diagonal matrix `diagTorusK x` with entries `x`, `kTypeChar ν` is the trace of `New.schur κ` (the
matrix of the Schur module of `κ`), twisted on each block by the power `e τ` of the determinant. -/
lemma kTypeChar_diagTorusK_eq_trace_schur {κ : ℤˣ → ℕ → ℕ} {e : ℤˣ → ℤ}
    (p : ∀ τ : ℤˣ, {i : n // ε i = τ} ≃ Fin (Fintype.card {i : n // ε i = τ}))
    (hν : ∀ (τ : ℤˣ) (i : {i : n // ε i = τ}),
      ν i = e τ + diagramWeight (rankAt fun τ : ℤˣ ↦ {i : n // ε i = τ}) κ (τ, p τ i))
    (x : n → Circle) :
    ν.kTypeChar (diagTorusK x) = (∏ τ : ℤˣ, ∏ a : {i : n // ε i = τ}, (x a : ℂ) ^ e τ) *
      (schur κ fun τ : ℤˣ ↦ diagonal fun a : {i : n // ε i = τ} ↦ (x a : ℂ)).trace := by
  -- On `K = ∏ U(m τ)`, `weightMinors ν` is a matrix coefficient of the irreducible representation
  -- `R`, a product of twisted Schur modules. By Schur's lemma `kTypeChar` is the trace of `R`.
  let m (τ : ℤˣ) : Type := {i // ε i = τ}
  -- `blocks k` is the family of the diagonal blocks of `k`
  let toParabolic : maxCompactU ε →* parabolic (R := ℂ) ε :=
    .mk' (fun k ↦ ⟨k.1.1, fun i j hij ↦ mem_blockDiagAlg.1 (mem_maxCompactU.1 k.2) i j hij.ne'⟩)
      fun _ _ ↦ rfl
  let blocks : maxCompactU ε →* ∀ τ, GL (m τ) ℂ :=
    .pi fun τ ↦ (blockHom ε τ).comp toParabolic
  let R : maxCompactU ε →* Matrix (WeylIndexFamily m κ) (WeylIndexFamily m κ) ℂ :=
    (weylRep κ e).comp blocks
  obtain ⟨v, w, h_coeff⟩ : ∃ v w : WeylIndexFamily m κ → ℂ,
      ∀ k : maxCompactU ε, w ⬝ᵥ R k *ᵥ v = weightMinors ν k := by
    let u : WeylIndexFamily m κ → ℂ := weylEval m κ (permArray fun τ i ↦ (p τ i : ℕ))
    refine ⟨u, u ᵥ* weylGramOver, fun k ↦ ?_⟩
    rw [← dotProduct_mulVec, ← prod_weightMinors_toSquareBlock k]
    refine (weylRep_coeff_eq_prod_weightMinors p (blocks k)).trans (prod_congr rfl fun τ _ ↦ ?_)
    exact congrArg₂ weightMinors (funext fun i ↦ (hν τ i).symm) rfl
  have h_cont : Continuous fun k : maxCompactU ε ↦ R k := by
    simp [R, blocks, toParabolic, weylRep, Units.smul_def, blockHom, toSquareBlock_def]
    -- `try` is needed as the discharger is run on other side conditions as well
    fun_prop (disch := try exact fun k ↦ .inl (blocks k _).det_ne_zero)
  -- The mean `A` of `R g (v wᵀ) R g⁻¹` over `K` commutes with `R`, hence is a scalar `z`;
  -- `h_mean L` says that `L A` is the mean of `L (R g (v wᵀ) R g⁻¹)` for a linear map `L`.
  obtain ⟨A, hA, h_mean⟩ :=
    exists_intertwining_mean (haarK ε) R R (vecMulVec v w) (by fun_prop)
  obtain ⟨z, rfl⟩ : A ∈ Set.range (scalar (WeylIndexFamily m κ)) :=
    mem_range_scalar_of_commute_schur fun g hg ↦ by
      obtain ⟨y, -, rfl⟩ := exists_maxCompactU_of_blocks g hg
      -- the two sides differ from those of `A * R y = R y * A` by a nonzero scalar
      simpa [R, weylRep, Units.smul_def, GeneralLinearGroup.det_ne_zero, zpow_ne_zero] using! hA y
  have h_one : w ⬝ᵥ v = 1 := by simpa using h_coeff 1
  -- Apply the functionals `X ↦ tr (X R k)` and `X ↦ wᵀ X v` to the mean; the second takes the
  -- value `z` on the scalar, because `wᵀ v = weightMinors ν 1 = 1`.
  have h_integral (k : maxCompactU ε) :
      ∫ g, weightMinors ν (g⁻¹ * k * g).1 ∂haarK ε = z * (R k).trace := by
    have h_trace_conj (g : maxCompactU ε) :
        (R g * vecMulVec v w * R g⁻¹ * R k).trace = weightMinors ν (g⁻¹ * k * g).1 := by
      rw [← h_coeff]
      simp [mul_vecMulVec, vecMulVec_mul, ← dotProduct_mulVec, dotProduct_comm (_ *ᵥ _)]
    simpa [h_trace_conj, ← smul_one_eq_diagonal] using
      h_mean (traceLinearMap _ ℂ ℂ ∘ₗ .mulRight ℂ (R k))
  have h_norm : ν.kTypeNormSq = z := by
    -- the functional `X ↦ wᵀ X v`
    let coeffMap : Matrix (WeylIndexFamily m κ) (WeylIndexFamily m κ) ℂ →ₗ[ℂ] ℂ :=
      (dotProductBilin ℂ ℂ w).comp ((mulVecBilin ℂ ℂ).flip v)
    have h_normSq (g : maxCompactU ε) :
        coeffMap (R g * vecMulVec v w * R g⁻¹) = (‖weightMinors ν g‖ ^ 2 : ℝ) := by
      simp [coeffMap, mul_vecMulVec, vecMulVec_mul, vecMulVec_mulVec, ← dotProduct_mulVec,
        weightMinors_unitary_inv, conj_mul', h_coeff]
    rw [kTypeNormSq, ← integral_complex_ofReal,
      ← show coeffMap (scalar _ z) = z by simp [coeffMap, ← smul_one_eq_diagonal, h_one],
      ← h_mean coeffMap]
    simp [h_normSq]
  have h_trace (k : maxCompactU ε) : ν.kTypeChar k = (R k).trace := by
    simp [↓h_integral, ← h_norm, ne_of_gt, kTypeChar]
  have h_blocks (τ : ℤˣ) :
      (blocks (diagTorusK x) τ : Matrix (m τ) (m τ) ℂ) = diagonal fun a : m τ ↦ (x a : ℂ) := by
    ext
    simp [m, blocks, toParabolic, blockHom, toSquareBlock_def, diagTorus, diagonal_apply,
      Subtype.val_inj]
  rw [h_trace]
  simp [R, weylRep, Units.smul_def, GeneralLinearGroup.val_det_apply, h_blocks, m, prod_zpow]

omit [DecidableEq n] in
/-- If `q τ` enumerates the block of sign `τ` by increasing `l`, then the indices of this block at
which `l` is below `l (q τ j)` are the `q τ i` with `i < j`. -/
lemma filter_lt_eq_map_Iio
    (q : ∀ τ : ℤˣ, Fin (Fintype.card {i : n // ε i = τ}) ≃ {i : n // ε i = τ})
    (hq : ∀ (τ : ℤˣ) (a b : Fin (Fintype.card {i : n // ε i = τ})),
      l (q τ a) < l (q τ b) ↔ a < b)
    (τ : ℤˣ) (j : Fin (Fintype.card {i : n // ε i = τ})) :
    ({b : n | τ = ε b ∧ l b < l (q τ j)} : Finset n) = (Iio j).map (q τ).asEmbedding := by
  ext b
  simp only [mem_filter, mem_univ, true_and, mem_map]
  constructor
  · rintro ⟨rfl, h_lt⟩
    exact ⟨(q (ε b)).symm ⟨b, rfl⟩, by simpa [← hq] using h_lt, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(q τ i).2.symm, (hq τ i j).2 (mem_Iio.1 hi)⟩

/-- If `q τ` enumerates the block of sign `τ` by increasing `l`, then on the torus the product over
the compact roots is the product over the blocks of Vandermonde determinants. -/
lemma torusEval_rootProd_eq_prod_vandermonde
    (q : ∀ τ : ℤˣ, Fin (Fintype.card {i : n // ε i = τ}) ≃ {i : n // ε i = τ})
    (hq : ∀ (τ : ℤˣ) (a b : Fin (Fintype.card {i : n // ε i = τ})),
      l (q τ a) < l (q τ b) ↔ a < b)
    (x : n → Circle) :
    torusEval x (l.rootProd Eq) =
      ∏ τ : ℤˣ, (vandermonde ((fun a : {i : n // ε i = τ} ↦ (x a : ℂ)) ∘ q τ)).det := by
  rw [torusEval_rootProd, ← Fintype.prod_fiberwise ε]
  congr with τ
  calc ∏ a : {i : n // ε i = τ}, ∏ b : n with ε a = ε b ∧ l b < l a, (x a - x b : ℂ)
    _ = ∏ j : Fin (Fintype.card {i : n // ε i = τ}), ∏ i ∈ Iio j,
          (x (q τ j) - x (q τ i) : ℂ) := by
      rw [← (q τ).prod_comp]
      simp [(q τ _).2, filter_lt_eq_map_Iio q hq]
    _ = ∏ i : Fin (Fintype.card {i : n // ε i = τ}), ∏ j ∈ Ioi i,
          (x (q τ j) - x (q τ i) : ℂ) := prod_comm' (by simp)
    _ = _ := (det_vandermonde _).symm

/-- Let `l` be injective and `ν` dominant for the order of `l`. Enumerate each block `{i | ε i = τ}`
by increasing `l`, through `q τ`. Then on the block, read by decreasing `l`, the weight `ν` is a
constant `e τ` plus the partition `New.diagramWeight` of some `κ` (value at `(τ, k)`: the sum of
`κ τ h` for `k < h < rankAt _ τ`, the block size), and on the torus `New.HCParam.kTypeChar ν` is the
trace of `New.schur κ` twisted by the powers `e τ` of the determinants of the blocks. -/
lemma exists_kTypeChar_diagTorusK_eq_trace_schur (hl : l.Injective) (hν : IsKDominant ε (-l) ν) :
    ∃ (q : ∀ τ : ℤˣ, Fin (Fintype.card {i : n // ε i = τ}) ≃ {i : n // ε i = τ})
      (κ : ℤˣ → ℕ → ℕ) (e : ℤˣ → ℤ),
      (∀ (τ : ℤˣ) (a b : Fin (Fintype.card {i : n // ε i = τ})), l (q τ a) < l (q τ b) ↔ a < b) ∧
      (∀ (τ : ℤˣ) (j : Fin (Fintype.card {i : n // ε i = τ})),
        ν (q τ j) = e τ + diagramWeight (rankAt fun τ : ℤˣ ↦ {i : n // ε i = τ}) κ (τ, j.rev)) ∧
      ∀ x : n → Circle, ν.kTypeChar (diagTorusK x) =
        (∏ τ : ℤˣ, ∏ a : {i : n // ε i = τ}, (x a : ℂ) ^ e τ) *
          (schur κ fun τ : ℤˣ ↦ diagonal fun a : {i : n // ε i = τ} ↦ (x a : ℂ)).trace := by
  let m (τ : ℤˣ) : Type := {i // ε i = τ}
  have h_enum (τ : ℤˣ) : ∃ q : Fin (Fintype.card (m τ)) ≃ m τ,
      ∀ a b : Fin (Fintype.card (m τ)), l (q a).1 < l (q b).1 ↔ a < b :=
    exists_equiv_fin_lt_iff (n := m τ) hl.injOn.injective
  choose q hq using h_enum
  obtain ⟨κ, e, h_partition⟩ := exists_eq_const_add_partition hν q hq
  have hν_q (τ : ℤˣ) (j : Fin (Fintype.card (m τ))) :
      ν (q τ j).1 = e τ + diagramWeight (rankAt m) κ (τ, j.rev) := by
    simpa only [Fin.eta, Fin.rev_rev] using h_partition τ j.rev j.rev.2
  -- `(q τ).symm.trans Fin.revPerm` numbers the block by decreasing `l`.
  exact ⟨q, κ, e, hq, hν_q, kTypeChar_diagTorusK_eq_trace_schur
    (fun τ ↦ (q τ).symm.trans Fin.revPerm) fun τ i ↦ by simpa using hν_q τ ((q τ).symm i)⟩

/-- If `l` is injective and `ν` is dominant for the order of `l`, then on the diagonal torus
`New.HCParam.kTypeChar ν` is given by a Laurent polynomial. -/
lemma exists_kTypeChar_diagTorusK_eq_torusEval (hl : l.Injective) (hν : IsKDominant ε (-l) ν) :
    ∃ P : AddMonoidAlgebra ℂ (n → ℤ), ∀ x : n → Circle,
      ν.kTypeChar (diagTorusK x) = torusEval x P := by
  -- The character is a twisted trace of `schur κ`, which on diagonal matrices is diagonal with
  -- monomial entries.
  obtain ⟨-, κ, e, -, -, h_char⟩ := exists_kTypeChar_diagTorusK_eq_trace_schur hl hν
  let m (τ : ℤˣ) : Type := {i // ε i = τ}
  let P : AddMonoidAlgebra ℂ (n → ℤ) :=
    ∑ i : WeylIndexFamily m κ, ∏ τ, ∏ a : m τ, .single (Pi.single a.1 (e τ + tableauWeight i τ a)) 1
  refine ⟨P, fun x ↦ ?_⟩
  have h_single (a : n) (c : ℤ) : torusEval x (.single (Pi.single a c) 1) = (x a : ℂ) ^ c := by
    simp [torusEval, Pi.single_apply]
  have h_value : torusEval x P =
      ∑ i : WeylIndexFamily m κ, ∏ τ, ∏ a : m τ, (x a.1 : ℂ) ^ (e τ + tableauWeight i τ a) := by
    simp only [P, map_sum, map_prod, h_single]
  rw [h_char, h_value, schur_diagonal, trace_diagonal, mul_sum]
  simp only [zpow_add₀ (Circle.coe_ne_zero _), zpow_natCast, prod_mul_distrib, m]

/-- Weyl's character formula for `K` at a point `x` of the torus. Let `l` be injective and `ν`
dominant for the order of `l`. The product of `x a - x b` over `ε a = ε b`, `l b < l a`, times
`New.HCParam.kTypeChar ν` at the diagonal matrix with entries `x`, is
`∑ sgn(w) x ^ ((ν + δ) ∘ w)`, where `δ a` is the number of such `b` and `w` runs over the
permutations preserving `ε`. -/
lemma torusEval_rootProd_mul_kTypeChar_eq_alternant (hl : l.Injective)
    (hν : IsKDominant ε (-l) ν) (x : n → Circle) :
    torusEval x (l.rootProd Eq) * ν.kTypeChar (diagTorusK x) =
      torusEval x (alternant ε (ν + l.lowerCount Eq)) := by
  -- The character is a twisted trace of Schur modules, and `weyl_character` (the formula for
  -- Schur modules of `GL`) applies to each block.
  set δ : n → ℤ := l.lowerCount Eq
  obtain ⟨q, κ, e, hq, hν_q, h_char⟩ := exists_kTypeChar_diagTorusK_eq_trace_schur hl hν
  -- The alternant over the Weyl group of `K` is the determinant of a block diagonal matrix `Z`,
  -- and the denominator is a product of Vandermonde determinants.
  let Z : Matrix n n ℂ := of fun a b ↦ if ε a = ε b then (x a : ℂ) ^ (ν + δ) b else 0
  have h_tri : Z.BlockTriangular ε := fun a b hab ↦ ite_eq_right hab.ne'
  have h_alt : torusEval x (alternant ε (ν + δ)) = ∏ τ : ℤˣ, (Z.toSquareBlock ε τ).det :=
    (torusEval_alternant x).trans h_tri.det_fintype
  rw [torusEval_rootProd_eq_prod_vandermonde q hq, h_char, mul_rotate', weyl_character q,
    ← prod_mul_distrib, h_alt]
  -- In each block, move the factor `∏ a, x a ^ e τ` into the determinant and compare entries.
  congr with τ
  rw [← det_submatrix_equiv_self (q τ), ← (q τ).prod_comp, ← det_mul_column]
  have hδ_q (j : Fin (Fintype.card {i : n // ε i = τ})) : δ (q τ j) = (j : ℤ) := by
    simp [δ, lowerCount, (q τ j).2, filter_lt_eq_map_Iio q hq]
  congr with i j
  simp [toSquareBlock_def, Z, (q τ _).2, hν_q, hδ_q, zpow_add₀, pow_add, mul_assoc]

/-- Weyl's character formula for `K`. Let `l` be injective and `ν` dominant for `K` in the order of
`l`: `ν b ≤ ν a` if `ε a = ε b` and `l b < l a` (this is `New.IsKDominant ε (-l) ν`). Let `χ x` be
`New.HCParam.kTypeChar ν` at the diagonal matrix with entries `x`. (a) `χ` is given by a Laurent
polynomial in `x`; (b) `∏ (x a - x b) * χ x = ∑ sgn(w) x ^ ((ν + δ) ∘ w)`, the product over
`ε a = ε b`, `l b < l a`, with `δ a` the number of such `b`, the sum over the permutations
preserving `ε`. -/
lemma weyl_character_kTypeChar (hl : l.Injective) (hν : IsKDominant ε (-l) ν) :
    (∃ P : AddMonoidAlgebra ℂ (n → ℤ), ∀ x : n → Circle,
      ν.kTypeChar (diagTorusK x) = torusEval x P) ∧
    ∀ x : n → Circle,
      torusEval x (l.rootProd Eq) * ν.kTypeChar (diagTorusK x) =
        torusEval x (alternant ε (ν + l.lowerCount Eq)) :=
  ⟨exists_kTypeChar_diagTorusK_eq_torusEval hl hν,
    torusEval_rootProd_mul_kTypeChar_eq_alternant hl hν⟩

/-- Weyl's denominator formula for `K`: for injective `l`, the product of `x a - x b` over
`ε a = ε b`, `l b < l a` is `∑ sgn(w) x ^ (δ ∘ w)` over the permutations `w` that preserve
`ε`, where `δ a` is the number of such `b`. -/
lemma weyl_denominator (hl : l.Injective) : l.rootProd Eq = alternant ε (l.lowerCount Eq) := by
  -- the case `ν = 0` of the character formula, where the character is `1`
  refine eq_of_torusEval_eq fun x ↦ ?_
  have h_char : kTypeChar (0 : HCParam ε) (diagTorusK x) = 1 := by
    simp [kTypeNormSq, kTypeChar, GeneralLinearGroup.det_ne_zero, Pi.zero_def]
  simpa [h_char] using
    torusEval_rootProd_mul_kTypeChar_eq_alternant (ν := 0) hl (by simp [IsKDominant]) x

/-- Every element of the compact group `K` is conjugate in `K` to an element of the diagonal
torus. -/
lemma exists_conj_diagTorusK (k : maxCompactU ε) :
    ∃ (y : maxCompactU ε) (x : n → Circle), y * diagTorusK x * y⁻¹ = k := by
  -- Write `k = exp X` with `X` block diagonal, and diagonalise the Hermitian blocks of `-I • X`
  -- by unitary matrices; these assemble to the conjugating element `y`.
  obtain ⟨X, hXk, hX⟩ := exists_expU_eq_maxCompactU k
  set H : Matrix n n ℂ := -Complex.I • X.1 with hH
  have h_herm (t : ℤˣ) : (H.toSquareBlock ε t).IsHermitian := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simpa [hH, hi, hj, signMatrix, add_eq_zero_iff_eq_neg, field, toSquareBlock_def] using
      congrFun (congrFun (X.2 : X.1ᴴ * signMatrix ε + signMatrix ε * X.1 = 0) i) j
  let U (t : ℤˣ) : Matrix {i // ε i = t} {i // ε i = t} ℂ := (h_herm t).eigenvectorUnitary.1
  obtain ⟨y, hy, -⟩ := exists_maxCompactU_of_blocks U
    fun t ↦ Unitary.coe_star_mul_self (h_herm t).eigenvectorUnitary
  -- `θ i` is the eigenvalue with index `i` of the block that contains `i`
  let θ (i : n) : ℝ := (h_herm (ε i)).eigenvalues ⟨i, rfl⟩
  let e : Matrix (Σ t : ℤˣ, {i // ε i = t}) (Σ t : ℤˣ, {i // ε i = t}) ℂ ≃+* Matrix n n ℂ :=
    reindexRingEquiv ℂ (sigmaFiberEquiv ε)
  have h_spectral : H.toSquareBlock ε =
      fun t ↦ U t * diagonal (fun i ↦ ((h_herm t).eigenvalues i : ℂ)) * star (U t) :=
    funext fun t ↦ (h_herm t).spectral_theorem
  -- `H` is block diagonal, as `X` is, so it is recovered from its blocks
  have h_recover : e (blockDiagonal' (H.toSquareBlock ε)) = H := by
    refine e.eq_symm_apply.1 (ext fun ⟨s, i, hi⟩ ⟨t, j, hj⟩ ↦ ?_)
    by_cases hst : s = t
    · subst hst
      simp [e, sigmaFiberEquiv, toSquareBlock_def]
    · have h_off : X.1 i j = 0 := mem_blockDiagAlg.1 hX i j (by rwa [hi, hj])
      simp [e, hH, sigmaFiberEquiv, blockDiagonal'_apply_ne, hst, h_off]
  have h_eigenvalues : e (blockDiagonal' fun t ↦ diagonal fun i ↦ ((h_herm t).eigenvalues i : ℂ)) =
      diagonal fun i ↦ (θ i : ℂ) := by
    simp [e, θ, submatrix_diagonal_equiv, blockDiagonal'_diagonal]
    -- on both sides the index of `i` within its block is `⟨i, rfl⟩`
    exact fun i ↦ rfl
  have hy_eq : e (blockDiagonal' U) = (y : Matrix n n ℂ) := hy.symm
  have hy_star : e (blockDiagonal' fun t ↦ star (U t)) = (y : Matrix n n ℂ)⁻¹ := by
    simp [e, hy, ↓maxCompactU.coe_inv, star_eq_conjTranspose]
  have h_conj : H =
      (y : Matrix n n ℂ) * diagonal (fun i ↦ (θ i : ℂ)) * (y : Matrix n n ℂ)⁻¹ := by
    rw [← h_recover, h_spectral, blockDiagonal'_mul, blockDiagonal'_mul, map_mul, map_mul, hy_eq,
      h_eigenvalues, hy_star]
  have h_diag : (X : Matrix n n ℂ) =
      (y : Matrix n n ℂ) * diagonal (fun i ↦ θ i * Complex.I) * (y : Matrix n n ℂ)⁻¹ := by
    rw [show (X : Matrix n n ℂ) = Complex.I • H by simp [hH, smul_smul], h_conj, ← smul_mul_assoc,
      ← mul_smul_comm, ← diagonal_smul]
    simp [Pi.smul_def, mul_comm Complex.I]
  -- exponentiate: `exp` commutes with conjugation and acts entrywise on a diagonal matrix
  refine ⟨y, fun i ↦ Circle.exp (θ i), (Subtype.ext (Subtype.ext (Units.ext ?_))).symm⟩
  simp [← hXk, h_diag, exp_eq_exp_ℂ, ← Pi.exp_def, ← exp_diagonal, ← Matrix.exp_conj, diagTorus]

end WeylCharacterK

end New.Orbital

/-!
## Weyl's dimension formula for U(n)

`New.weyl_dimension_formula` evaluates `Λ.kTypeNormSq = ∫ |New.weightMinors Λ k|² dk` over `U(n)`
(all signs `1`). In the classical theory this is the reciprocal of the dimension of the
representation of highest weight `Λ = λ - ρ`, where `ρ` is half the sum of the positive roots.
-/

section WeylDimension

open Finset Complex Nat New Orbital AddCircle HCParam Matrix
/-- For an injective `l` with all signs `1`, the numbers `δ i = l.lowerCount Eq i` of the `j` with
`l j < l i` run through `0, …, n - 1`, so their Vandermonde product, taken in the order of `l`, is
`∏_{i < n} i !`. -/
lemma New.HCParam.prod_prod_lowerCount_sub {n : Type} [Fintype n] [DecidableEq n]
    {l : HCParam (1 : n → ℤˣ)} (hl : l.Injective) :
    ∏ i : n, ∏ j : n with l j < l i, ((l.lowerCount Eq i : ℂ) - l.lowerCount Eq j) =
      ∏ i ∈ range (Fintype.card n), (i ! : ℂ) := by
  obtain ⟨e, he⟩ := exists_equiv_fin_lt_iff hl
  have h_map (a : Fin (Fintype.card n)) :
      ({b | l b < l (e a)} : Finset n) = (Iio a).map e.toEmbedding := by
    ext b
    obtain ⟨c, rfl⟩ := e.surjective b
    simp [he]
  have h_count (a : Fin (Fintype.card n)) : l.lowerCount Eq (e a) = (a : ℤ) := by
    simp [lowerCount, h_map]
  have h_factorial (a : ℕ) : ∏ k ∈ range a, ((a : ℂ) - k) = a ! := by
    rw [prod_range_natCast_sub, ← descFactorial_eq_prod_range, descFactorial_self]
  calc _ = ∏ a : Fin (Fintype.card n), ∏ k ∈ range (a : ℕ), ((a : ℂ) - k) := by
        simp [← e.prod_comp, h_map, h_count, ← Iio_eq_range, ← Fin.map_valEmbedding_Iio]
    _ = _ := by simp only [h_factorial, Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ (i ! : ℂ))]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
/-- Weyl's dimension formula for `U(n)`. Let `l = 2λ` be a parameter for all signs `1` (distinct
entries congruent to `n - 1` mod 2; the gap `h` plays no role as all signs are equal) and
`Λ = l.lowestKType = λ - ρ`. The number `Λ.kTypeNormSq` is the integral of `|New.weightMinors Λ k|²`
over `U(n)` for Haar measure of mass one, and `New.weylDimensionPoly l` is the product of `λᵢ - λⱼ`
over `λⱼ < λᵢ`, divided by `∏_{i < n} i !`. The statement says that the inverse of the former is
the latter. By Schur orthogonality the inverse of the former is the dimension of the representation
of highest weight `Λ` (compare `New.IsHCParam.prod_formalDegree`). -/
lemma New.weyl_dimension_formula {n : Type} [Fintype n] [DecidableEq n] {l : HCParam (1 : n → ℤˣ)}
    {h : ℕ} (h_gap : l.HasGap h) :
    l.lowestKType.kTypeNormSq⁻¹ = weylDimensionPoly l := by
  -- Compare the denominator formula and the character formula for `Λ` along two one-parameter
  -- subgroups of the torus, divide by a power of `t` and let `t → 0`.
  -- `δ i` counts the `j` with `l j < l i`; `x a t` has entries `exp (I t aᵢ)`; `χ ν` is the
  -- character on the torus; `Δ` is the Vandermonde product in the order of `l`.
  set Λ : HCParam (1 : n → ℤˣ) := l.lowestKType
  let δ : n → ℤ := l.lowerCount Eq
  let x (a : n → ℤ) (t : ℝ) (i : n) : Circle := Circle.exp t ^ a i
  let χ (ν : HCParam (1 : n → ℤˣ)) (y : n → Circle) : ℂ := ν.kTypeChar (diagTorusK y)
  let Δ (a : n → ℂ) : ℂ := ∏ i, ∏ j with l j < l i, (a i - a j)
  have hΔ (y : n → Circle) : Orbital.torusEval y (l.rootProd Eq) = Δ (y ·) := by
    simp [torusEval_rootProd, Δ]
  -- Both sides are the determinant of `exp (I t (Λ + δ)ᵢ δⱼ)`, one of them transposed: the left by
  -- the denominator formula, the right by the character formula.
  have h_swap (t : ℝ) : Δ (x (Λ + δ) t ·) = Δ (x δ t ·) * χ Λ (x δ t) := by
    rw [← hΔ, ← hΔ,
      torusEval_rootProd_mul_kTypeChar_eq_alternant h_gap.injective h_gap.isKDominant_lowestKType,
      weyl_denominator h_gap.injective, torusEval_alternant, torusEval_alternant, ← det_transpose]
    simp [x, δ, Λ, transpose, zpow_comm]
  -- Each factor `exp (I t aᵢ) - exp (I t aⱼ)`, divided by `t`, tends to `I (aᵢ - aⱼ)`.
  have h_lim (a : n → ℤ) : Filter.Tendsto (fun t : ℝ ↦ (∏ i, (t : ℂ) ^ #{j | l j < l i})⁻¹ *
      Δ (x a t ·)) (nhdsWithin 0 {0}ᶜ) (nhds ((∏ i, Complex.I ^ #{j | l j < l i}) * Δ (a ·))) := by
    have h_exp (c : ℂ) : HasDerivAt (fun t : ℝ ↦ cexp (c * (t * Complex.I))) (c * Complex.I) 0 := by
      simpa using (((hasDerivAt_id 0).ofReal_comp.mul_const Complex.I).const_mul c).cexp
    have h_slope (i j : n) : Filter.Tendsto (fun t : ℝ ↦ (t : ℂ)⁻¹ * (x a t i - x a t j))
        (nhdsWithin 0 {0}ᶜ) (nhds (Complex.I * (a i - a j))) := by
      simpa [exp_int_mul, mul_comm _ Complex.I, ← mul_sub, x] using
        ((h_exp (a i)).sub (h_exp (a j))).tendsto_slope_zero
    simpa [Δ, prod_mul_distrib] using
      tendsto_finsetProd univ fun i _ ↦ tendsto_finsetProd {j | l j < l i} fun j _ ↦ h_slope i j
  -- The limits of the two sides of `h_swap` agree, and at the identity `χ Λ 1 = Λ.kTypeNormSq⁻¹`.
  have h_cont : Continuous fun t ↦ χ Λ (x δ t) := by fun_prop
  have h_scaled : Filter.Tendsto
      (fun t : ℝ ↦ (∏ i, (t : ℂ) ^ #{j | l j < l i})⁻¹ * Δ (x δ t ·) * χ Λ (x δ t))
      (nhdsWithin 0 {0}ᶜ) (nhds ((∏ i, Complex.I ^ #{j | l j < l i}) * Δ ((Λ + δ) ·))) :=
    (h_lim (Λ + δ)).congr fun t ↦ by rw [h_swap, mul_assoc]
  have h_limit_eq : Δ (δ ·) * (Λ.kTypeNormSq : ℂ)⁻¹ = Δ ((Λ + δ) ·) := by
    have h_id : χ Λ (x δ 0) = (Λ.kTypeNormSq : ℂ)⁻¹ := by
      simp [χ, kTypeChar, x, diagTorusK, diagTorus]
    -- cancel the powers of `I`
    simpa [h_id, prod_eq_zero_iff, mul_assoc] using
      tendsto_nhds_unique ((h_lim δ).mul h_cont.continuousWithinAt) h_scaled
  -- `Λ + δ` differs from `l / 2` by the constant `(n - 1) / 2`.
  have h_shift (i : n) : (2 * (Λ + δ) i + 1 : ℂ) = l i + Fintype.card n := by
    have h_two : 2 * Λ i = l i - (#{j | l j < l i} - #{j | l i < l j}) := by
      simpa [twoRho] using two_mul_lowestKType h_gap i
    norm_cast
    rw [Pi.add_apply, show δ i = #{j | l j < l i} by simp [δ, lowerCount],
      ← card_lt_add_card_gt_add_one h_gap.injective i]
    omega
  -- `δ` is a permutation of `0, …, n - 1`, so its Vandermonde product is `∏ i !`.
  rw [weylDimensionPoly, eq_div_iff (by positivity), ← ofReal_inj, mul_comm]
  push_cast [← HCParam.prod_prod_lowerCount_sub h_gap.injective]
  refine h_limit_eq.trans (prod_congr rfl fun i _ ↦ prod_congr rfl fun j _ ↦ ?_)
  linear_combination (h_shift i - h_shift j) / 2

end WeylDimension

/-!
## Weyl's character formula at regular elements via Vandermonde determinants

* `New.Variety.det_zpow_add`: a common integer shift of the exponents comes out of a generalised
  Vandermonde determinant in nonzero numbers.
* `New.Variety.trace_weylRep`: the character formula at elements with distinct eigenvalues.
-/

section WeylTrace

open Matrix Finset

namespace New.Variety

variable {a : ℕ} {ι : Type} [Fintype ι]

/-- If the `r i` are nonzero, a common integer shift `d` of the exponents comes out of
`det (r i ^ (d + k j))` as the factor `(∏ r i) ^ d`. -/
lemma det_zpow_add {r : Fin a → ℂ} (h_ne : ∀ i : Fin a, r i ≠ 0) (d : ℤ) (k : Fin a → ℤ) :
    (of fun i j : Fin a ↦ r i ^ (d + k j)).det =
      univ.prod r ^ d * (of fun i j : Fin a ↦ r i ^ k j).det := by
  -- Row `i` has the factor `r i ^ d`.
  simp only [zpow_add₀ (h_ne _), ← prod_zpow]
  exact det_mul_column _ _

/-- Weyl's character formula: if each g_v in GL_a(ℂ) has distinct eigenvalues x_{v,i}, the trace of
`New.weylRep κ e` (the Schur module of κ twisted by the powers e_v of the determinants) at g times
∏_v det(x_{v,i}^j) equals ∏_v det(x_{v,i}^(e_v + λ_{v,a−1−j} + j)), with 0 ≤ i, j < a, λ_{v,k} the
sum of the κ v h for k < h < a (`rankAt fun _ ↦ Fin a` gives every block the size a), and λ the
weight `New.diagramWeight` of κ.

Known result: Weyl's character formula for GL_a. -/
lemma trace_weylRep [DecidableEq ι] (κ : ι → ℕ → ℕ) (e : ι → ℤ) {g : ι → GL (Fin a) ℂ}
    {x : ι → Fin a ↪ ℂ} (hg : ∀ (v : ι) (i : Fin a), (g v).val.charpoly.IsRoot (x v i)) :
    (weylRep κ e g).trace * ∏ v : ι, (vandermonde (x v)).det =
      ∏ v : ι, (of fun i j : Fin a ↦
        x v i ^ (e v + ↑(diagramWeight (rankAt fun _ : ι ↦ Fin a) κ (v, j.rev) + j))).det := by
  -- diagonalise each `g v`; the trace is invariant under conjugation
  have h_eigen (v : ι) : ∃ h : GL (Fin a) ℂ, h.1 * diagonal (x v) = (g v).1 * h.1 :=
    isConj_diagonal_of_isRoot_charpoly (hg v)
  choose h h_diag using h_eigen
  have h_trace : (weylRep κ e g).trace =
      (∏ v : ι, (univ.prod (x v)) ^ e v) * (schur κ fun v ↦ diagonal (x v)).trace := by
    have h_conj (v : ι) : ((h⁻¹ * (g * h)) v).1 = diagonal (x v) := by simp [← h_diag]
    rw [← mul_inv_cancel_right g h, map_mul, trace_mul_comm, ← map_mul]
    generalize h⁻¹ * (g * h) = g' at h_conj ⊢
    simp [weylRep, Units.smul_def, h_conj]
  -- the formula for diagonal matrices, and the shift by `e v` in each determinant
  have h_diagonal : (schur κ fun v : ι ↦ diagonal (x v)).trace * ∏ v : ι, (vandermonde (x v)).det =
      ∏ v : ι, (of fun i j : Fin a ↦
        x v i ^ (diagramWeight (rankAt fun _ : ι ↦ Fin a) κ (v, j.rev) + j)).det :=
    weyl_character (fun _ : ι ↦ Equiv.refl (Fin a)) _
  rw [h_trace, mul_assoc, h_diagonal, ← prod_mul_distrib]
  refine prod_congr rfl fun v _ ↦ ?_
  rw [det_zpow_add fun i ↦
    spectrum.ne_zero_of_mem_of_unit (mem_spectrum_of_isRoot_charpoly (hg v i))]
  norm_cast

end New.Variety

end WeylTrace

end
