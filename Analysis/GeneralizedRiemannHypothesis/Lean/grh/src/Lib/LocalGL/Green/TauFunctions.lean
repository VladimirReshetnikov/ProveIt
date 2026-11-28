import Lib.LocalGL.Green.CuspidalFunctions

/-!
# Green's characters of GL_n over a finite field: θ_x, τ_P, labels and their degrees

This file studies Green's characters of `GL n k` over a finite field `k` that are attached to
squarefree polynomials. These characters live in `New.Hall k`, the complex-valued functions on
similarity classes of square matrices of all sizes, with parabolic induction as product. A faithful
character `T` of the algebraic closure `K` gives characters `θ_x = New.thetaChar T Q x`. For a label
`c`, they also give the product `Ξ_c = New.labelChar T c` of the `τ_P` over the irreducible factors
`P` of `c`. The file proves the symmetries of `θ_x`. It shows that the `τ_P` are cuspidal and
orthonormal and do not depend on the chosen root.

## Main definitions and results

* `New.faithfulChar`, `New.thetaChar`: a faithful character `T` of the algebraic closure, and the
  power `θ_x` of `T` attached to an element `x` of the subfield with `Q` elements.
* `New.greenTau`, `New.labelChar`: the function `τ_P` of an irreducible `P`, and the product `Ξ_c`
  of the `τ_P` over the irreducible factors of `c`.
* `New.IsLabel`: labels of degree `r`, which are monic squarefree polynomials with nonzero constant
  term.
* `New.charName`: for `T` faithful, the isomorphism χ ↦ x_χ from the multiplicative characters of
  the finite field k onto k^×; its inverse sends a unit a to the restriction of θ_a to k.
* `New.rankInner_greenTau`: the `τ_P` are orthonormal.
* `New.labelChar_degree_bounds`: let `q = |k|`. Let `c` be a label of degree `r`
  (`New.IsLabel r c`), with `r = card n`. Let `Ξ = New.labelChar T c` on `GL n k`. Then the real
  part of `Ξ(1)` is non-negative. Also `Ξ(1) conj Ξ(1) / |GL n k|` is at least
  `(1 - r / q) / q ^ r`.

Notions from other files:
* `New.Hall.greenCuspidal`: The class function C_η = (β_η·μ) ∗ 𝟙: the pointwise product of the
  eigenvalue sum β_η with the inverse μ (`moebius`) of 𝟙 (for any F, `F.mulMoebius` is the pointwise
  product F·μ), multiplied in the induction product by the constant function 𝟙.
* `New.Hall.brauerLift`: The class function β_η sending an endomorphism to the sum of η over the
  roots in K of its characteristic polynomial, counted with multiplicity.
* `New.Hall.evalGL`: For a complex function F on similarity classes and an invertible matrix g in
  `GL n k`, indexed by a finite type n, the value of F at the class of the endomorphism of `n → k`
  given by g.
* `New.Hall.rankInner`: For n and complex functions F, H on similarity classes, the average over
  GL_n(k) of the conjugate of F times H.

## Relation to the literature

Known result: Green's characters of GL_n(F_q) and the parabolic-induction ring. Only cuspidal
characters and their products over squarefree polynomials are treated, named through a fixed
character of the algebraic closure, with cuspidality, orthonormality, independence of the chosen
root and a degree bound. Hall polynomials are not covered. Source: J. A. Green, The characters of
the finite general linear groups, Trans. AMS 80 (1955), Thms 2, 9, 12-14; for the ring on all
matrices, Z. Chen, arXiv 2408.06191, Prop. 3.2.
-/

noncomputable section

namespace New

/-!
## Green's characters of squarefree polynomials and their idempotents

Choices are made with `Classical.epsilon`.
-/

section LabelDefs

open Polynomial UniqueFactorizationMonoid Hall Real Function

attribute [local instance low] Fintype.ofFinite

section

variable (k : Type*) [Field k] [Finite k]
  {K : Type*} [Field K] [Algebra k K] (T : MulChar K ℂ)
  {n : Type _} [Fintype n] [DecidableEq n]
  (Q r : ℕ) (P c : k[X]) (χ : MulChar k ℂ)

/-- The finite set of monic polynomials of degree r over the finite field k. -/
def monicsOfDegree : Finset k[X] :=
  @Set.toFinset k[X] {c : k[X] | c.Monic ∧ c.natDegree = r}
    (Fintype.ofEquiv (Fin r → k) ((monicEquivDegreeLT r).trans (degreeLTEquiv k r).toEquiv).symm)

/-- A chosen injective multiplicative character from the algebraic closure of `k` to `ℂ`
(arbitrary if there is none). For finite `k` one exists (`New.exists_injective_mulChar`), so the
chosen character is injective (the instance `New.faithfulChar_injective`). -/
def faithfulChar : MulChar (AlgebraicClosure k) ℂ :=
  Classical.epsilon fun T : MulChar (AlgebraicClosure k) ℂ ↦ Injective T

/-- The field K is algebraically closed and the multiplicative character T : K → ℂ is injective,
so it embeds K^× in ℂ^×. -/
class IsFaithfulMulChar (K : Type*) [Field K] (T : outParam (MulChar K ℂ)) :
    Prop extends IsAlgClosed K where
  /-- The character T is injective. -/
  injective : Injective T

variable {k}

/-- A chosen natural number `j` with `T x = exp (2πi / (Q - 1)) ^ j` (arbitrary if there is
none). -/
def thetaExponent (x : K) : ℕ :=
  Classical.epsilon fun j : ℕ ↦ T x = Complex.exp (2 * π * Complex.I / (Q - 1 : ℕ)) ^ j

/-- Let `T` be a multiplicative character `K → ℂ`. Suppose `2 ≤ Q` and `x` is a `(Q - 1)`-th root of
unity. Then `T x = exp (2πi / (Q - 1)) ^ thetaExponent T Q x`, where `thetaExponent T Q x` is a
chosen natural number `j` with `T x = exp (2πi / (Q - 1)) ^ j` (arbitrary if none exists). So such
an exponent exists. -/
theorem apply_eq_exp_pow_thetaExponent {Q : ℕ} {x : K} (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) :
    T x = Complex.exp (2 * π * Complex.I / (Q - 1 : ℕ)) ^ thetaExponent T Q x := by
  -- `T x` is a `(Q - 1)`-th root of unity in `ℂ`, so a power of the primitive one.
  have hQ_sub_ne : NeZero (Q - 1) := ⟨Nat.sub_ne_zero_of_lt hQ⟩
  have h_root : T x ^ (Q - 1) = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨j, -, hj⟩ :=
    (Complex.isPrimitiveRoot_exp (Q - 1) (NeZero.ne _)).eq_pow_of_pow_eq_one h_root
  exact Classical.epsilon_spec (p := fun j : ℕ ↦ T x = _ ^ j) ⟨j, hj.symm⟩

/-- The character `θ_x = T ^ j` of `K`, where `j = thetaExponent T Q x`. -/
def thetaChar (x : K) : MulChar K ℂ := T ^ thetaExponent T Q x

variable (K) in
/-- A chosen root of `P` in `K` (arbitrary if there is none). -/
def chosenRoot : K := Classical.epsilon fun x : K ↦ P.aeval x = 0

omit [Finite k] in
theorem aeval_chosenRoot {P : k[X]} {x : K} (hx : P.aeval x = 0) :
    P.aeval (chosenRoot K P) = 0 :=
  Classical.epsilon_spec (p := fun x : K ↦ P.aeval x = 0) ⟨x, hx⟩

omit [Finite k] in
theorem chosenRoot_X_sub_C (a : k) : chosenRoot K (X - C a) = algebraMap k K a := by
  have h_root : (X - C a).aeval (chosenRoot K (X - C a)) = 0 :=
    aeval_chosenRoot (x := algebraMap k K a) (by simp)
  simpa [sub_eq_zero] using h_root

/-- Green's class function `τ_P`: `(-1) ^ d` times the rank `d` part of `greenCuspidal k θ_x`,
where `d = deg P`, `x = chosenRoot K P` and `θ_x` is formed with `Q = |k| ^ d`. -/
def greenTau : Hall k :=
  (-1 : ℂ) ^ P.natDegree •
    (greenCuspidal k (thetaChar T (Nat.card k ^ P.natDegree) (chosenRoot K P))).rankPart
      P.natDegree

open scoped Classical in
/-- The multiplicative map c ↦ Ξ_c: the product, by parabolic induction, of τ_P over the monic
irreducible factors P of c with multiplicity; Ξ_0 = 0. -/
def labelChar : k[X] →* Hall k where
  toFun c := if c = 0 then 0 else ((normalizedFactors c).map (greenTau T)).prod
  map_one' := by simp
  map_mul' c d := by
    by_cases hc : c = 0
    · simp [hc]
    by_cases hd : d = 0
    · simp [hd]
    simp [hc, hd, normalizedFactors_mul hc hd]

/-- `c` is a label of degree `r`: a monic squarefree polynomial over `k` of degree `r` with nonzero
constant term. -/
def IsLabel : Prop := c.Monic ∧ Squarefree c ∧ c.natDegree = r ∧ c.coeff 0 ≠ 0

/-- The class function χ∘det on endomorphisms of every dimension, written through the constant
term of the characteristic polynomial. -/
def detChar : Hall k := fun c : SimClass k ↦ χ ((-1) ^ c.dim * c.charpoly.coeff 0)

open scoped Classical in
/-- For a vector `l : n → k`, the element ∑ χ(det h)⁻¹ h of ℂ[GL_n(k)], summed over the invertible
h of the form 1 + u lᵀ with u a column vector. -/
def hyperplaneSum (l : n → k) : MonoidAlgebra ℂ (GL n k) :=
  groupAlgElem fun h : GL n k ↦
    if ∃ u : n → k, h.val = 1 + Matrix.vecMulVec u l then χ⁻¹ h.val.det else 0

variable (n)

open scoped Classical in
/-- The element e_c = ∑ (Ξ_c(1)/|G|)·conj Ξ_c(g)·g of ℂ[G], G = GL_n(k), Ξ_c formed with
`New.faithfulChar`, if c is a label of degree |n|; zero otherwise. -/
def labelIdem : MonoidAlgebra ℂ (GL n k) :=
  let Ξ := (labelChar (faithfulChar k) c).evalGL (n := n)
  if IsLabel (Fintype.card n) c then
    groupAlgElem fun g ↦ Ξ 1 / Nat.card (GL n k) * starRingEnd ℂ (Ξ g)
  else
    0

end

end LabelDefs

/-!
## The characters θ_x and the name x_χ of a character of k^×

Fix a multiplicative character `T : K → ℂ`. For x with x^(Q−1) = 1, `thetaChar T Q x` is the
character θ_x = T^e, where T(x) = exp(2πi/(Q−1))^e.

* `New.thetaChar_apply_pow`: the key symmetry, θ_x(z^m) = (T^a)(x) when T(z) = exp(2πi/N)^a and
  N = (Q − 1)m ≠ 0. It gives `New.thetaChar_mul` (θ_{xy} = θ_x θ_y on (Q−1)-th roots of unity) and
  `New.thetaChar_eq_apply_norm_pow` (the change from Q to Q^r is composition with a norm).
-/

section ThetaCharacters

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] (T : MulChar K ℂ)
  {Q Q' m : ℕ} {x y z : K}

open Complex MulChar Finite Nat Units

/-- For `2 ≤ Q` and a `(Q - 1)`-th root of unity `x`, the character `thetaChar T Q x` is `T ^ e`
for an exponent `e` with `T x = exp (2πi / (Q - 1)) ^ e`. -/
lemma exists_thetaChar_eq_pow (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) :
    ∃ e : ℕ, thetaChar T Q x = T ^ e ∧ T x = exp (2 * Real.pi * I / (Q - 1 : ℕ)) ^ e :=
  ⟨thetaExponent T Q x, rfl, apply_eq_exp_pow_thetaExponent T hQ hx⟩

/-- Let `T` be a multiplicative character of the field `K`, and let `θ_x = thetaChar T Q x` be the
character `T ^ j` of `K`, where `j = thetaExponent T Q x`.
Suppose `Q ≥ 2`, `N ≠ 0`, `N = (Q − 1)m` and `x^{Q−1} = 1`. If `z ∈ K`
satisfies `T(z) = exp(2πi/N)^a`, then `θ_x(z^m) = T(x)^a`. -/
lemma thetaChar_apply_pow (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) {a N : ℕ} (hN : N ≠ 0)
    (hN_eq : N = (Q - 1) * m) (hTz : T z = exp (2 * Real.pi * I / N) ^ a) :
    thetaChar T Q x (z ^ m) = (T ^ a) x := by
  -- Write `thetaChar T Q x = T ^ e` with `T x = exp (2πi / (Q - 1)) ^ e`. The left side is
  -- `exp (2πi / N) ^ (a * e * m)`, the right side is `exp (2πi / (Q - 1)) ^ (e * a)`.
  obtain ⟨x, rfl⟩ : IsUnit x := IsUnit.of_pow_eq_one hx (by lia)
  obtain ⟨z, rfl⟩ : IsUnit z := T.apply_ne_zero_iff.mp (hTz.trans_ne (by simp))
  obtain ⟨e, hθ, hTx⟩ := exists_thetaChar_eq_pow T hQ hx
  have hm_ne : (m : ℂ) ≠ 0 := mod_cast right_ne_zero_of_mul (hN_eq.symm.trans_ne hN)
  rw [hθ, map_pow, pow_apply_coe, pow_apply_coe, hTz, hTx, hN_eq]
  -- The exponents agree: the factor `m` cancels against the one in `N = (Q - 1) * m`.
  have h_exponent :
      (m : ℂ) * (e * (a * (2 * Real.pi * I / ((Q - 1 : ℕ) * m)))) =
        a * (e * (2 * Real.pi * I / (Q - 1 : ℕ))) := by
    field_simp
  simp only [← exp_nsmul, nsmul_eq_mul, cast_mul, h_exponent]

/-- Let Q ≥ 2 and let x, y, z in K satisfy x^(Q−1) = y^(Q−1) = z^(Q−1) = 1. Then
θ_{xy}(z) = θ_x(z)·θ_y(z), where all three characters are formed with Q. -/
lemma thetaChar_mul (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (hy : y ^ (Q - 1) = 1)
    (hz : z ^ (Q - 1) = 1) :
    thetaChar T Q (x * y) z = thetaChar T Q x z * thetaChar T Q y z := by
  -- `thetaChar` is symmetric on `(Q - 1)`-th roots of unity, and multiplicative in its last
  -- argument.
  obtain ⟨e, hθ, hTz⟩ := exists_thetaChar_eq_pow T hQ hz
  have h_symm {w : K} (hw : w ^ (Q - 1) = 1) : thetaChar T Q w z = thetaChar T Q z w := by
    simpa [hθ] using thetaChar_apply_pow T hQ hw (by lia) (mul_one _).symm hTz
  rw [h_symm hx, h_symm hy, h_symm (by rw [mul_pow, hx, hy, one_mul]), map_mul]

/-- Change of Q. Let `T` be a multiplicative character of the field `K`, and let θ_x, formed with
Q, be the character T^j of `K` with j = `thetaExponent T Q x`.
Let Q ≥ 2, Q' = Q^r ≥ 2, x^(Q−1) = 1, y = x^a and z^(Q'−1) = 1. Then θ_y(z), formed with Q', equals
θ_x(z^(1 + Q + … + Q^(r−1)))^a, formed with Q; the power of z is its norm from the field with Q'
elements to the field with Q elements. -/
lemma thetaChar_eq_apply_norm_pow (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) {r a : ℕ} (hQ' : 2 ≤ Q')
    (hr : Q' = Q ^ r) (hxy : x ^ a = y) (hz : z ^ (Q' - 1) = 1) :
    thetaChar T Q' y z = thetaChar T Q x (z ^ ∑ i ∈ Finset.range r, Q ^ i) ^ a := by
  -- Write `T z = exp (2πi / (Q' - 1)) ^ e`. By `thetaChar_apply_pow` the left side is `(T ^ e) y`
  -- and the right side is `(T ^ e) x ^ a`, since `Q ^ r - 1 = (Q - 1) * ∑ i < r, Q ^ i`.
  obtain ⟨e, -, hTz⟩ := exists_thetaChar_eq_pow T hQ' hz
  have hQ'_sub_ne : Q' - 1 ≠ 0 := by lia
  have h_geom : Q' - 1 = (Q - 1) * ∑ i ∈ .range r, Q ^ i := by
    rw [hr, mul_comm, geom_sum_mul_of_one_le (by lia)]
  have hy : y ^ (Q' - 1) = 1 := by simp [← hxy, pow_right_comm x a, h_geom, pow_mul, hx]
  have h_left : thetaChar T Q' y z = (T ^ e) y := by
    simpa using thetaChar_apply_pow T hQ' hy hQ'_sub_ne (mul_one _).symm hTz
  rw [h_left, thetaChar_apply_pow T hQ hx hQ'_sub_ne h_geom hTz, ← hxy, map_pow]

variable [IsFaithfulMulChar K T]

/-- Let `T` be faithful (`New.IsFaithfulMulChar`) and `a` a unit of the finite field `k`. If θ_a,
formed with Q = |k|, is trivial on the units of `k`, then `a = 1`. -/
lemma eq_one_of_thetaChar_algebraMap_eq_one {a : kˣ}
    (h_theta_one :
      ∀ y : kˣ, thetaChar T (Nat.card k) (algebraMap k K a) (algebraMap k K y) = 1) :
    a = 1 := by
  obtain ⟨e, hθ, hTa⟩ := exists_thetaChar_eq_pow T one_lt_card (algebraMap_pow_card_pred_eq_one a)
  have h_one {x : k} (hx : T (algebraMap k K x) = 1) : x = 1 := by
    simpa [map_eq_one_iff T IsFaithfulMulChar.injective] using hx
  -- `T y ^ e = 1` gives `y ^ e = 1` for all units `y`, so the order of the cyclic group `kˣ`
  -- divides `e`.
  have h_pow (y : kˣ) : y ^ e = 1 := by
    have hy : T ((Units.map (algebraMap k K : k →* K) y : Kˣ) : K) ^ e = 1 := by
      rw [← pow_apply_coe, ← hθ]
      exact h_theta_one y
    have hy_pow : T (algebraMap k K ↑(y ^ e)) = 1 := by simpa using hy
    exact val_eq_one.mp (h_one hy_pow)
  have h_dvd : Nat.card k - 1 ∣ e := by
    rw [← card_units, ← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one h_pow
  -- Hence `T a`, the `e`-th power of a root of unity of that order, is `1`.
  have h_prim :
      IsPrimitiveRoot (exp (2 * Real.pi * I / (Nat.card k - 1 : ℕ))) (Nat.card k - 1) :=
    isPrimitiveRoot_exp _ (sub_ne_zero_of_lt one_lt_card)
  rw [(h_prim.pow_eq_one_iff_dvd e).mpr h_dvd] at hTa
  exact val_eq_one.mp (h_one hTa)

/-- For `T` faithful (`New.IsFaithfulMulChar`), the group isomorphism χ ↦ x_χ from the
multiplicative characters of `k` to `kˣ`, inverse to a ↦ θ_a restricted to `k`, with θ_a formed
with Q = |k|. -/
noncomputable def charName : MulChar k ℂ ≃* kˣ :=
  -- `R a` is the restriction of θ_a to `k`.
  let R : kˣ →* MulChar k ℂ :=
    MonoidHom.mk'
      (fun a ↦ ⟨(thetaChar T (Nat.card k) (algebraMap k K a)).toMonoidHom.comp (algebraMap k K),
        by simp⟩)
      (fun a b ↦ MulChar.ext fun y ↦ by
        -- At `y`, this is θ_{ab} = θ_a θ_b on the (|k| - 1)-th roots of unity.
        show thetaChar T (Nat.card k) (algebraMap k K ↑(a * b)) (algebraMap k K y) =
          thetaChar T (Nat.card k) (algebraMap k K a) (algebraMap k K y) *
            thetaChar T (Nat.card k) (algebraMap k K b) (algebraMap k K y)
        simp [thetaChar_mul T one_lt_card, algebraMap_pow_card_pred_eq_one])
  MulEquiv.symm
    (MulEquiv.ofBijective R (by
      -- `R` is injective, and `kˣ` has as many elements as its character group.
      have h_inj : Function.Injective R :=
        (injective_iff_map_eq_one R).mpr fun a ha ↦
          eq_one_of_thetaChar_algebraMap_eq_one T fun y ↦
            -- `R a y` is by definition the value of θ_a at `y`.
            (DFunLike.congr_fun ha (y : k)).trans (MulChar.one_apply_coe y)
      exact h_inj.bijective_of_nat_card_le (card_eq_card_units_of_hasEnoughRootsOfUnity k ℂ).le))

/-- The inverse of `charName T` sends a unit `a` to the restriction of θ_a to `k`. -/
private lemma charName_symm_apply (a : kˣ) (y : k) :
    (charName T).symm a y = thetaChar T (Nat.card k) (algebraMap k K a) (algebraMap k K y) :=
  rfl

/-- Let `T` be faithful (`K` algebraically closed, `T : K → ℂ` injective), and let θ_a = T^j
(j = `thetaExponent`) be formed with Q = |k|. Let x_χ = `charName T χ` ∈ kˣ be the element attached
to a multiplicative character χ of `k` by inverting the isomorphism a ↦ θ_a restricted to `k`. Then
θ_{x_χ}(y) = χ(y) for all y ∈ k, so every χ is the restriction of θ_{x_χ} to `k`. -/
lemma thetaChar_charName (χ : MulChar k ℂ) (y : k) :
    thetaChar T (Nat.card k) (algebraMap k K (charName T χ)) (algebraMap k K y) = χ y := by
  rw [← charName_symm_apply, MulEquiv.symm_apply_apply]

variable {T}

lemma charName_pow_eq_one {χ : MulChar k ℂ} {M : ℕ} (hχ : χ ^ M = 1) :
    (charName T χ).val ^ M = (1 : k) := by
  simp [← val_pow_eq_pow_val, ← map_pow, hχ]

end ThetaCharacters

/-!
## Green's functions τ_P: cuspidality, orthonormality, independence of the root

Up to the sign `(-1)^d`, `τ_P` is the part of rank `d = deg P` of `New.Hall.greenCuspidal k θ_x`.
Here `x` is a chosen root of `P` in `K` and `Q = |k|^d`. `rankPart d` keeps rank `d`, and
`rankInner d` is the inner product on `GL_d(k)`.
-/

section GreenTau

open Polynomial Hall IsAlgClosed FiniteField LinearMap Finset minpoly Multiset Module
  UniqueFactorizationMonoid ComplexConjugate AdjoinRoot

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] {T : MulChar K ℂ} {P : k[X]}

/-- Let `T : K → ℂ` be any multiplicative character of a field `K` over the finite field `k`. For
`P` monic and irreducible over `k`, the label character `labelChar T P` (the parabolic-induction
product of Green's class functions over the monic irreducible factors) is the single function
`τ_P = greenTau T P`. -/
@[simp]
lemma labelChar_eq_greenTau (T : MulChar K ℂ) (hP : Irreducible P) (hP_monic : P.Monic) :
    labelChar T P = greenTau T P := by
  classical
  simp [labelChar, normalizedFactors_irreducible hP, hP_monic.normalize_eq_self, hP.ne_zero]

/-- Let `T` be any multiplicative character of the field `K` over `k`, and let P be any polynomial
over `k`, of degree d. Green's class function τ_P is (−1)^d times the rank d
part of `greenCuspidal k θ_x`, where x = `chosenRoot K P` and θ_x = T^j (j = `thetaExponent`) is
formed with Q = |k|^d. Then τ_P is cuspidal: its mean over block triangular matrices with given
diagonal blocks vanishes whenever both blocks have nonzero dimension.

This is the cuspidality assertion in the theorem of Green and Deligne–Lusztig on characters of GL_n
over a finite field attached to the Coxeter torus, for τ_P defined by Green's formula.
Irreducibility is not stated here. -/
lemma isCuspidal_greenTau : (greenTau T P).IsCuspidal := by
  -- In rank `P.natDegree` it is a multiple of the cuspidal `greenCuspidal`, in other ranks zero.
  intro a
  simp_intro b ha hb [blockAverage, greenTau]
  split
  · simpa [blockAverage] using isCuspidal_greenCuspidal _ a b ha hb
  · simp

lemma greenTau_eq_zero_of_dim_ne (c : SimClass k) (hc : c.dim ≠ P.natDegree) :
    greenTau T P c = 0 := by
  simp [hc, greenTau]

/-- If the endomorphism σ of L is y ↦ y^(q^i) with q = |k|, then the roots of σP in the
algebraically closed field K are the q^i-th powers of the roots of P, with multiplicity. -/
lemma aroots_map_frobenius_pow [IsAlgClosed K] {L : Type*} [Field L] [Algebra L K] {i : ℕ}
    (σ : L →+* L) (hσ : ∀ y : L, σ y = y ^ Nat.card k ^ i) (P : L[X]) :
    (P.map σ).aroots K = (P.aroots K).map fun z : K ↦ z ^ Nat.card k ^ i := by
  -- Apply `Splits.roots_map` to the `i`-th power of the Frobenius map of `K`, which extends `σ`.
  have h_fintype : Fintype k := Fintype.ofFinite k
  have h_map : (P.map σ).map (algebraMap L K) =
      (P.map (algebraMap L K)).map (frobeniusAlgHom k K ^ i).toRingHom := by
    aesop (add simp coe_frobeniusAlgHom)
  rw [aroots_def, aroots_def, h_map, (splits _).roots_map]
  exact Multiset.map_congr rfl fun y _ ↦ by simp [coe_frobeniusAlgHom]

/-- A root `x` of an irreducible `P` with `P(0) ≠ 0` is a `(Q - 1)`-th root of unity, where
`Q = |k| ^ deg P ≥ 2`. -/
lemma root_pow_card_pow_pred_eq_one (hP : Irreducible P) (hP_coeff : P.coeff 0 ≠ 0) {x : K}
    (hx : P.aeval x = 0) :
    x ^ (Nat.card k ^ P.natDegree - 1) = 1 ∧ 2 ≤ Nat.card k ^ P.natDegree := by
  have hQ : 2 ≤ Nat.card k ^ P.natDegree := Nat.one_lt_pow hP.natDegree_pos.ne' Finite.one_lt_card
  have hx0 : x ≠ 0 := fun h ↦ hP_coeff (by simpa [h, aeval_def] using hx)
  have h_fix : x ^ Nat.card k ^ P.natDegree = x :=
    (root_pow_card_pow_eq_self_iff hP hx).2 dvd_rfl
  exact ⟨(pow_pred_eq_one_iff hQ).mpr ⟨hx0, h_fix⟩, hQ⟩

/-- For `a ≠ 0`, in rank `deg P` (`rankPart` keeps the values on classes of dimension `deg P` and is
zero elsewhere), replacing the root `x` by `x ^ a` in `θ_x` has the same effect on
`New.Hall.greenCuspidal` as composing `θ_x` with the `a`-th power map. -/
lemma rankPart_greenCuspidal_pow (hP : Irreducible P) (hP_coeff : P.coeff 0 ≠ 0) {x : K}
    (hx : P.aeval x = 0) {a : ℕ} [NeZero a] :
    let d := P.natDegree
    (greenCuspidal k (thetaChar T (Nat.card k ^ d) (x ^ a))).rankPart d =
      (greenCuspidal k fun z : K ↦ thetaChar T (Nat.card k ^ d) x (z ^ a)).rankPart d := by
  -- On a class of dimension `P.natDegree` it suffices, by `greenCuspidal_simClassOf_eq_mul`, to
  -- compare the two functions at the `z` with `z ^ Q = z`, where `Q = Nat.card k ^ P.natDegree`.
  obtain ⟨hx_pow, hQ⟩ := root_pow_card_pow_pred_eq_one hP hP_coeff hx
  refine Hall.ext fun n g ↦ ite_congr rfl (fun hc ↦ ?_) fun _ ↦ rfl
  rw [dim_simClassOf] at hc
  show greenCuspidal k (thetaChar T (Nat.card k ^ P.natDegree) (x ^ a)) (simClassOf g) =
    greenCuspidal k (fun z : K ↦ thetaChar T (Nat.card k ^ P.natDegree) x (z ^ a)) (simClassOf g)
  refine (greenCuspidal_simClassOf_eq_mul (a := 1) _ _ fun z _ hz_fix ↦ ?_).trans (one_mul _)
  by_cases hz : z = 0
  · simp [hz, NeZero.ne, MulChar.map_zero]
  · -- By `thetaChar_eq_apply_norm_pow` with `r = 1`, both sides are the `a`-th power of
    -- `thetaChar T Q x z`.
    have hz_pow : z ^ (Nat.card k ^ P.natDegree - 1) = 1 :=
      (pow_pred_eq_one_iff hQ).mpr ⟨hz, by rwa [hc] at hz_fix⟩
    have h_theta : thetaChar T (Nat.card k ^ P.natDegree) (x ^ a) z =
        thetaChar T (Nat.card k ^ P.natDegree) x (z ^ a) := by
      simp [thetaChar_eq_apply_norm_pow T hQ hx_pow hQ (pow_one _).symm rfl hz_pow]
    rw [one_mul, h_theta]

variable [IsFaithfulMulChar K T]

/-- For irreducible `P` with `P.coeff 0 ≠ 0`, any root `x` of `P` may replace the chosen one in the
definition of `greenTau T P`.

This is a case of Green's independence of the cuspidal character from the chosen root, with the
class function defined by Green's formula rather than by Deligne–Lusztig induction. -/
lemma greenTau_eq (hP : Irreducible P) (h0 : P.coeff 0 ≠ 0) {x : K} (hx : P.aeval x = 0) :
    greenTau T P = (-1 : ℂ) ^ P.natDegree •
      (greenCuspidal k (thetaChar T (Nat.card k ^ P.natDegree) x)).rankPart P.natDegree := by
  -- The chosen root is a Frobenius conjugate `x ^ Nat.card k ^ i` of `x`, and Frobenius permutes
  -- the eigenvalues over which `brauerLift` sums.
  obtain ⟨i, -, hi⟩ : ∃ i < P.natDegree, x ^ Nat.card k ^ i = chosenRoot K P :=
    exists_pow_card_pow_eq_of_root hP hx (aeval_chosenRoot hx)
  have h_roots (c : SimClass k) :
      (c.charpoly.aroots K).map (fun z : K ↦ z ^ Nat.card k ^ i) = c.charpoly.aroots K := by
    have h_fintype : Fintype k := Fintype.ofFinite k
    rw [← aroots_map_frobenius_pow (.id k) (by simp [pow_card_pow]), c.charpoly.map_id]
  have h_brauer (η : K → ℂ) :
      brauerLift k (fun z : K ↦ η (z ^ Nat.card k ^ i)) = brauerLift k η := by
    funext c
    simpa [brauerLift] using congrArg (fun s ↦ (s.map η).sum) (h_roots c)
  simp_rw [greenTau, ← hi, rankPart_greenCuspidal_pow hP h0 hx, greenCuspidal, h_brauer]

open scoped Classical in
/-- Orthogonality of the multiplicative characters of a finite field `L`: the mean over `Lˣ` of
`conj χ · ξ` is `1` if `χ = ξ` and `0` otherwise. -/
private lemma finMean_conj_mul_eq_ite {L : Type*} [Field L] [Finite L] (χ ξ : MulChar L ℂ) :
    finMean (fun z : Lˣ ↦ conj (χ z) * ξ z) = if χ = ξ then 1 else 0 := by
  -- the sum over `Lˣ` of the character `χ⁻¹ ξ` is `|Lˣ|` if it is trivial and `0` otherwise
  have h_fintype : Fintype Lˣ := Fintype.ofFinite Lˣ
  have h_sum : ∑ z : Lˣ, ((χ⁻¹ * ξ).comp (Units.coeHom L)) z =
      ((if (χ⁻¹ * ξ).comp (Units.coeHom L) = 1 then Fintype.card Lˣ else 0 : ℕ) : ℂ) :=
    sum_hom_units ((χ⁻¹ * ξ).comp (Units.coeHom L))
  simpa [finMean_eq, field, ← χ.star_apply', ← inv_mul_eq_one (a := χ), Units.val_inj,
    MulChar.ext_iff, MonoidHom.ext_iff] using h_sum

/-- Let `L` be a finite extension of `k` with an embedding `φ` into `K`, and `q = |k|`. The roots in
`K` of the characteristic polynomial of multiplication by `u` on `L` are the conjugates
`φ(u) ^ q ^ i`, `i < [L : k]`. -/
private lemma aroots_charpoly_mulLeft {L : Type*} [Field L] [Finite L] [Algebra k L]
    [FiniteDimensional k L] (φ : L →ₐ[k] K) (u : L) :
    (mulLeft k u).charpoly.aroots K =
      Multiset.map (fun i : ℕ ↦ φ u ^ Nat.card k ^ i) (Multiset.range (finrank k L)) := by
  have h_pow : (mulLeft k u).charpoly = minpoly k u ^ (finrank k L / (minpoly k u).natDegree) :=
    charpoly_eq_pow_of_isNilpotent (irreducible (.of_finite k u)) (monic (.of_finite k u))
      (by simp [show aeval (mulLeft k u) (minpoly k u) = 0 from
        aeval_algHom k (Algebra.lmul k L) u])
  have h_root : Polynomial.aeval (φ u) (minpoly k u) = 0 := by simp [Polynomial.aeval_algHom_apply]
  rw [← (mulLeft k u).charpoly_natDegree, h_pow]
  exact (aroots_pow_eq_frobenius_orbit (irreducible (.of_finite k u)) h_root).left

open scoped Classical in
/-- Let `x` be a root of a monic irreducible `P` and let `S` be monic irreducible. Then `x` is a
root of `S`, and then a simple one, exactly when `P = S`: its multiplicity among the roots of `S`
in `K` is `1` if `P = S` and `0` otherwise. -/
private lemma count_aroots_eq_ite {S : k[X]} (hP : Irreducible P) (hm : P.Monic) {x : K}
    (hx : P.aeval x = 0) (hS : Irreducible S) (hSm : S.Monic) :
    (count x (S.aroots K) : ℂ) = if P = S then 1 else 0 := by
  have h_nodup : (S.aroots K).Nodup := nodup_roots (PerfectField.separable_of_irreducible hS).map
  have h_mem_iff : x ∈ S.aroots K ↔ P = S := by
    rw [mem_aroots, eq_of_irreducible_of_monic hP hx hm]
    simp [hS.ne_zero, eq_comm, eq_iff_aeval_eq_zero, hS, hSm]
  rw [count_eq_of_nodup h_nodup]
  simp [h_mem_iff]

open scoped Classical in
/-- Let `T` be a faithful multiplicative character of the algebraically closed field `K ⊇ k`
(`IsFaithfulMulChar`), and let `P` be monic irreducible with `P(0) ≠ 0`. Let `τ_P = greenTau T P` be
Green's class function: `(-1)^d` times the rank `d = deg P` part of `greenCuspidal k θ_x`, where `x`
is a chosen root of `P` in `K`. (a) For `S` monic irreducible with `S(0) ≠ 0`, the inner product of
`τ_P` and `τ_S` on `GL_{deg P}(k)` (the mean over the group of conj τ_P · τ_S) is `1` if `P = S` and
`0` otherwise. (b) If `P(1) ≠ 0`, then `New.Hall.skew` of `τ_P` against the constant function `1` in
rank `deg P` vanishes: for every class `a`, the average over `b ∈ GL_{deg P}(k)` of conj `τ_P(b)`
times the block average of `1` at `(a, b)` is zero. Here `1` is `constOne`, and its block average is
its mean over block triangular matrices with diagonal blocks `a`, `b`. -/
lemma rankInner_greenTau (hP : Irreducible P) (h0 : P.coeff 0 ≠ 0) (hm : P.Monic) :
    -- (a)
    (∀ S : k[X], Irreducible S → S.Monic → S.coeff 0 ≠ 0 →
      rankInner P.natDegree (greenTau T P) (greenTau T S) = if P = S then 1 else 0) ∧
    -- (b)
    (P.eval 1 ≠ 0 → skew P.natDegree (greenTau T P) constOne = 0) := by
  -- Let `L` have degree `deg P` over `k`. An irreducible `S` of that degree with `S.coeff 0 ≠ 0`
  -- has a root `j ξ`, for `ξ` a character of `L`, and `rankInner_greenCuspidal_mulMoebius` turns
  -- the inner products into means over `Lˣ`.
  have h_deg_ne : NeZero P.natDegree := .of_pos hP.natDegree_pos
  let L : Type := Extension k (ringChar k) P.natDegree
  let alg_LK : Algebra L K := (lift : L →ₐ[k] K).toAlgebra
  have h_deg : P.natDegree = finrank k L := (finrank_extension ..).symm
  let j (χ : MulChar L ℂ) : K := algebraMap L K (charName T χ).val
  let θ (χ : MulChar L ℂ) : MulChar K ℂ := thetaChar T (.card L) (j χ)
  have h_root {S : k[X]} (hS : Irreducible S) (hS0 : S.coeff 0 ≠ 0)
      (hS_deg : S.natDegree = finrank k L) : ∃ ξ : MulChar L ℂ, S.aeval (j ξ) = 0 := by
    have h_fact : Fact (Irreducible S) := ⟨hS⟩
    obtain ⟨φ⟩ : Nonempty (AdjoinRoot S →ₐ[k] L) :=
      nonempty_algHom_of_finrank_dvd (finrank_quotient_span_eq_natDegree.trans hS_deg).dvd
    have hy : S.aeval (φ (.root S)) = 0 := AdjoinRoot.aeval_algHom_eq_zero S φ
    have hy0 : φ (.root S) ≠ 0 := fun h ↦ hS0 (by simpa [h, aeval_def] using hy)
    exact ⟨(charName T).symm (.mk0 _ hy0), by simp [j, hy]⟩
  obtain ⟨χ, hχ⟩ := h_root hP h0 h_deg
  -- Orthogonality of the characters of `Lˣ`.
  have h_orth (ξ : MulChar L ℂ) :
      finMean (fun z : Lˣ ↦ conj (χ z) * ξ z) = if j χ = j ξ then 1 else 0 := by
    have h_j_iff : j χ = j ξ ↔ χ = ξ := by
      simp only [j, (algebraMap L K).injective.eq_iff, Units.val_inj, EmbeddingLike.apply_eq_iff_eq]
    simp only [finMean_conj_mul_eq_ite, h_j_iff]
  -- `greenCuspidal k (θ χ)` is cuspidal, so pairing with it obeys the Leibniz rule on the product
  -- `B.mulMoebius * constOne` (`rankInner_mul_of_isCuspidal`).
  have h_pair (B : Hall k) :
      rankInner (finrank k L) (greenCuspidal k (θ χ)) (B.mulMoebius * constOne) =
        finMean (fun z : Lˣ ↦ conj (θ χ (algebraMap L K z)) * B (simClassOf (mulLeft k z.val))) *
            rankInner 0 (constOne : Hall k) constOne +
          rankInner 0 constOne B.mulMoebius *
            rankInner (finrank k L) (greenCuspidal k (θ χ)) constOne := by
    simp [rankInner_mul_of_isCuspidal (isCuspidal_greenCuspidal _) finrank_pos.ne',
      rankInner_greenCuspidal_mulMoebius _ (IsScalarTower.toAlgHom k L K)]
  rw [greenTau_eq hP h0 hχ, h_deg, ← natCard_eq_pow_finrank]
  refine ⟨fun S hS hSm hS0 ↦ ?_, fun h1 ↦ ?_⟩
  · obtain hS_deg | hS_deg := ne_or_eq S.natDegree (finrank k L)
    · -- `greenTau T S` lives in another rank.
      simp [ne_of_apply_ne natDegree (h_deg.trans_ne hS_deg.symm), hS_deg.symm, greenTau, rankInner]
    obtain ⟨ξ, hξ⟩ := h_root hS hS0 hS_deg
    -- The eigenvalues of multiplication by `u` are the conjugates of `u`.
    have h_eigen (u : L) : (mulLeft k u).charpoly.aroots K =
        .map (fun i : ℕ ↦ algebraMap L K u ^ Nat.card k ^ i) (.range (finrank k L)) :=
      aroots_charpoly_mulLeft (lift : L →ₐ[k] K) u
    -- Take `B = brauerLift k (θ ξ)` in `h_pair`. It vanishes in rank `0`, so the second term drops;
    -- in the first, `θ χ` and `θ ξ` restrict to `χ` and `ξ` on `L` (`thetaChar_charName`), and
    -- `h_eigen`, `h_orth` give the number of `i` with `j χ = j ξ ^ q ^ i`, `q = Nat.card k`.
    rw [← count_aroots_eq_ite hP hm hχ hS hSm, greenTau_eq hS hS0 hξ]
    -- The two signs `(-1) ^ deg P` cancel.
    have h_left :
        rankInner (finrank k L)
            ((-1 : ℂ) ^ finrank k L • rankPart (finrank k L) (greenCuspidal k (θ χ)))
            ((-1 : ℂ) ^ S.natDegree • rankPart S.natDegree
              (greenCuspidal k (thetaChar T (Nat.card k ^ S.natDegree) (j ξ)))) =
          rankInner (finrank k L) (greenCuspidal k (θ χ))
            ((brauerLift k (θ ξ)).mulMoebius * constOne) := by
      have h_sign : (-1 : ℂ) ^ finrank k L * (-1) ^ finrank k L = 1 := by simp [← mul_pow]
      simp [hS_deg, ← natCard_eq_pow_finrank, rankInner, θ, greenCuspidal, ← mul_assoc]
      simp_rw [mul_right_comm ((-1 : ℂ) ^ finrank k L) _ ((-1 : ℂ) ^ finrank k L), h_sign, one_mul]
    have h_second : rankInner 0 constOne (brauerLift k (θ ξ)).mulMoebius = 0 := by
      simp [mulMoebius, brauerLift, rankInner, charpoly_monic, eq_one_of_monic_natDegree_zero,
        charpoly_natDegree]
    -- the mean counts the `i < deg S` with `j χ = j ξ ^ q ^ i`: the roots of `S` equal to `j χ`
    have h_first :
        finMean (fun z : Lˣ ↦ conj (θ χ (algebraMap L K z)) *
            brauerLift k (θ ξ) (simClassOf (mulLeft k z.val))) =
          count (j χ) (S.aroots K) := by
      simp [h_eigen, aroots_eq_frobenius_orbit hS hξ, hS_deg, h_orth, brauerLift, j, θ, mul_sum,
        ← range_val, finMean_sum, ← ξ.pow_apply_coe, count_map, thetaChar_charName,
        Finset.card_def, Finset.filter_val]
    have h_rank_zero : rankInner 0 (constOne : Hall k) constOne = 1 := by simp [rankInner]
    rw [h_left, h_pair, h_first, h_second, h_rank_zero, mul_one, zero_mul, add_zero]
  · -- For `B = constOne` the left side of `h_pair` vanishes by `moebius_mul_constOne`, and so does
    -- the mean of `χ`, which is not trivial since `P` does not vanish at `1`.
    have h_ne : j χ ≠ j 1 := fun h_eq ↦ h1 (by simpa [h_eq, j, aeval_def] using hχ)
    have h_mean : finMean (fun z : Lˣ ↦ conj (χ z)) = 0 := by simpa [h_ne] using h_orth 1
    have h_left :
        rankInner (finrank k L) (greenCuspidal k (θ χ)) (constOne.mulMoebius * constOne) = 0 := by
      simp [mulMoebius.eq_unfold, moebius_mul_constOne, rankInner, one_apply, finrank_pos.ne']
    have h_first :
        finMean (fun z : Lˣ ↦ conj (θ χ (algebraMap L K z)) *
            (constOne : Hall k) (simClassOf (mulLeft k z.val))) = 0 := by
      -- the mean of `conj θ_χ` over `Lˣ` is that of `conj χ`
      simpa [θ, j, thetaChar_charName] using h_mean
    have h_inner : rankInner (finrank k L) (greenCuspidal k (θ χ)) constOne = 0 := by
      have h_rank_zero : rankInner 0 (constOne : Hall k) (constOne : Hall k).mulMoebius = 1 := by
        simp [mulMoebius.eq_unfold, moebius_eq_one_of_dim_eq_zero, rankInner]
      have h_pair_one := h_pair constOne
      rw [h_left, h_first, h_rank_zero, zero_mul, zero_add, one_mul] at h_pair_one
      exact h_pair_one.symm
    -- `skew` pairs with the block averages of `constOne`, which are `constOne`
    simpa [skew, blockAverage, Hall.ext_iff, rankInner, θ] using h_inner

end GreenTau

/-!
## Lower bound for the degrees of Green's characters

Idea: pair with the indicator function of the identity maps times `moebius`. Each factor
`New.greenTau T P` multiplies the pairing by `(-1) ^ d / (q ^ d - 1)`, with `d = deg P` and
`q = |k|`, by `mulMoebius_greenCuspidal_one_mul`.
-/

section LabelDegree

open Module Matrix Finset Complex Hall Fintype ComplexOrder LinearMap GeneralLinearGroup

variable {k n : Type*} {r : ℕ}
  (K : Type*) [Field k] [Finite k] [Field K] [Algebra k K]
  {T : MulChar K ℂ} [IsFaithfulMulChar K T] [Fintype n] {c : Polynomial k}

omit [Finite k] in
/-- Induction on labels: start from `1` and multiply by monic irreducible polynomials other than
`X`. -/
@[elab_as_elim]
lemma IsLabel.induction_irreducible_mul [IsAlgClosed K] {p : ℕ → Polynomial k → Prop}
    (hc : IsLabel r c) (h_one : p 0 1)
    (h_step : ∀ (P : Polynomial k) (r : ℕ) (c : Polynomial k) (ξ : K), P.Monic → Irreducible P →
      P.coeff 0 ≠ 0 → P.aeval ξ = 0 → p r c →
      p (P.natDegree + r) (P * c)) :
    p r c := by
  -- Strong induction on the degree: split off a monic irreducible factor.
  induction r using Nat.strongRec generalizing c with
  | ind r ih =>
    obtain ⟨h_monic, h_sqfree, rfl, h_coeff⟩ := hc
    by_cases h_unit : IsUnit c
    · simpa [h_monic.isUnit_iff.1 h_unit] using h_one
    obtain ⟨P, hP_monic, hP_irred, c, rfl⟩ := c.exists_monic_irreducible_factor h_unit
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_aeval_eq_zero K P hP_irred.degree_pos.ne'
    have hc_monic : c.Monic := hP_monic.of_mul_monic_left h_monic
    rw [Polynomial.mul_coeff_zero, mul_ne_zero_iff] at h_coeff
    rw [hP_monic.natDegree_mul hc_monic] at ih ⊢
    exact h_step P _ c ξ hP_monic hP_irred h_coeff.left hξ
      (ih _ (Nat.lt_add_of_pos_left hP_irred.natDegree_pos)
        ⟨hc_monic, h_sqfree.of_mul_right, rfl, h_coeff.right⟩)

/-- A label stays a label over an extension field, as a finite field is perfect. -/
lemma IsLabel.map (hc : IsLabel r c) : IsLabel r (c.map (algebraMap k K)) := by
  obtain ⟨h_monic, h_sqfree, h_deg, h_coeff⟩ := hc
  have h_sep : c.Separable := PerfectField.separable_iff_squarefree.mpr h_sqfree
  exact ⟨h_monic.map _, h_sep.map.squarefree, by simpa, by simpa⟩

/-- For a real number q > 1 and m : ℕ, (q - m) q^m ∏_{i<m} q^i ≤ q ∏_{i<m} (q^(i+1) - 1). Divided by
q^(m+1) ∏_{i<m} q^i, this says that ∏_{i<m} (1 - q^(-(i+1))) is at least 1 - m/q. -/
lemma _root_.sub_mul_pow_mul_prod_le_mul_prod {q : ℝ} (hq : 1 < q) (m : ℕ) :
    (q - m) * q ^ m * ∏ i ∈ Finset.range m, q ^ i ≤
      q * ∏ i ∈ Finset.range m, (q ^ (i + 1) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- One more factor on each side; it suffices that `q - m ≤ q ^ (m + 1)`.
    have h_factor_nonneg : 0 ≤ q ^ (m + 1) - 1 := sub_nonneg.2 (one_le_pow₀ hq.le)
    have h_key : (q - (m + 1)) * q ^ (m + 1) ≤ (q - m) * (q ^ (m + 1) - 1) := by
      nlinarith [le_self_pow₀ hq.le m.add_one_ne_zero, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    push_cast [Finset.prod_range_succ]
    calc (q - (m + 1)) * q ^ (m + 1) * ((∏ i ∈ Finset.range m, q ^ i) * q ^ m)
        ≤ (q - m) * (q ^ (m + 1) - 1) * ((∏ i ∈ Finset.range m, q ^ i) * q ^ m) := by gcongr
      _ = (q - m) * q ^ m * (∏ i ∈ Finset.range m, q ^ i) * (q ^ (m + 1) - 1) := by ring
      _ ≤ q * (∏ i ∈ Finset.range m, (q ^ (i + 1) - 1)) * (q ^ (m + 1) - 1) := by gcongr
      _ = q * ((∏ i ∈ Finset.range m, (q ^ (i + 1) - 1)) * (q ^ (m + 1) - 1)) := by ring

variable (k) in
/-- The power basis of `k` over itself with generator `1`. -/
private def powerBasisOne : PowerBasis k k := ⟨1, 1, .singleton (Fin 1) k, by simp⟩

variable (k) in
open Classical in
/-- The indicator function of the classes of identity maps, in every dimension: for a class `c`,
`c.out.2` is a chosen endomorphism in it. -/
private def identityIndicator : Hall k := fun c : SimClass k ↦ if ∀ x, c.out.2 x = x then 1 else 0

/-- The pointwise product `mulMoebius` with `moebius` of Green's cuspidal function
`greenCuspidal k η` at the identity of `Fin d → k`, times `q ^ d - 1` with `q = |k|`, is `η 1` times
the order of `GL_d(k)`. This is `mulMoebius_greenCuspidal_lsmul` at the generator `1`. -/
private lemma mulMoebius_greenCuspidal_one_mul (d : ℕ) [NeZero d] (η : K → ℂ) :
    (greenCuspidal k η).mulMoebius (simClassOf (1 : End k (Fin d → k))) * (Nat.card k ^ d - 1) =
      η 1 * Nat.card (End k (Fin d → k))ˣ := by
  have h := mulMoebius_greenCuspidal_lsmul (V := Fin d → k) (powerBasisOne k) η
  simp [minpoly.eq_X_sub_C'] at h
  simpa [powerBasisOne, Nat.card_fun, ← Nat.card_congr (generalLinearEquiv ..).1] using h

omit [IsFaithfulMulChar K T] in
/-- Let `δ` be the indicator function of the identity classes and `q = |k|`. Pairing with
`δ.mulMoebius`, a factor `τ_P` of degree `d = deg P` in front of `F` multiplies the pairing by
`(-1) ^ d / (q ^ d - 1)`. -/
private lemma rankInner_greenTau_mul_mulMoebius (P : Polynomial k) (hP : Irreducible P) (m : ℕ)
    (F : Hall k) :
    rankInner (P.natDegree + m) (greenTau T P * F) (identityIndicator k).mulMoebius *
        (Nat.card k ^ P.natDegree - 1 : ℕ) =
      (-1) ^ P.natDegree * rankInner m F (identityIndicator k).mulMoebius := by
  classical
  have h_deg_ne : NeZero P.natDegree := .of_pos hP.natDegree_pos
  have h_mulMu_one (η : K → ℂ) :
      (greenCuspidal k η).mulMoebius (simClassOf (1 : End k (Fin P.natDegree → k))) *
          (Nat.card k ^ P.natDegree - 1) =
        η 1 * Nat.card (End k (Fin P.natDegree → k))ˣ :=
    mulMoebius_greenCuspidal_one_mul K P.natDegree η
  -- Move `τ_P` to the other side of the pairing by adjunction. Conjugating turns the conjugates in
  -- `rankInner` into plain values; on both sides only the identity classes contribute.
  rw [rankInner_mul_eq_rankInner_skew greenTau_eq_zero_of_dim_ne, ← star_inj]
  simp [identityIndicator, skew, greenTau, field, ite_div, ite_and, forall_and,
    LinearMap.ext_iff (M := _ × _), rankInner, finMean, finsum_eq_sum_of_fintype,
    simClassOf_out_eq_one_iff] at h_mulMu_one ⊢
  -- The goal now reads `F(1) C(1) μ(1) μ'(1) (q ^ d - 1) = F(1) μ'(1) |GL_d|`, where `C` is
  -- `greenCuspidal k θ_x` and `μ`, `μ'` are `moebius` at the identities of rank `d`, `m`.
  -- This is `h_mulMu_one` at `η = θ_x`, where `θ_x 1 = 1`, multiplied by `F(1) μ'(1)`.
  set one : SimClass k := simClassOf (1 : End k (Fin P.natDegree → k))
  set one_m : SimClass k := simClassOf (1 : End k (Fin m → k))
  have h_theta_one :
      greenCuspidal k (thetaChar T (Nat.card k ^ P.natDegree) (chosenRoot K P)) one *
          moebius one * ((Nat.card k : ℂ) ^ P.natDegree - 1) =
        Fintype.card (End k (Fin P.natDegree → k))ˣ := by
    rw [h_mulMu_one, map_one, one_mul]
  linear_combination (F one_m * moebius one_m) * h_theta_one

/-- Let `c` be a label of degree `r`, `q = |k|` and `δ` the indicator function of the identity
classes. There is a natural number `B ≤ q ^ r` such that the pairing of `labelChar T c` with
`δ.mulMoebius` in rank `r`, times `B`, is `(-1) ^ r`. -/
private lemma exists_le_rankInner_labelChar_mul_eq (hc : IsLabel r c) :
    ∃ B ≤ Nat.card k ^ r,
      rankInner r (labelChar T c) (identityIndicator k).mulMoebius * B = (-1) ^ r := by
  classical
  -- Induction over the irreducible factors, each contributing `q ^ deg P - 1` to `B`.
  refine hc.induction_irreducible_mul K ⟨1, ?_⟩ fun P m c' _ξ hm hP _hP_coeff _hξ ih ↦ ?_
  · simp [identityIndicator, mulMoebius, moebius_eq_one_of_dim_eq_zero, rankInner, finMean,
      finsum_eq_sum_of_fintype, simClassOf_out_eq_one_iff, eq_iff_true_of_subsingleton]
  obtain ⟨B, hB, h_pair⟩ := ih
  refine ⟨(Nat.card k ^ P.natDegree - 1) * B, ?_, ?_⟩
  · grw [pow_add, hB, Nat.sub_le]
  · rw [map_mul, labelChar_eq_greenTau T hP hm, Nat.cast_mul, ← mul_assoc,
      rankInner_greenTau_mul_mulMoebius K P hP, mul_assoc, h_pair, pow_add]

/-- Let `T` be a faithful multiplicative character of the algebraically closed field `K ⊇ k`
(`IsFaithfulMulChar`), and let `c` be a label of degree `r = card n`, i.e. a monic squarefree
polynomial over `k` of degree `r` with nonzero constant term. Let `q = |k|`, and let
`Ξ = labelChar T c` be the class function on `GL n k` obtained by parabolic induction from the
product of Green's functions `τ_P` over the monic irreducible factors `P` of `c`. (a) The real part
of `Ξ(1)` is non-negative. (b) `Ξ(1) conj Ξ(1) / |GL n k|` is at least `(1 - r / q) / q ^ r` in the
order of `ℂ`, so it is a real number. These bounds are consequences of the degree formula of Green
and Deligne–Lusztig for the characters attached to labels; the exact degree is not stated here. -/
lemma labelChar_degree_bounds [DecidableEq n] (hc : IsLabel (Fintype.card n) c) :
    let d := (labelChar T c).evalGL (n := n) 1
    0 ≤ d.re ∧
    ((1 - Fintype.card n / Nat.card k) / Nat.card k ^ Fintype.card n : ℝ) ≤
      d / Nat.card (GL n k) * star d := by
  classical
  -- With `q = |k|`, `r = |n|`: the value at `1` is `|GL| / (B ∏_(i<r) q ^ i)` for a natural number
  -- `B ≤ q ^ r`. To find it, pair with `(identityIndicator k).mulMoebius`, the indicator function
  -- of the identity maps times `moebius`.
  have hq : 1 < Nat.card k := Finite.one_lt_card
  obtain ⟨B, hB, h_pair⟩ :
      ∃ B ≤ Nat.card k ^ card n,
        rankInner (card n) (labelChar T c) (identityIndicator k).mulMoebius * B = (-1) ^ card n :=
    exists_le_rankInner_labelChar_mul_eq K hc
  -- `B = 0` would make the left side of `h_pair` vanish.
  have hB₀ : B ≠ 0 := by
    rintro rfl
    simp [eq_comm (a := (0 : ℂ))] at h_pair
  -- Only `1` contributes to the pairing, and `moebius 1 = ∏_(i<r) (-q ^ i)` by
  -- `moebius_simClassOf_lsmul`.
  let v : ℝ := Nat.card (GL n k) / B / ∏ i ∈ range (card n), (Nat.card k : ℝ) ^ i
  have value : (labelChar T c).evalGL (1 : GL n k) = v := by
    have μ_one :
        moebius (simClassOf (1 : End k (n → k))) = ∏ i ∈ range (card n), -(Nat.card k : ℂ) ^ i := by
      simpa [powerBasisOne, Lagrange.eval_nodal] using
        moebius_simClassOf_lsmul (V := n → k) (powerBasisOne k)
    rw [← finrank_pi k, rankInner_eq_classInner_simClassOf, classInner, ← star_inj] at h_pair
    -- The pairing identity now reads `Ξ(1) * ∏_(i<r) q ^ i * B = |GL|`.
    have h_value : labelChar T c (simClassOf (1 : End k (n → k))) *
        (∏ i ∈ range (card n), (Nat.card k : ℂ) ^ i) * B = Nat.card (GL n k) := by
      -- `↓`: the count of `GL n k` is rewritten before simp turns it into a count of units.
      simpa [identityIndicator, μ_one, prod_neg, field, ↓← Nat.card_congr toLin.toEquiv, finMean,
        finsum_eq_sum_of_fintype, simClassOf_out_eq_one_iff, NeZero.ne] using h_pair
    simp_all [v, ← eq_div_iff, evalGL, End.one_eq_id, prod_eq_zero_iff, NeZero.ne]
  suffices h : 0 ≤ v ∧
      (1 - card n / Nat.card k : ℝ) / Nat.card k ^ card n ≤ v / Nat.card (GL n k) * v by
    simp only [value, star_def, conj_ofReal]
    exact_mod_cast h
  rify at hq hB hB₀
  refine ⟨by positivity, ?_⟩
  -- The product inequality `∏_(i<r) (1 - q ^ (-i-1)) ≥ 1 - r / q`, with denominators cleared.
  have h_prod := sub_mul_pow_mul_prod_le_mul_prod hq (card n)
  -- Bound `B` by `q ^ r` and insert `|GL| = ∏_(i<r) q ^ i (q ^ (i + 1) - 1)`.
  unfold v
  grw [hB, hB]
  simpa [card_GL_eq_prod, field, prod_mul_distrib] using h_prod

end LabelDegree

end New

end
