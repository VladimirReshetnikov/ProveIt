import Lib.GLn.SchurModule.Basic
import Lib.General.Groups.BesselGroups

/-!
# Frobenius cycles, the twisted action of GL_k(W), depth and defect

This file contains the definitions for the theorem on elementary divisors
(`New.FrobeniusCycle.elementary_divisors`). Let `W` be a local ring with finite residue field.
Variables are pairs `(b, s)` of an index `b : Fin k` and a letter `s : ZMod N`.

## Main definitions and results

* `New.FrobeniusCycle`: a prime number `p` with a square root `sqrtPrime` in `R`, a power `P` of
  `p`, and ring maps `embedding s : W → R`, each marked even or odd, and each the `P`-th power of
  the one before modulo `p`.
* `New.FrobeniusCycle.letterMatrix`, `New.FrobeniusCycle.polyAction`,
  `New.FrobeniusCycle.letterRep`: `g` acts on the letter `s` through the image under `embedding s`
  of `g` (even) or of its inverse transpose (odd), both on polynomials and on coefficient vectors of
  forms of degree `n` in each letter. `New.FrobeniusCycle.polyAction_polyOfCoeffs` says that the two
  actions agree.
* `New.FrobeniusCycle.depth`, `New.FrobeniusCycle.defectWeight`: the depth of a monomial, and the
  weight of a variable in the defect of a monomial at a letter.
* `New.FrobeniusCycle.translatesIn`, `New.FrobeniusCycle.defectConditions`: vectors whose
  translates have given coefficients in an ideal.
* `New.FrobeniusCycle.deepForms`: vectors all of whose translates have only monomials of large
  depth.

Notions from other files:
* `New.linSubst z`: for a matrix `z` over `R`, the `R`-algebra map of polynomial rings that sends
  `X b` to `∑ t, z t b • X t`.
* `New.Monomials σ n`: the exponent vectors of degree `n` on the variables `σ`.
* `New.exponentOf β`, `New.polyOfCoeffs F`: the exponent vector on the variables `(b, s)` that is
  `β s` in the letter `s`, and the polynomial `∑ β, F β • x ^ β`.
* `New.symPowMatrix n`, `New.kroneckerPi`: the `n`-th symmetric power of a matrix, and the Kronecker
  product of a family of matrices.
* `New.levi W τ`, `New.parahoric W τ`: for a labelling `τ : Fin k → ℕ` of the indices, the matrices
  in `GL_k(W)` whose entry `(i, j)` is zero whenever `τ i ≠ τ j`, and those whose entry `(i, j)`
  lies in the maximal ideal of `W` whenever `τ i < τ j`.

## Notation

Matrices act on vectors of coefficients, so they are the transposes of the matrices substituted in
the variables: for both parities, the translate of a polynomial `h` in the letter `s` by `g` is
`h ∘ g_sᵀ`, where `g_s = T.letterMatrix s g`.

## Relation to the literature

See `New.UpperBound.ElementaryDivisors.DefectCount` for related work.
-/

noncomputable section

namespace New

open Fintype Finset MvPolynomial Matrix IsLocalRing Ideal

/-- The exponents of the monomials that are homogeneous of degree `n` in each of the `N` letters,
with `k` variables in each letter. -/
abbrev Exponents (N k n : ℕ) : Type := ZMod N → Monomials (Fin k) n

/-- For natural `r`, the labelling of the indices `b : Fin k` that is `0` if `b < r` and `1`
otherwise. -/
def twoBlock (k r : ℕ) (b : Fin k) : ℕ := if (b : ℕ) < r then 0 else 1

/-- The number `c* = 3 k c`, for the rank `k` and a precision `c` of congruences modulo powers of
the square root of `p`. It is the unit in which later files state their thresholds for defects. -/
def defectThreshold (k c : ℕ) : ℕ := 3 * k * c

lemma three_mul_le_defectThreshold {k : ℕ} (hk : 0 < k) (c : ℕ) : 3 * c ≤ defectThreshold k c :=
  Nat.mul_le_mul_right c (Nat.le_mul_of_pos_right 3 hk)

/-- A Frobenius cycle: a prime `p` with `P = p ^ frobExp ≥ 5`, where the residue field of `W` has
`P ^ N` elements. It also gives ring maps `embedding s : W → R` for `s` in `ℤ/N`, alternately even
and odd, with `embedding (s + 1) ≡ embedding s ^ P` modulo `p`, and an element `sqrtPrime` of `R`
with `sqrtPrime ^ 2 = p`. -/
structure FrobeniusCycle (N : ℕ) (W R : Type) [CommRing W] [IsLocalRing W] [CommRing R] where
  /-- The prime `p`. -/
  p : ℕ
  /-- The exponent `frobExp`, with `P = p ^ frobExp`. -/
  frobExp : ℕ
  /-- The ring maps `ι_s : W → R`, one for each letter `s ∈ ℤ/N`. -/
  embedding : ZMod N → W →+* R
  /-- Whether the letter `s` is even (`true`) or odd (`false`). -/
  isEven : ZMod N → Bool
  /-- A square root of `p` in `R`. -/
  sqrtPrime : R
  /-- `p` is prime. -/
  prime : p.Prime
  /-- `P = p ^ frobExp` is at least `5`. -/
  five_le_P : 5 ≤ p ^ frobExp
  /-- `sqrtPrime ^ 2 = p` in `R`. -/
  sqrtPrime_sq : sqrtPrime ^ 2 = p
  /-- `embedding (s + 1) ≡ embedding s ^ P` modulo `p`. -/
  frobenius_congr (s : ZMod N) (x : W) : (p : R) ∣ embedding (s + 1) x - embedding s x ^ p ^ frobExp
  /-- Even and odd letters alternate. -/
  isEven_succ (s : ZMod N) : isEven (s + 1) = !isEven s
  /-- The residue field of `W` has `(p ^ frobExp) ^ N` elements. -/
  card_residueField : Nat.card (IsLocalRing.ResidueField W) = (p ^ frobExp) ^ N

namespace FrobeniusCycle

variable {k N : ℕ} {W R R' : Type} [CommRing W] [IsLocalRing W] [CommRing R] [CommRing R']
  (φ : R →+* R') [NeZero N] (T : FrobeniusCycle N W R) (n r : ℕ) (i : ZMod N) (a a' : Fin k)
  (g : GL (Fin k) W) (s : ZMod N) (x : Fin k × ZMod N)

/-! ### The twisted action -/

/-- The prime power `P = p ^ frobExp` of the Frobenius cycle. -/
abbrev P : ℕ := T.p ^ T.frobExp

/-- The number `q = P ^ N` of elements of the residue field of `W`. -/
abbrev q : ℕ := T.P ^ N

/-- For a Frobenius cycle over `R` and a ring map `φ : R →+* R'`, the Frobenius cycle over `R'`
obtained by composing each ring map `embedding s` with `φ` and applying `φ` to `sqrtPrime`. -/
def map : FrobeniusCycle N W R' :=
  { T with
    embedding := φ.comp ∘ T.embedding
    sqrtPrime := φ T.sqrtPrime
    sqrtPrime_sq := by simp [← map_pow, sqrtPrime_sq]
    frobenius_congr s x := by simpa using map_dvd φ (T.frobenius_congr s x) }

/-- The homomorphism sending g in GL_k(W) to the matrix g_s over R: ι_s(g) if the letter s is
even, ι_s of the inverse transpose if s is odd. -/
@[simps -isSimp]
def letterMatrix : GL (Fin k) W →* Matrix (Fin k) (Fin k) R where
  toFun g := (if T.isEven s then ↑g else g⁻¹.1ᵀ).map (T.embedding s)
  map_one' := by simp
  map_mul' g h := by cases T.isEven s <;> simp [Matrix.map_mul]

/-- The action of GL_k(W) on polynomials in the variables x_{bs}: g sends x_{bs} to ∑_c
(g_s)_{cb} x_{cs}, with g_s = `New.FrobeniusCycle.letterMatrix` s g. -/
def polyAction :
    GL (Fin k) W →* MvPolynomial (Fin k × ZMod N) R →ₐ[R] MvPolynomial (Fin k × ZMod N) R where
  toFun g := linSubst (blockDiagonal fun s : ZMod N ↦ T.letterMatrix s g)
  map_one' := by simp [← Pi.one_def, AlgHom.ext_iff]
  map_mul' := by simp [AlgHom.ext_iff, linSubst_mul]

/-- The matrix ρ(g) of g in GL_k(W) on forms of degree n in each letter: the Kronecker product
over s of the n-th symmetric powers of `New.FrobeniusCycle.letterMatrix` s g. -/
@[simps -isSimp]
def letterRep : GL (Fin k) W →* Matrix (Exponents N k n) (Exponents N k n) R :=
  ({ toFun g := kroneckerPi fun s : ZMod N ↦ symPowMatrix n (T.letterMatrix s g)
     map_one' := by simp
     map_mul' := by simp [kroneckerPi_mul] } : GL (Fin k) W →* _)

/-! ### Depth, defect and the coefficient condition -/

/-- The indicator of the deep variables `x = (b, s)`, with `b` counted from `0`: it is `1` if `s`
is even and `r ≤ b`, or `s` is odd and `b < r`, and `0` otherwise. -/
def deepIndicator : ℕ := if T.isEven x.2 ↔ r ≤ (x.1 : ℕ) then 1 else 0

/-- The depth of a family β of exponent vectors of degree n, one for each letter: the total degree
of the monomial x^β in the variables that are deep for r (`New.FrobeniusCycle.deepIndicator`). -/
def depth (k n r : ℕ) (β : Exponents N k n) : ℕ := (exponentOf β).weight (T.deepIndicator r)

/-- For indices a,a' and letter s, the variable index (a',s) if s is even and (a,s) if s is odd. -/
@[simps]
def rootVar : Fin k × ZMod N := (if T.isEven s then a' else a, s)

/-- The weight of the variable `x = (b, s)` in the defect of a monomial at the letter `i` along the
root `(a, a')`; the defect is the sum of these weights over the monomial. Write
`u_s = T.rootVar a a' s` and `ū_s = T.rootVar a' a s`. The weight is `P ^ ((s - i) mod N) / (q - 1)`
times `[x = u_s] - [x = ū_s]`, plus `1` if `x = u_i`. For the recursive description of the defect
see `New.FrobeniusCycle.defectWeight_dotProduct_permStep`. -/
def defectWeight : ℝ :=
  ((if x = T.rootVar a a' x.2 then (T.P : ℝ) ^ (1 + (x.2 - 1 - i).val) else 0) -
    if x = T.rootVar a' a x.2 then (T.P : ℝ) ^ (x.2 - i).val else 0) / (T.q - 1)

/-- The submodule of the coefficient vectors `F : Exponents N k n → R` with `(ρ(g) F) β ∈ I` for
all `g` in the Levi subgroup `levi W τ` and all `β` in the set `B` of exponents, where
`ρ = T.letterRep n`. Here `τ` labels the indices `Fin k` by natural numbers, and `levi W τ`
consists of the matrices in `GL_k(W)` whose entry `(i, j)` is zero whenever `τ i ≠ τ j`. -/
def translatesIn (τ : Fin k → ℕ) (I : Ideal R) (B : Set (Exponents N k n)) :
    Submodule R (Exponents N k n → R) :=
  { carrier := {F : Exponents N k n → R | ∀ g ∈ levi W τ, ∀ β ∈ B, (T.letterRep n g *ᵥ F) β ∈ I}
    add_mem' hF hG g hg β hβ := by simpa [mulVec_add] using add_mem (hF g hg β hβ) (hG g hg β hβ)
    zero_mem' := by simp
    smul_mem' c F hF g hg β hβ := by
      simpa [mulVec_smul] using I.mul_mem_left c (hF g hg β hβ) }

/-- The coefficient vectors F such that (ρ(g)F)_β lies in I, with ρ = `New.FrobeniusCycle.letterRep`
n. This must hold whenever g is block diagonal with blocks of sizes a' and k − a' and β has defect
along the root (a, a') (`New.FrobeniusCycle.defectWeight`) above h at some letter. -/
abbrev defectConditions (I : Ideal R) (h : ℝ) : Submodule R (Exponents N k n → R) :=
  T.translatesIn n (twoBlock k a') I
    {β : Exponents N k n | ∃ i : ZMod N, h < (exponentOf β).weight (T.defectWeight i a a')}

/-- The coefficient vectors F of forms of degree n in each letter such that, for every g in GL_k(W),
all monomials of ρ(g)F have depth (`New.FrobeniusCycle.depth`, for r) at least d. -/
abbrev deepForms (k n r d : ℕ) : Submodule R (Exponents N k n → R) :=
  T.translatesIn n 0 ⊥ {β : Exponents N k n | T.depth k n r β < d}

/-! ### First properties -/

omit [NeZero N] in
lemma one_lt_P : (1 : ℝ) < T.P := mod_cast Nat.one_lt_ofNat.trans_le T.five_le_P

lemma one_lt_q : (1 : ℝ) < T.q := by simpa using one_lt_pow₀ T.one_lt_P (NeZero.ne N)

omit [NeZero N] in
/-- For a Frobenius cycle `T` and natural `n`, the ring map of the letter `s + n` is the `P ^ n`-th
power of that of the letter `s` modulo `p`. -/
lemma frobenius_pow_congr (x : W) : (T.p : R) ∣ T.embedding (s + n) x - T.embedding s x ^ T.P ^
  n := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Raise the induction hypothesis to the power `P`, then take one step by `T.frobenius_congr`.
    have h_pow : (T.p : R) ∣ T.embedding (s + n) x ^ T.P - (T.embedding s x ^ T.P ^ n) ^ T.P :=
      ih.trans (sub_dvd_pow_sub_pow ..)
    simpa [← add_assoc, pow_succ, pow_mul] using (T.frobenius_congr (s + n) x).add h_pow

variable {n r i a a' g x}

omit [NeZero N] in
lemma sqrtPrime_ne_zero [CharZero R] : T.sqrtPrime ≠ 0 := by
  intro hw
  have hp : (T.p : R) = 0 := by simp [← T.sqrtPrime_sq, hw]
  exact T.prime.ne_zero (Nat.cast_eq_zero.1 hp)

omit [NeZero N] in
lemma finite_residueField (T : FrobeniusCycle N W R) : Finite (IsLocalRing.ResidueField W) :=
  Nat.finite_of_card_ne_zero (by simp [T.card_residueField, T.prime.ne_zero])

/-- The ring map `T.embedding s : W → R` of the letter `s` sends the maximal ideal of `W` into
`(p)`. -/
lemma p_dvd_embedding_of_mem_maximalIdeal {y : W} (hy_mem : y ∈ maximalIdeal W) :
    (T.p : R) ∣ T.embedding s y := by
  -- As `ι s y ≡ (ι s y) ^ q` modulo `p`, the prime `p` divides `ι s y * ι s (1 - y ^ (q - 1))`,
  -- whose last factor is a unit.
  have hq : 1 < T.q := mod_cast T.one_lt_q
  have h_unit : IsUnit (1 - y ^ (T.q - 1)) :=
    isUnit_one_sub_self_of_mem_nonunits _ (pow_mem_of_mem _ hy_mem _ (Nat.sub_pos_of_lt hq))
  have h_factor : T.embedding s y * T.embedding s (1 - y ^ (T.q - 1)) = T.embedding s y -
    T.embedding s y ^ T.q := by
    simp [mul_sub, mul_pow_sub_one, T.prime.ne_zero]
  rw [← (h_unit.map (T.embedding s)).dvd_mul_right, h_factor]
  simpa [ZMod.natCast_self] using T.frobenius_pow_congr N s y

/-- Let `g` lie in the parahoric subgroup of `τ`. Each letter `s` in `ℤ/N` is marked even or odd by
`T.isEven s`, neighbouring letters differently, and on an even letter the matrix
`T.letterMatrix s g` is the entrywise image of `g` under the ring map `T.embedding s : W → R`. If
`s` is even and `τ i < τ j`, then `p` divides the entry `(i, j)` of this matrix. -/
lemma p_dvd_letterMatrix_of_mem_parahoric_of_isEven {τ : Fin k → ℕ} {g : GL (Fin k) W}
    (hg : g ∈ parahoric W τ) (hs : T.isEven s = true) {i j : Fin k} (hij : τ i < τ j) :
    (T.p : R) ∣ T.letterMatrix s g i j := by
  have h_entry : T.letterMatrix s g i j = T.embedding s (g i j) := by simp [letterMatrix_apply, hs]
  rw [h_entry]
  exact T.p_dvd_embedding_of_mem_maximalIdeal s ((residue_eq_zero_iff _).1 (hg hij))

/-- Let `g` lie in the parahoric subgroup of `τ`. Each letter `s` in `ℤ/N` is marked even or odd by
`T.isEven s`, neighbouring letters differently, and on an odd letter the matrix `T.letterMatrix s g`
is the entrywise image of the transpose of `g⁻¹` under the ring map `T.embedding s : W → R`. If `s`
is odd and `τ j < τ i`, then `p` divides the entry `(i, j)` of this matrix. -/
lemma p_dvd_letterMatrix_of_mem_parahoric_of_not_isEven {τ : Fin k → ℕ} {g : GL (Fin k) W}
    (hg : g ∈ parahoric W τ) (hs : T.isEven s = false) {i j : Fin k} (hji : τ j < τ i) :
    (T.p : R) ∣ T.letterMatrix s g i j := by
  -- The entry comes from the entry `(j, i)` of `g⁻¹`, which is parahoric too.
  have h_entry : T.letterMatrix s g i j = T.embedding s (g⁻¹ j i) := by
    simp [letterMatrix_apply, hs]
  rw [h_entry]
  exact T.p_dvd_embedding_of_mem_maximalIdeal s ((residue_eq_zero_iff _).1 (inv_mem hg hji))

/-- Let `g` lie in the parahoric subgroup of `τ`. Suppose that `τ i < τ j` if `s` is even, and
`τ j < τ i` if it is odd. Then `p` divides the entry `(i, j)` of `T.letterMatrix s g`. -/
lemma p_dvd_letterMatrix_of_mem_parahoric {τ : Fin k → ℕ} {g : GL (Fin k) W}
    (hg : g ∈ parahoric W τ) (i j : Fin k) (h_even : T.isEven s = true → τ i < τ j)
    (h_odd : T.isEven s = false → τ j < τ i) : (T.p : R) ∣ T.letterMatrix s g i j := by
  cases hs : T.isEven s with
  | true => exact T.p_dvd_letterMatrix_of_mem_parahoric_of_isEven s hg hs (h_even hs)
  | false => exact T.p_dvd_letterMatrix_of_mem_parahoric_of_not_isEven s hg hs (h_odd hs)

/-- Under `T.polyAction`, an element `g` of GL_k(W) sends the variable `X x`, where `x = (c, s)`, to
`∑ b, (g_s) b c • X (b, s)`, where `g_s = T.letterMatrix s g`. -/
lemma polyAction_X (T : FrobeniusCycle N W R) {g : GL (Fin k) W} {x : Fin k × ZMod N} :
    T.polyAction g (X x) = ∑ b : Fin k, C (T.letterMatrix x.2 g b x.1) * X (b, x.2) := by
  simp [polyAction, linSubst, blockDiagonal, smul_eq_C_mul, sum_prod_type_right]

/-- Fix a threshold `r`. The variable `(b, s)` is deep if `s` is even and `r ≤ b`, or `s` is odd and
`b < r`; the number `T.deepIndicator r (b, s)` is `1` on deep variables and `0` on the others.
An element `β` of `Exponents N k n` is a monomial of degree `n` in each letter, and
`T.depth k n r β` is its degree in the deep variables. The diagonal matrix with entries
`t ^ T.depth k n r β` is the Kronecker product over the letters `s` of the `n`-th symmetric powers
of the diagonal matrices that scale the deep variables of `s` by `t` and fix the others. -/
lemma diagonal_pow_depth (T : FrobeniusCycle N W R) {n r : ℕ} (t : R) :
    diagonal (fun β : Exponents N k n ↦ t ^ T.depth k n r β) =
      kroneckerPi fun s : ZMod N ↦
        symPowMatrix n (diagonal fun b : Fin k ↦ t ^ T.deepIndicator r (b, s)) := by
  -- In each letter a diagonal substitution scales a monomial by the product of the factors of its
  -- variables, and the exponents of `t` add up to the depth.
  set δ : Fin k × ZMod N → ℕ := T.deepIndicator r with hδ
  have h_scale (s : ZMod N) (α : Fin k →₀ ℕ) :
      linSubst (diagonal fun b : Fin k ↦ t ^ δ (b, s)) (monomial α 1) =
        monomial α (t ^ ∑ b : Fin k, α b * δ (b, s)) := by
    simp [monomial_eq, linSubst, diagonal_apply, smul_eq_C_mul, Finsupp.prod_fintype, mul_pow,
      prod_mul_distrib, ← prod_pow_eq_pow_sum, pow_mul']
  have h_letter (s : ZMod N) : symPowMatrix n (diagonal fun b : Fin k ↦ t ^ δ (b, s)) =
      diagonal fun α : Monomials (Fin k) n ↦ t ^ ∑ b : Fin k, α.val b * δ (b, s) := by
    ext α β
    by_cases h_eq : α = β
    · simp [symPowMatrix, h_scale, h_eq]
    · simp [symPowMatrix, h_scale, coeff_monomial, h_eq, Ne.symm h_eq]
  have h_depth (β : Exponents N k n) :
      T.depth k n r β = ∑ s : ZMod N, ∑ b : Fin k, (β s).val b * δ (b, s) := by
    simp [depth, exponentOf, Finsupp.weight_eq_sum, sum_prod_type_right, hδ]
  ext α β
  simp [h_letter, h_depth, kroneckerPi, diagonal_apply, Fintype.prod_ite_zero, funext_iff,
    prod_pow_eq_pow_sum]

/-- For a Frobenius cycle `T`, an element `g` of `GL_k(W)` acts on polynomials in the variables
`x_{(b, s)}` by `T.polyAction g`: in each letter `s` it substitutes linearly by the matrix
`T.letterMatrix s g`, which is the image in `R` of `g` (even `s`) or of its inverse transpose
(odd `s`). A coefficient vector `F` stands for the form `∑ β, F β • x ^ β` of degree `n` in each
letter. The matrix `T.letterRep n g`, the Kronecker product over the letters of the `n`-th symmetric
powers of these matrices, represents the action on such forms. -/
lemma polyAction_polyOfCoeffs (T : FrobeniusCycle N W R) {n : ℕ} {g : GL (Fin k) W}
    (F : Exponents N k n → R) :
    T.polyAction g (polyOfCoeffs F) = polyOfCoeffs (T.letterRep n g *ᵥ F) := by
  -- `mono s` renames to the variables of the letter `s`. The image of the monomial `α s` is a form
  -- of degree `n`, which we expand in monomials; then we multiply over the letters.
  let mono (s : ZMod N) (f : MvPolynomial (Fin k) R) : MvPolynomial (Fin k × ZMod N) R :=
    rename (fun b : Fin k ↦ (b, s)) f
  have expand (α : Exponents N k n) (s : ZMod N) :
      linSubst (T.letterMatrix s g) (monomial (α s) 1) =
        ∑ β : Monomials (Fin k) n, symPowMatrix n (T.letterMatrix s g) β (α s) • monomial β 1 :=
    (sum_monomials_eq_of_isHomogeneous ((α s).isHomogeneous_linSubst (T.letterMatrix s g))).symm
  calc T.polyAction g (polyOfCoeffs F)
      = ∑ α, F α • ∏ s, mono s (linSubst (T.letterMatrix s g) (monomial (α s) 1)) := by
        simp [mono, monomial_eq, polyAction, linSubst, blockDiagonal, smul_eq_C_mul,
          sum_prod_type_right, polyOfCoeffs, exponentOf, prod_prod_type_right]
    _ = ∑ α, F α • ∑ β, T.letterRep n g β α • ∏ s, mono s (monomial (β s) 1) := by
        simp [expand, mono, prod_univ_sum, prod_smul, letterRep, kroneckerPi, -univ_eq_attach]
    _ = polyOfCoeffs (T.letterRep n g *ᵥ F) := by
        simp [mono, monomial_eq, polyOfCoeffs, exponentOf, prod_prod_type_right, mulVec_eq_sum,
          smul_eq_C_mul, Finset.mul_sum]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- The matrix of `g` on forms for the Frobenius cycle `T.map φ`, obtained from `T` along the ring
map `φ : R →+* R'`, is the entrywise image under `φ` of the matrix of `g` for `T`. -/
lemma letterRep_map : (T.map φ).letterRep n g = (T.letterRep n g).map φ := by
  have h_letterMatrix_map (s : ZMod N) :
      (T.map φ).letterMatrix s g = (T.letterMatrix s g).map φ := rfl
  ext β α
  simp [h_letterMatrix_map, letterRep, kroneckerPi, symPowMatrix, linSubst, smul_eq_C_mul,
    map_bind₁, ← coeff_map]

@[simp]
lemma one_add_val_sub_one_sub : 1 + (s - 1 - i).val = if s = i then N else (s - i).val := by
  zify
  simp [sub_right_comm, ZMod.cast_sub_one, sub_eq_zero]

/-! ### Bounds on the defect weights -/

/-- For a Frobenius cycle `T`, let `P = T.P` be its prime power, which is at least `5`, and let
`q = T.q = P ^ N`. For every letter `s` one has `5 P ^ s ≤ q`, where `s` is read in
`{0, …, N - 1}`. -/
lemma five_mul_P_pow_le_q : 5 * T.P ^ s.val ≤ T.q :=
  calc 5 * T.P ^ s.val ≤ T.P ^ (s.val + 1) := by grw [pow_succ', T.five_le_P]
    _ ≤ T.P ^ N := Nat.pow_le_pow_right (pow_pos T.prime.pos T.frobExp) s.val_lt

lemma five_le_q : (5 : ℝ) ≤ T.q := mod_cast T.five_le_P.trans (Nat.le_self_pow (NeZero.ne N) T.P)

/-- Let `a ≠ a'`. In the letter `s` let `u = T.rootVar a a' s` be the variable `(a', s)` if `s` is
even and `(a, s)` if `s` is odd, and let `ū = T.rootVar a' a s` be the other of these two variables.
The defect of a monomial at the letter `i` along the root `(a, a')` is its weighted degree for the
real weights `T.defectWeight i a a'`. These are `P ^ (1 + (s - 1 - i).val) / (q - 1)` at `u`,
`-P ^ (s - i).val / (q - 1)` at `ū` and `0` at the other variables. The weight of `u` minus the
weight of `ū` lies in `[0, 3 / 2]`. -/
lemma defectWeight_sub_mem_Icc (T : FrobeniusCycle N W R) {i : ZMod N} {a a' : Fin k} (s : ZMod N)
    (ha : a ≠ a') :
    T.defectWeight i a a' (T.rootVar a a' s) - T.defectWeight i a a' (T.rootVar a' a s) ∈
      Set.Icc 0 (3 / 2) := by
  have q_sub_one_pos : (0 : ℝ) < T.q - 1 := sub_pos.2 T.one_lt_q
  have h_ne : T.rootVar a a' s ≠ T.rootVar a' a s := by grind [rootVar]
  have h_diff :
      T.defectWeight i a a' (T.rootVar a a' s) - T.defectWeight i a a' (T.rootVar a' a s) =
        (T.P ^ (1 + (s - 1 - i).val) + T.P ^ (s - i).val) / (T.q - 1) := by
    simp only [defectWeight, rootVar_snd, ite_true, ite_eq_right h_ne, ite_eq_right h_ne.symm]
    ring
  have h_first : (T.P : ℝ) ^ (1 + (s - 1 - i).val) ≤ T.q :=
    mod_cast Nat.pow_le_pow_right (pow_pos T.prime.pos _) (by linarith [(s - 1 - i).val_lt])
  have h_second : (5 * T.P ^ (s - i).val : ℝ) ≤ T.q := mod_cast T.five_mul_P_pow_le_q (s - i)
  rw [h_diff]
  exact ⟨by positivity, (div_le_iff₀ q_sub_one_pos).2 (by linarith [T.five_le_q])⟩

/-- Let `P = T.P` be the prime power of the Frobenius cycle, which is at least `5`, and let
`q = T.q = P ^ N`. As `s` runs over the letters, the exponent `1 + (s - 1 - i).val` runs over
`1, …, N`, and the sum `P + P ^ 2 + ⋯ + P ^ N` is at most `2 (q - 1)`. -/
lemma sum_P_pow_le (T : FrobeniusCycle N W R) (i : ZMod N) :
    ∑ s : ZMod N, (T.P : ℝ) ^ (1 + (s - 1 - i).val) ≤ 2 * (T.q - 1) := by
  -- With `S = 1 + P + ⋯ + P ^ (N - 1)` the sum is both `P S` and `S + (q - 1)`.
  set S : ℝ := ∑ s : ZMod N, (T.P : ℝ) ^ (s - i).val with hS
  have h_mul : ∑ s : ZMod N, (T.P : ℝ) ^ (1 + (s - 1 - i).val) = T.P * S := by
    simp only [pow_add, pow_one, ← mul_sum]
    exact congrArg _ ((Equiv.subRight 1).sum_comp fun s : ZMod N ↦ (T.P : ℝ) ^ (s - i).val)
  have h_term (s : ZMod N) : (T.P : ℝ) ^ (1 + (s - 1 - i).val) =
      T.P ^ (s - i).val + if s = i then (T.q - 1 : ℝ) else 0 := by
    rw [one_add_val_sub_one_sub]
    split_ifs with hs <;> simp [hs]
  have h_add : ∑ s : ZMod N, (T.P : ℝ) ^ (1 + (s - 1 - i).val) = S + (T.q - 1) := by
    simp only [h_term, sum_add_distrib, Fintype.sum_ite_eq', hS]
  have hP : 5 * S ≤ T.P * S := mul_le_mul_of_nonneg_right (mod_cast T.five_le_P) (by positivity)
  linarith [T.one_lt_q]

/-- The defect of an exponent vector `α` at the letter `i` along the root `(a, a')` is the sum of
`α x * T.defectWeight i a a' x` over the variables `x = (b, s)`. If `α` has degree at most `d` in
each letter, then its defect has absolute value at most `2 d`. -/
lemma abs_weight_defectWeight_le (T : FrobeniusCycle N W R) {i : ZMod N} {a a' : Fin k}
    {α : Fin k × ZMod N →₀ ℕ} {d : ℝ} (hα : ∀ s : ZMod N, ∑ b : Fin k, (α (b, s) : ℝ) ≤ d) :
    |α.weight (T.defectWeight i a a')| ≤ 2 * d := by
  have q_sub_one_pos : (0 : ℝ) < T.q - 1 := sub_pos.2 T.one_lt_q
  have hd : 0 ≤ d := le_trans (by positivity) (hα i)
  let bound (s : ZMod N) : ℝ := T.P ^ (1 + (s - 1 - i).val) / (T.q - 1)
  have h_var (x : Fin k × ZMod N) : |T.defectWeight i a a' x| ≤ bound x.2 := by
    have h_exp : (x.2 - i).val ≤ 1 + (x.2 - 1 - i).val := by
      rw [one_add_val_sub_one_sub]
      split_ifs
      exacts [(ZMod.val_lt (x.2 - i)).le, le_rfl]
    have h_pow_nonneg : 0 ≤ (T.P : ℝ) ^ (x.2 - i).val := by positivity
    have h_pow_le : (T.P : ℝ) ^ (x.2 - i).val ≤ (T.P : ℝ) ^ (1 + (x.2 - 1 - i).val) :=
      pow_le_pow_right₀ T.one_lt_P.le h_exp
    -- The numerator is a difference of two numbers in `[0, P ^ (1 + (s - 1 - i))]`.
    rw [defectWeight, abs_div, abs_of_pos q_sub_one_pos]
    refine div_le_div_of_nonneg_right (abs_sub_le_iff.2 ⟨?_, ?_⟩) q_sub_one_pos.le
    · split_ifs <;> linarith
    · split_ifs <;> linarith
  calc |α.weight (T.defectWeight i a a')|
      ≤ ∑ x : Fin k × ZMod N, α x * |T.defectWeight i a a' x| := by
        simpa [Finsupp.weight_eq_sum, abs_mul] using
          abs_sum_le_sum_abs (fun x ↦ α x * T.defectWeight i a a' x) univ
    _ ≤ ∑ x : Fin k × ZMod N, α x * bound x.2 := by grw [h_var]
    _ = ∑ s : ZMod N, (∑ b : Fin k, (α (b, s) : ℝ)) * bound s := by
        simp only [sum_prod_type_right, sum_mul]
    _ ≤ ∑ s : ZMod N, d * bound s := by grw [hα]
    _ = (∑ s : ZMod N, (T.P : ℝ) ^ (1 + (s - 1 - i).val)) / (T.q - 1) * d := by
        rw [← mul_sum, Finset.sum_div, mul_comm]
    _ ≤ 2 * d := mul_le_mul_of_nonneg_right ((div_le_iff₀ q_sub_one_pos).2 (T.sum_P_pow_le i)) hd

end FrobeniusCycle

end New

end
