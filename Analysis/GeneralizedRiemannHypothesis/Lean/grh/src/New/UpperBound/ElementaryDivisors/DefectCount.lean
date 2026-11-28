import Lib.General.Measure.IntegralOperators
import Lib.LocalGL.Green.CuspidalFunctions
import New.UpperBound.ElementaryDivisors.PieriCone
import New.UpperBound.ElementaryDivisors.RootLemma

/-!
# The dimension of the forms of bounded defect

Let `T` be a Frobenius cycle (`New.FrobeniusCycle`) over a field `K` of characteristic `p`, with
`P = T.P` and `q = T.q = P ^ N`. Exponents are indexed by `(b, s) ∈ Fin k × ZMod N`, and `s` is
called the letter. The defect of an exponent `β` at the letter `i` along the root `(a, a')` is the
linear form `∑ x, T.defectWeight i a a' x * β x`. Pieri's inequalities say that the defects along
the simple roots `(b, b + 1)` are at most `0`.

The forms whose translates by a Levi subgroup with two blocks have bounded defect along the root
between the blocks are counted by flags and lattice points. One substitutes `x ^ m` for the
variables, `m` a power of `q`, and multiplies by one monomial for each class of exponents modulo
`m`. Give the variable `(b, s)` the height `b` for even `s` and `-b` for odd `s`. Among the terms of
all translates of the resulting polynomial by the Levi subgroup, one of least height has defect at
most `0` along the other simple roots, and it occurs in the translate by a representative of a flag,
that is, of a coset of the lower Iwahori subgroup. A shift by an integral vector moves its exponent,
divided by `m`, into the cone of Pieri's inequalities. As `m` grows, the count of these exponents
becomes the volume of the cone cut by a slab, and the share of the cone in a slab is the inverse of
the number of all flags.

## Main definitions and results

* `New.FrobeniusCycle.defectCone`: the real vectors of bounded defect along the simple roots.
* `New.powerPacking`: a family of forms in the `m`-th powers of the variables, packed into one
  polynomial.
* `New.FrobeniusCycle.exists_finrank_defectConditions_le_volume`: the dimension of the forms of
  bounded defect is at most a number of flags times the volume of the part of a slab in which
  Pieri's inequalities hold.
* `New.FrobeniusCycle.index_mul_finrank_defectConditions_le`: in large degree, the parahoric index
  times the dimension of the forms of bounded defect is at most `1 + θ` times the number of
  exponents.

Notions from other files:
* `New.parahoric`: The parahoric subgroup of a labelling τ: matrices in GL_k(W), W local, whose
  (i,j) entry lies in the maximal ideal whenever τ(i) < τ(j).
* `New.FrobeniusCycle.defectConditions`: The forms F such that, for every g block diagonal with
  blocks of sizes a', k − a' and every β of defect above h along (a, a') at some letter, the
  coefficient of g·F at β lies in a given ideal I. In this file I = ⊥.
* `levi W (twoBlock k r)`: The block diagonal matrices with blocks r and k − r.
* `degreeSlab k D`: The real vectors β ≥ 0 whose degree ∑_b β(b,s) in each letter s lies in [D
  s − 1, D s].

## Notation

In the count, `m = q ^ j` is a power of `q`. As matrices act transposed, the lower Iwahori subgroup
is used.

## Relation to the literature

Volumes of interlacing regions, Frobenius amplification and counting by leading terms along flags
are known in the literature. Related work: Forrester–Zhang, Corank-1 projections and the randomised
Horn problem, 2021 (after Dixon, 1905; Anderson, 1991); Bombieri, Counting points on curves over
finite fields, Sém. Bourbaki 430, 1973; Okounkov, Brunn–Minkowski inequality for multiplicities,
1996.
-/

/-!
## Forms of bounded defect: flags times the volume of a cone

The lower Iwahori subgroup is `parahoric W Fin.val`.
-/

section FlagsAndVolume

open Subgroup MvPolynomial Matrix Finset Module Nat Fintype Finsupp MeasureTheory Set Filter

namespace New

variable {N k : ℕ}
  {W K : Type} [NeZero N] [CommRing W] [IsLocalRing W] [Field K]

/-- Over a local ring `W` with finite residue field, the parahoric subgroup of `GL_k(W)` of every
labelling `τ` has finite index. -/
instance [Finite (IsLocalRing.ResidueField W)] (τ : Fin k → ℕ) :
    (parahoric (k := k) W τ).FiniteIndex :=
  finiteIndex_of_le (ker_le_comap (GeneralLinearGroup.map (IsLocalRing.residue W)) _)

/-- Bound for the number of full flags over a finite field `K` with `q` elements: the index of the
subgroup of lower triangular matrices in `GL_k(K)` is at most `∏ (q ^ (l + 1) - 1) / (q - 1)` over
`l < k`. -/
lemma index_borel_le [Finite K] :
    (parabolic (R := K) (OrderDual.toDual ∘ (Fin.val : Fin k → ℕ))).index ≤
      ∏ l : Fin k, ((Nat.card K : ℝ) ^ (l.val + 1) - 1) / (Nat.card K - 1) := by
  -- A unit on the diagonal and `i` free entries left of it, in each row `i`, give
  -- `∏ (q - 1) q ^ i` elements of `B`. Divide `#GL = ∏ q ^ i (q ^ (i + 1) - 1)` by this number.
  set B : Subgroup (GL (Fin k) K) := parabolic (OrderDual.toDual ∘ (Fin.val : Fin k → ℕ))
  set q : ℝ := (Nat.card K : ℝ)
  let Rows : Type := ∀ i : Fin k, Kˣ × (Set.Iio i → K)
  let low (x : Rows) : Matrix (Fin k) (Fin k) K :=
    of fun i j ↦ if i < j then 0 else if h : j < i then (x i).2 ⟨j, h⟩ else (x i).1
  have det_low (x : Rows) : (low x).det ≠ 0 := by
    simp +contextual [low, BlockTriangular, det_of_isLowerTriangular, univ.prod_eq_zero_iff]
  let f (x : Rows) : B := ⟨.mkOfDetNeZero _ (det_low x), fun _ _ hij ↦ ite_eq_left hij⟩
  have f_inj : f.Injective := by
    intro x y hxy
    have h_low : low x = low y :=
      congrArg (fun g : B ↦ ((g : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) hxy
    ext i j
    · simpa [low] using congrFun₂ h_low i i
    · simpa [low, Set.mem_Iio.1 j.2, (Set.mem_Iio.1 j.2).not_gt] using congrFun₂ h_low i j
  have h_card : (B.index : ℝ) * Nat.card Rows ≤ Nat.card (GL (Fin k) K) :=
    mod_cast (mul_le_mul_right (card_le_card_of_injective f f_inj) _).trans B.index_mul_card.le
  have hq : 1 < q := Nat.one_lt_cast.2 Finite.one_lt_card
  have h_rows : (Nat.card Rows : ℝ) = ∏ i : Fin k, (q - 1) * q ^ i.val := by
    simp [Rows, q, Nat.card_pi, Nat.card_units]
  have h_GL : (Nat.card (GL (Fin k) K) : ℝ) = ∏ i : Fin k, q ^ i.val * (q ^ (i.val + 1) - 1) := by
    simp [q, card_GL_eq_prod, prod_range]
  have h_pos : 0 < ∏ i : Fin k, (q - 1) * q ^ i.val :=
    prod_pos fun i _ ↦ mul_pos (sub_pos.2 hq) (pow_pos (one_pos.trans hq) _)
  refine le_of_mul_le_mul_right ?_ h_pos
  calc (B.index : ℝ) * ∏ i : Fin k, (q - 1) * q ^ i.val
      ≤ ∏ i : Fin k, q ^ i.val * (q ^ (i.val + 1) - 1) := by rwa [h_rows, h_GL] at h_card
    _ = (∏ l : Fin k, (q ^ (l.val + 1) - 1) / (q - 1)) * ∏ i : Fin k, (q - 1) * q ^ i.val := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun i _ ↦ by field [(sub_pos.2 hq).ne']

/-- The defect of a vector `β` indexed by `(b, s) ∈ Fin k × ZMod N`, at the letter `i` along the
root `(b, b')`, is the linear form with coefficients `T.defectWeight i b b'`, namely
`β v + ∑ s, ± P ^ ((s - i) mod N) * (β (b', s) - β (b, s)) / (q - 1)`, with the sign `+` at even
`s`, and `v = (b', i)` for even `i`, `v = (b, i)` for odd `i`. The set `T.defectCone a h` consists
of the real vectors `β` whose defect, at every letter, is at most `h` along the simple root
`(a, a + 1)` and at most `0` along the other simple roots `(b, b + 1)`. For `h = 0` these are
Pieri's inequalities, see `New.FrobeniusCycle.permStep_mem_defectCone_iff`. The condition `β ≥ 0` is
not part of this set; it comes with the slab. -/
def FrobeniusCycle.defectCone (T : FrobeniusCycle N W K) (a : Fin k) (h : ℝ) :
    Set (Fin k × ZMod N → ℝ) :=
  {β : Fin k × ZMod N → ℝ |
    ∀ (i : ZMod N) (b b' : Fin k), b.val + 1 = b' → T.defectWeight i b b' ⬝ᵥ β ≤
      (if b = a then h else 0)}

/-- The vectors `β ≥ 0` with degree `∑ b, β (b, s)` in `[D s - 1, D s]` for each letter `s`, and
with defect at every letter at most `h` along `(a, a + 1)` and at most `0` along the other simple
roots `(b, b + 1)`, form a convex set. -/
lemma FrobeniusCycle.convex_defectCone_inter_degreeSlab (T : FrobeniusCycle N W K) (a : Fin k)
    (h : ℝ) (D : ZMod N → ℝ) :
    Convex ℝ (T.defectCone a h ∩ degreeSlab k D) := by
  rintro x ⟨hx_cone, hx_nonneg, hx_deg⟩ y ⟨hy_cone, hy_nonneg, hy_deg⟩ s t hs ht hst
  refine ⟨fun i b b' hb ↦ ?_, add_nonneg (smul_nonneg hs hx_nonneg) (smul_nonneg ht hy_nonneg),
    fun j ↦ ?_⟩
  · rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    exact convex_Iic (if b = a then h else 0) (hx_cone i b b' hb) (hy_cone i b b' hb) hs ht hst
  · simpa [univ.mul_sum, sum_add_distrib] using
      convex_Icc (D j - 1) (D j) (hx_deg j) (hy_deg j) hs ht hst

omit [NeZero N] in
/-- In characteristic `T.p`, the values of the embedding `T.embedding s` of each letter `s` are
fixed by raising to the power `q ^ j`, with `q = T.q = P ^ N`. -/
lemma FrobeniusCycle.embedding_pow_q_pow (T : FrobeniusCycle N W K) [CharP K T.p]
    (s : ZMod N) (y : W) (j : ℕ) :
    T.embedding s y ^ T.q ^ j = T.embedding s y := by
  have h_dvd := T.frobenius_pow_congr (N * j) s y
  rw [show s + (N * j : ℕ) = s by simp [ZMod.natCast_self], CharP.cast_eq_zero K T.p,
    zero_dvd_iff, sub_eq_zero] at h_dvd
  rw [q, ← pow_mul, ← h_dvd]

/-- In characteristic `T.p`, the linear substitution `T.polyAction g` by which a matrix `g` acts on
polynomials over `K` commutes with the substitution `x ↦ x ^ m` of the variables, for every power
`m` of `q = T.q`. -/
lemma FrobeniusCycle.polyAction_commute_expand (T : FrobeniusCycle N W K) [CharP K T.p]
    {m j : ℕ} (hm : m = T.q ^ j) (g : GL (Fin k) W) :
    Commute (T.polyAction g) (expand m) := by
  -- Raising to the power `m` is additive and fixes the entries of the twisted matrices.
  have : Fact (Nat.Prime T.p) := Fact.mk T.prime
  have h_pow : m = T.p ^ (T.frobExp * (N * j)) := by simp [hm, pow_mul]
  have h_fixed (s : ZMod N) (y : W) : T.embedding s y ^ m = T.embedding s y := by
    rw [hm, T.embedding_pow_q_pow]
  subst h_pow
  refine algHom_ext fun y ↦ ?_
  simp [polyAction_X, sum_pow_char_pow, mul_pow, ← C_pow, letterMatrix, h_fixed]

/-- Let `T` be a Frobenius cycle from the local ring `W` to the field `K`: ring maps `ι s : W → K`,
one for each letter `s ∈ ℤ/N`, with `ι (s + 1) ≡ ι s ^ P` modulo the prime `T.p`. A matrix
`g ∈ GL_k(W)` acts on polynomials in the variables `x (b, s)`, `b < k`, by the linear substitution
`T.polyAction g`, given in the letter `s` by `ι s g` for even `s` and by `ι s` of the inverse
transpose of `g` for odd `s`. This action keeps the degree in each letter: if `x ^ ε` occurs in the
translate by `g` of the monomial `x ^ γ`, then `ε` and `γ` have the same degree in the letter
`s`. -/
lemma FrobeniusCycle.sum_eq_of_coeff_polyAction_monomial (T : FrobeniusCycle N W K)
    {g : GL (Fin k) W} {γ ε : Fin k × ZMod N →₀ ℕ}
    (hε : (T.polyAction g (monomial γ 1)).coeff ε ≠ 0) (s : ZMod N) :
    ∑ b : Fin k, ε (b, s) = ∑ b : Fin k, γ (b, s) := by
  -- The translate is a product of powers of linear forms, each in the variables of one letter,
  -- so it is homogeneous for the weight `c` that counts the degree in the letter `s`.
  let c (x : Fin k × ZMod N) : ℕ := if x.2 = s then 1 else 0
  have h_linear (x : Fin k × ZMod N) : IsWeightedHomogeneous c (T.polyAction g (X x)) (c x) := by
    rw [polyAction_X]
    exact .sum _ _ _ fun b _ ↦ (isWeightedHomogeneous_X K c (b, x.2)).C_mul _
  have h_homogeneous : IsWeightedHomogeneous c (T.polyAction g (monomial γ 1))
      (∑ x : Fin k × ZMod N, γ x • c x) := by
    simpa [monomial_eq, Finsupp.prod_pow] using
      IsWeightedHomogeneous.prod univ _ _ fun x _ ↦ (h_linear x).pow (γ x)
  simpa [c, weight_eq_sum, sum_prod_type] using h_homogeneous hε

/-! ### Powers -/

/-- An exponent in the class `u` modulo `m` whose degree in each letter `s` lies in
`[m k, m k + m]`: the number `m (k - ⌊(∑ b, u (b, s)) / m⌋)` is added to the entry of `u` at the
index `(a, s)`. -/
noncomputable def residueExponent (a : Fin k) {m : ℕ} (u : Fin k × ZMod N → Fin m) :
    Fin k × ZMod N →₀ ℕ :=
  equivFunOnFinite.symm fun x : Fin k × ZMod N ↦
    u x + m * if x.1 = a then k - (∑ b : Fin k, (u (b, x.2)).val) / m else 0

/-- The exponent `New.residueExponent a u` lies in the class `u` modulo `m`. -/
lemma residueExponent_mod (a : Fin k) {m : ℕ} (u : Fin k × ZMod N → Fin m) (x : Fin k × ZMod N) :
    residueExponent a u x % m = u x := by
  rw [residueExponent, equivFunOnFinite_symm_apply_apply, Nat.add_mul_mod_self_left,
    mod_eq_of_lt (u x).is_lt]

/-- The exponent `residueExponent a u` has the entries `u (b, s) < m`, with `m (k - ⌊d / m⌋)` added
where `b = a`, for `d = ∑ b, u (b, s)`. Its degree in each letter `s` lies in `[m k, m k + m]`. -/
lemma sum_residueExponent_mem_Icc (a : Fin k) {m : ℕ} (u : Fin k × ZMod N → Fin m) (s : ZMod N) :
    ∑ b : Fin k, residueExponent a u (b, s) ∈ Set.Icc (m * k) (m * k + m) := by
  set d : ℕ := ∑ b : Fin k, (u (b, s)).val with hd
  have h_sum : ∑ b : Fin k, residueExponent a u (b, s) = d + m * (k - d / m) := by
    simp [residueExponent, sum_add_distrib, hd]
  have h_le : d ≤ m * k :=
    calc d ≤ ∑ _b : Fin k, m := sum_le_sum fun b _ ↦ (u (b, s)).is_lt.le
      _ = m * k := by simp [mul_comm]
  have h_split : m * (k - d / m) + m * (d / m) = m * k := by
    rw [← mul_add, Nat.sub_add_cancel (Nat.div_le_of_le_mul h_le)]
  have h_div : m * (d / m) + d % m = d := Nat.div_add_mod d m
  have h_mod : d % m < m := Nat.mod_lt d (u (a, s)).pos
  rw [h_sum, Set.mem_Icc]
  omega

/-- Packing of a family `F` of forms of degree `n` in each letter, one for each class `u` of
exponents modulo `m`, into the polynomial `∑ u, F u (x ^ m) * x ^ γ u`, with
`γ u = New.residueExponent a u`. -/
noncomputable def powerPacking (a : Fin k) (n m : ℕ) :
    ((Fin k × ZMod N → Fin m) → Exponents N k n → K) →ₗ[K] MvPolynomial (Fin k × ZMod N) K :=
  ∑ u : Fin k × ZMod N → Fin m, .mulRight K (monomial (residueExponent a u) 1) ∘ₗ
    (expand m).toLinearMap ∘ₗ polyOfCoeffs ∘ₗ .proj u

/-- Substituting `x ^ m` for the variables `x` in the form with coefficients `G` multiplies its
exponents by `m`. -/
lemma expand_polyOfCoeffs {n : ℕ} (m : ℕ) (G : Exponents N k n → K) :
    expand m (polyOfCoeffs G) = ∑ δ : Exponents N k n, monomial (m • exponentOf δ) (G δ) := by
  simp [polyOfCoeffs, expand_monomial]

lemma powerPacking_apply {n m : ℕ} {a : Fin k}
    {F : (Fin k × ZMod N → Fin m) → Exponents N k n → K} :
    powerPacking a n m F = ∑ u : Fin k × ZMod N → Fin m,
      expand m (polyOfCoeffs (F u)) * monomial (residueExponent a u) 1 := by
  simp [powerPacking]

/-- Let `F u` be forms of degree `n` in each letter `s ∈ ℤ/N`, one for each class `u` of exponents
modulo `m`. They are packed into `powerPacking a n m F = ∑ u, F u (x ^ m) * x ^ γ u`. Here
`γ u = residueExponent a u` is `u` with multiples of `m` added at the index `(a, s)` in each letter
`s`. The terms do not interfere: the coefficient of the packed polynomial at
`m • exponentOf β + γ u` is the coefficient of `F u` at `β`. -/
lemma coeff_powerPacking {n m : ℕ} {a : Fin k}
    {F : (Fin k × ZMod N → Fin m) → Exponents N k n → K}
    (u : Fin k × ZMod N → Fin m) (β : Exponents N k n) :
    (powerPacking a n m F).coeff (m • exponentOf β + residueExponent a u) = F u β := by
  have h_class (v : Fin k × ZMod N → Fin m) (δ : Exponents N k n)
      (h_eq : m • exponentOf δ + residueExponent a v = m • exponentOf β + residueExponent a u) :
      v = u := by
    ext x
    simpa [Nat.mul_add_mod, residueExponent_mod] using congrArg (· x % m) h_eq
  simp only [powerPacking_apply, expand_polyOfCoeffs, Finset.sum_mul, monomial_mul_monomial,
    mul_one, coeff_sum, coeff_monomial]
  rw [Fintype.sum_eq_single u fun v hv ↦
    sum_eq_zero fun δ _ ↦ ite_eq_right fun h_eq ↦ hv (h_class v δ h_eq)]
  simp [(u (a, 0)).pos.ne']

/-- Let `T` be a Frobenius cycle from the local ring `W` to the field `K` of characteristic `T.p`:
ring maps `ι s : W → K`, one for each letter `s ∈ ℤ/N`, with `ι (s + 1) ≡ ι s ^ P` modulo the prime
`T.p`. Here `P = T.P` is a power of `T.p`, the residue field of `W` has `q = T.q = P ^ N` elements,
and the letters are alternately even and odd (`T.isEven`). A matrix `g ∈ GL_k(W)` acts on
polynomials in the variables `x (b, s)`, `b < k`, by the linear substitution `T.polyAction g`, given
in the letter `s` by `ι s g` for even `s` and by `ι s` of the inverse transpose of `g` for odd `s`.
Let `m` be a power of `q`. The forms `F u`, of degree `n` in each letter, are packed into
`powerPacking a n m F = ∑ u, F u (x ^ m) * x ^ γ u`, where `γ u = residueExponent a u` is the vector
`u` of residues modulo `m` with `m (k - ⌊(∑ b, u (b, s)) / m⌋)` added at each index `(a, s)`.
Translating by `g` replaces each monomial `x ^ γ u` by its translate and each `F u` by its
translate, which has the coefficients `T.letterRep n g *ᵥ F u`; here `T.letterRep n g` is the matrix
of the action on such forms. -/
lemma FrobeniusCycle.polyAction_powerPacking (T : FrobeniusCycle N W K) {n m j : ℕ} {a : Fin k}
    {g : GL (Fin k) W} {F : (Fin k × ZMod N → Fin m) → Exponents N k n → K} [CharP K T.p]
    (hm : m = T.q ^ j) :
    T.polyAction g (powerPacking a n m F) =
      ∑ u : Fin k × ZMod N → Fin m, ∑ δ : Exponents N k n,
        monomial (m • exponentOf δ) ((T.letterRep n g *ᵥ F u) δ) *
          T.polyAction g (monomial (residueExponent a u) 1) := by
  have h_comm (f : MvPolynomial (Fin k × ZMod N) K) :
      T.polyAction g (expand m f) = expand m (T.polyAction g f) :=
    AlgHom.congr_fun (T.polyAction_commute_expand hm g).eq f
  simp only [powerPacking_apply, map_sum, map_mul, h_comm, polyAction_polyOfCoeffs,
    expand_polyOfCoeffs (m := m) (G := T.letterRep n g *ᵥ _), Finset.sum_mul]

/-- Let `T` be a Frobenius cycle over a field `K` of characteristic `T.p`, and let `m` be a power of
the number `T.q` of elements of the residue field of `W`. The forms `F u`, of degree `n` in each
letter, are packed into `powerPacking a n m F = ∑ u, F u (x ^ m) * x ^ γ u`, where the exponent
`γ u` is the class `u` modulo `m` with multiples of `m` added at the index `a`. Each exponent `α` of
the translate of this polynomial by `g ∈ GL_k(W)` is `m δ + ε`, where `δ` is an exponent of the
translate `T.letterRep n g *ᵥ F u` of some `F u` and `ε` has degree in `[m k, m k + m]` in each
letter. -/
lemma FrobeniusCycle.exists_eq_add_of_coeff_polyAction_powerPacking (T : FrobeniusCycle N W K)
    {n m j : ℕ} {a : Fin k} {g : GL (Fin k) W} {α : Fin k × ZMod N →₀ ℕ}
    {F : (Fin k × ZMod N → Fin m) → Exponents N k n → K} [CharP K T.p] (hm : m = T.q ^ j)
    (hα : (T.polyAction g (powerPacking a n m F)).coeff α ≠ 0) :
    ∃ (u : Fin k × ZMod N → Fin m) (δ : Exponents N k n) (ε : Fin k × ZMod N →₀ ℕ),
      α = m • exponentOf δ + ε ∧
      (T.letterRep n g *ᵥ F u) δ ≠ 0 ∧
      ∀ s : ZMod N, ∑ b : Fin k, ε (b, s) ∈ Set.Icc (m * k) (m * k + m) := by
  classical
  obtain ⟨u, δ, hδ⟩ : ∃ (u : Fin k × ZMod N → Fin m) (δ : Exponents N k n),
      (monomial (m • exponentOf δ) ((T.letterRep n g *ᵥ F u) δ) *
        T.polyAction g (monomial (residueExponent a u) 1)).coeff α ≠ 0 := by
    by_contra! h_zero
    simp [T.polyAction_powerPacking hm, h_zero] at hα
  obtain ⟨ε, rfl⟩ : ∃ ε, α = m • exponentOf δ + ε := le_iff_exists_add.1 <| by
    by_contra h_not_le
    simp [coeff_monomial_mul', h_not_le] at hδ
  rw [coeff_monomial_mul] at hδ
  refine ⟨u, δ, ε, rfl, left_ne_zero_of_mul hδ, fun s ↦ ?_⟩
  rw [T.sum_eq_of_coeff_polyAction_monomial (right_ne_zero_of_mul hδ) s]
  exact sum_residueExponent_mem_Icc a u s

/-- Let `T` be a Frobenius cycle over a field `K` of characteristic `T.p`, and let `m` be a power of
the number `T.q` of elements of the residue field of `W`. The forms `F u`, of degree `n` in each
letter, are packed into `powerPacking a n m F = ∑ u, F u (x ^ m) * x ^ γ u`, where the exponent
`γ u` is the class `u` modulo `m` with multiples of `m` added at the index `a`. Each exponent `α` of
the translate of this polynomial by `g ∈ GL_k(W)` has degree in `[m (n + k), m (n + k + 1)]` in each
letter `s`. -/
lemma FrobeniusCycle.sum_mem_Icc_of_coeff_polyAction_powerPacking (T : FrobeniusCycle N W K)
    {n m j : ℕ} {a : Fin k} {g : GL (Fin k) W} {α : Fin k × ZMod N →₀ ℕ}
    {F : (Fin k × ZMod N → Fin m) → Exponents N k n → K} [CharP K T.p] (hm : m = T.q ^ j)
    (hα : (T.polyAction g (powerPacking a n m F)).coeff α ≠ 0) (s : ZMod N) :
    ∑ b : Fin k, α (b, s) ∈ Set.Icc (m * (n + k)) (m * (n + k + 1)) := by
  obtain ⟨u, δ, ε, rfl, -, hε⟩ := T.exists_eq_add_of_coeff_polyAction_powerPacking hm hα
  have h_deg : ∑ b : Fin k, exponentOf δ (b, s) = n := by
    simpa [exponentOf, degree_eq_sum] using (δ s).degree_eq
  have h_sum : ∑ b : Fin k, (m • exponentOf δ + ε) (b, s) = m * n + ∑ b : Fin k, ε (b, s) := by
    simp [sum_add_distrib, ← h_deg, Finset.mul_sum]
  have h_range := Set.mem_Icc.1 (hε s)
  rw [h_sum, Set.mem_Icc]
  constructor <;> linarith

/-- Let `m` be a power of `q`, let `L = levi W (twoBlock k a')` be the group of block diagonal
matrices with blocks `a'` and `k - a'`, and let `g ∈ L`. Let the `F u` lie in
`T.defectConditions n a a' ⊥ h`, the space of forms of degree `n` in each letter whose translates by
`L` have coefficient in the ideal `⊥`, that is `0`, at every exponent of defect above `h` along
`(a, a')` at some letter. Then each exponent `α` of the translate by `g` of the packed polynomial
`∑ u, F u (x ^ m) * x ^ residueExponent a u` has defect at most `m (h + 2 (k + 1))` along `(a, a')`,
at every letter `i`. -/
lemma FrobeniusCycle.weight_defectWeight_le_of_coeff_polyAction_powerPacking
    (T : FrobeniusCycle N W K) {n m j : ℕ} {a a' : Fin k} {h : ℝ} {g : GL (Fin k) W}
    {α : Fin k × ZMod N →₀ ℕ} {F : (Fin k × ZMod N → Fin m) → Exponents N k n → K} [CharP K T.p]
    (hm : m = T.q ^ j) (hF : ∀ u : Fin k × ZMod N → Fin m, F u ∈ T.defectConditions n a a' ⊥ h)
    (hg : g ∈ levi W (twoBlock k a')) (hα : (T.polyAction g (powerPacking a n m F)).coeff α ≠ 0)
    (i : ZMod N) :
    weight (T.defectWeight i a a') α ≤ m * (h + 2 * (k + 1)) := by
  obtain ⟨u, δ, ε, rfl, hδ, hε⟩ := T.exists_eq_add_of_coeff_polyAction_powerPacking hm hα
  have hδ_le : weight (T.defectWeight i a a') (exponentOf δ) ≤ h :=
    not_lt.1 fun h_lt ↦ hδ (hF u g hg δ ⟨i, h_lt⟩)
  have hε_le : |weight (T.defectWeight i a a') ε| ≤ 2 * (m * k + m) :=
    T.abs_weight_defectWeight_le fun s ↦ mod_cast (hε s).2
  rw [map_add, map_nsmul, nsmul_eq_mul]
  linarith [mul_le_mul_of_nonneg_left hδ_le (cast_nonneg m), le_of_abs_le hε_le]

/-! ### Least height -/

/-- Let the height of a variable be its row index at even letters and minus its row index at odd
letters. In characteristic `T.p`, a matrix `g` that is lower triangular modulo the maximal ideal
sends the variable `u` to a multiple of itself, by a diagonal entry of `T.letterMatrix u.2 g`, plus
a linear combination of variables of height at least `height u + 1`. The latter is stated as
membership in the Gauss filtration for the heights and the powers of the square root
`T.sqrtPrime = 0` of `T.p`. -/
lemma FrobeniusCycle.polyAction_X_sub_mem_gaussFiltration (T : FrobeniusCycle N W K) [CharP K T.p]
    {g : GL (Fin k) W} (hg : g ∈ parahoric W Fin.val) {height : Fin k × ZMod N → ℝ}
    (h_height : ∀ y : Fin k × ZMod N, height y = if T.isEven y.2 then (y.1 : ℝ) else -y.1)
    (u : Fin k × ZMod N) :
    T.polyAction g (X u) - C (T.letterMatrix u.2 g u.1 u.1) * X u ∈
      gaussFiltration (adicFiltration T.sqrtPrime) height (height u + 1) := by
  rw [polyAction_X, ← Finset.add_sum_erase _ _ (Finset.mem_univ u.1), add_sub_cancel_left]
  simp_rw [C_mul_X_eq_monomial]
  refine sum_mem fun c hc ↦ monomial_mem_gaussFiltration (mem_adicFiltration_of_nonpos ?_)
  intro (h_ne : T.letterMatrix u.2 g c u.1 ≠ 0)
  -- An entry on the wrong side of the diagonal is divisible by `p = 0`.
  have h_not_dvd : ¬(T.p : K) ∣ T.letterMatrix u.2 g c u.1 := by
    simpa [CharP.cast_eq_zero K T.p] using h_ne
  have hc_ne : c.val ≠ u.1.val := Fin.val_ne_of_ne (ne_of_mem_erase hc)
  have h_greater : height u + 1 ≤ height (c, u.2) := by
    cases h_even : T.isEven u.2 with
    | true =>
      have h_side : u.1.val + 1 ≤ c.val := hc_ne.symm.lt_of_le <| not_lt.1 fun h_lt ↦
        h_not_dvd (T.p_dvd_letterMatrix_of_mem_parahoric_of_isEven u.2 hg h_even h_lt)
      simpa [h_height, h_even] using (mod_cast h_side : (u.1.val + 1 : ℝ) ≤ c.val)
    | false =>
      have h_side : c.val + 1 ≤ u.1.val := hc_ne.lt_of_le <| not_lt.1 fun h_lt ↦
        h_not_dvd (T.p_dvd_letterMatrix_of_mem_parahoric_of_not_isEven u.2 hg h_even h_lt)
      simp only [h_height, h_even, Bool.false_eq_true, ite_false]
      linarith [(mod_cast h_side : (c.val + 1 : ℝ) ≤ u.1.val)]
  simpa [weight_single] using h_greater

/-- Let the height of a variable be its row index at even letters and minus its row index at odd
letters, and let all terms of `f` have height at least that of `α`. In characteristic `T.p`, a
matrix `g` that is lower triangular modulo the maximal ideal multiplies the coefficient of `f` at
`α` by a product of diagonal entries, because it sends each monomial to a multiple of itself plus
monomials of greater height. -/
lemma FrobeniusCycle.coeff_polyAction_of_mem_parahoric (T : FrobeniusCycle N W K) [CharP K T.p]
    {g : GL (Fin k) W} (hg : g ∈ parahoric W Fin.val) {height : Fin k × ZMod N → ℝ}
    (h_height : ∀ y : Fin k × ZMod N, height y = if T.isEven y.2 then (y.1 : ℝ) else -y.1)
    {f : MvPolynomial (Fin k × ZMod N) K} {α : Fin k × ZMod N →₀ ℕ}
    (hf : f ∈ gaussFiltration (adicFiltration T.sqrtPrime) height (weight height α)) :
    (T.polyAction g f).coeff α =
      (∏ u : Fin k × ZMod N, T.letterMatrix u.2 g u.1 u.1 ^ α u) * f.coeff α := by
  -- Compare `g` with its diagonal part `diag`; the two differ by terms of greater height.
  let d (u : Fin k × ZMod N) : K := T.letterMatrix u.2 g u.1 u.1
  let diag : MvPolynomial (Fin k × ZMod N) K →ₐ[K] MvPolynomial (Fin k × ZMod N) K :=
    aeval fun u ↦ C (d u) * X u
  have h_diag (f' : MvPolynomial (Fin k × ZMod N) K) :
      (diag f').coeff α = (∏ u : Fin k × ZMod N, d u ^ α u) * f'.coeff α := by
    induction f' using MvPolynomial.induction_on' with
    | monomial γ c =>
      have h_monomial : diag (monomial γ c) = monomial γ ((∏ u, d u ^ γ u) * c) := by
        simp [diag, monomial_eq, Finsupp.prod_pow, mul_pow, prod_mul_distrib, mul_comm,
          mul_left_comm]
      rw [h_monomial, coeff_monomial, coeff_monomial]
      split_ifs with h_eq <;> simp [h_eq]
    | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂, mul_add]
  have h_level (u : Fin k × ZMod N) :
      diag (X u) ∈ gaussFiltration (adicFiltration T.sqrtPrime) height (height u) := by
    rw [aeval_X, C_mul_X_eq_monomial]
    exact monomial_mem_gaussFiltration
      (mem_adicFiltration_of_nonpos fun _ ↦ by simp [weight_single])
  -- The gain `1` is weakened to the gain `20⁻¹` of `algHom_sub_mem_of_mem_gaussFiltration`.
  have h_higher (u : Fin k × ZMod N) : T.polyAction g (X u) - diag (X u) ∈
      gaussFiltration (adicFiltration T.sqrtPrime) height (height u + 20⁻¹) := by
    simpa [diag] using IsRealFiltration.antitone (by linarith)
      (T.polyAction_X_sub_mem_gaussFiltration hg h_height u)
  have h_gain : T.polyAction g f - diag f ∈
      gaussFiltration (adicFiltration T.sqrtPrime) height (weight height α + 20⁻¹) :=
    (algHom_sub_mem_of_mem_gaussFiltration diag _ hf h_level _ h_higher C_mem_gaussFiltration).right
  -- As `T.sqrtPrime = 0`, a coefficient of positive order vanishes.
  have sqrtPrime_eq_zero : T.sqrtPrime = 0 := (pow_eq_zero_iff two_ne_zero).1
    (T.sqrtPrime_sq.trans (CharP.cast_eq_zero K _))
  have h_dvd : T.sqrtPrime ^ ⌈weight height α + 20⁻¹ - weight height α⌉₊ ∣
      (T.polyAction g f - diag f).coeff α :=
    mem_adicFiltration_iff.1 (mem_gaussFiltration_iff.1 h_gain α)
  simpa [sqrtPrime_eq_zero, sub_eq_zero, h_diag] using h_dvd

/-- Let `L = levi W τ` be the group of matrices whose entry `(b, c)` vanishes for `τ b ≠ τ c`, and
let `R` represent the right cosets in `L` of its intersection with the lower Iwahori subgroup
`parahoric W Fin.val` of matrices that are lower triangular modulo the maximal ideal. Some translate
of a polynomial `f ≠ 0` by an element `x` of `R` has an exponent `α` of defect at most `0` along all
simple roots `(b, b + 1)` with `τ b = τ (b + 1)`, at all letters. -/
lemma FrobeniusCycle.exists_coeff_ne_zero_weight_defectWeight_nonpos (T : FrobeniusCycle N W K)
    [CharP K T.p] {τ : Fin k → ℕ} {R : Set (levi W τ)}
    (hR : IsComplement ((parahoric W Fin.val).subgroupOf (levi W τ) : Set (levi W τ)) R)
    {f : MvPolynomial (Fin k × ZMod N) K} (hf : f ≠ 0) :
    ∃ (x : R) (α : Fin k × ZMod N →₀ ℕ), (T.polyAction x f).coeff α ≠ 0 ∧
      ∀ (i : ZMod N) (b b' : Fin k), b.val + 1 = b' → τ b = τ b' →
        weight (T.defectWeight i b b') α ≤ 0 := by
  -- Take a term of least height among all translates of `f` by `L`. It occurs at a representative,
  -- and `weight_defectWeight_nonpos_of_least` applies to each simple root inside a block.
  let height (y : Fin k × ZMod N) : ℝ := if T.isEven y.2 then y.1 else -y.1
  let S : Set (Fin k × ZMod N →₀ ℕ) := {α | ∃ g ∈ levi W τ, (T.polyAction g f).coeff α ≠ 0}
  have h_finite : S.Finite := (finite_of_degree_le f.totalDegree).subset fun α ⟨g, _, hα⟩ ↦
    (le_totalDegree (MvPolynomial.mem_support_iff.2 hα)).trans (T.totalDegree_polyAction_le g f)
  have h_nonempty : S.Nonempty :=
    (MvPolynomial.support_nonempty.2 hf).imp fun α hα ↦ ⟨1, one_mem _, by simpa using hα⟩
  obtain ⟨α, ⟨g, hg, hα⟩, h_min⟩ := Set.exists_min_image S (weight height) h_finite h_nonempty
  have h_least (g' : GL (Fin k) W) (hg' : g' ∈ levi W τ) :
      T.polyAction g' f ∈ gaussFiltration (adicFiltration T.sqrtPrime) height (weight height α) :=
    fun α' ↦ mem_adicFiltration_of_nonpos fun hα' ↦ sub_nonpos.2 (h_min α' ⟨g', hg', hα'⟩)
  -- Write `g = y x` with `y` lower triangular modulo the maximal ideal and `x` in `R`. No term of
  -- the translate by `x` has smaller height, so the coefficient for `g` is a multiple of the one
  -- for `x`.
  obtain ⟨⟨y, x⟩, hyx⟩ := hR.2 ⟨g, hg⟩
  have h_occurs : (T.polyAction x f).coeff α ≠ 0 := by
    rw [show g = y * x from congrArg Subtype.val hyx.symm, map_mul, AlgHom.mul_apply,
      T.coeff_polyAction_of_mem_parahoric (Subgroup.mem_subgroupOf.1 y.2) (fun _ ↦ rfl)
        (h_least x x.val.property)] at hα
    exact right_ne_zero_of_mul hα
  refine ⟨x, α, h_occurs, fun i b b' hb h_block ↦ ?_⟩
  have h_ne : b ≠ b' := fun h_eq ↦ by simp [h_eq] at hb
  have h_step (s : ZMod N) : height (T.rootVar b b' s) - height (T.rootVar b' b s) = 1 := by
    cases h_even : T.isEven s <;> simp [height, rootVar, h_even, ← hb]
  refine T.weight_defectWeight_nonpos_of_least i h_ne h_step (fun g' hg' ↦ ?_) h_occurs
  rw [← AlgHom.mul_apply, ← map_mul]
  exact h_least _ (mul_mem (rootSL_le_levi h_block hg') x.val.property)

/-! ### The shift -/

/-- The defect of a vector `β` indexed by `(b, s) ∈ Fin k × ZMod N`, at the letter `i` along the
root `(a, a')`, is the linear form with coefficients `T.defectWeight i a a'`, namely `β v + ∑ s, ± P
^ ((s - i) mod N) * (β (a', s) - β (a, s)) / (q - 1)`, with the sign `+` at even `s`, where
`v = T.rootVar a a' i` is `(a', i)` for even `i` and `(a, i)` for odd `i`. Let
`β = permStep T.isEven T.P 1 ν`, that is, `β (b, s) = ± (P * ν (b, s + 1) - ν (b, s))` with the same
signs. Then the defect of `β` is `β v - (ν (a, i) - ν (a', i))`. -/
lemma FrobeniusCycle.defectWeight_dotProduct_permStep (T : FrobeniusCycle N W K) {a a' : Fin k}
    (i : ZMod N) (ν : Fin k × ZMod N → ℝ) :
    T.defectWeight i a a' ⬝ᵥ permStep T.isEven T.P 1 ν =
      permStep T.isEven T.P 1 ν (T.rootVar a a' i) - (ν (a, i) - ν (a', i)) := by
  -- Each letter `s` contributes `telescope (s - 1) - telescope s`, and these terms cancel in the
  -- sum over all letters. The letter `i` contributes the right side in addition.
  have hq : ((T.p : ℝ) ^ T.frobExp) ^ N - 1 ≠ 0 := mod_cast (sub_pos.2 T.one_lt_q).ne'
  let telescope (s : ZMod N) : ℝ :=
    T.P ^ (1 + (s - i).val) * (ν (a, s + 1) - ν (a', s + 1)) / (T.q - 1)
  have h_prev (s : ZMod N) : telescope (s - 1) =
      T.P ^ (if s = i then N else (s - i).val) * (ν (a, s) - ν (a', s)) / (T.q - 1) := by
    simp [telescope, one_add_val_sub_one_sub]
  have h_letter (s : ZMod N) :
      ∑ b : Fin k, T.defectWeight i a a' (b, s) * permStep T.isEven T.P 1 ν (b, s) =
        telescope (s - 1) - telescope s +
        if s = i then permStep T.isEven T.P 1 ν (T.rootVar a a' i) - (ν (a, i) - ν (a', i))
        else 0 := by
    rw [h_prev]
    simp only [telescope, defectWeight, rootVar, one_add_val_sub_one_sub]
    -- Only the rows a and a' contribute; the cases are s = i or not, and the parity of s.
    rcases eq_or_ne s i with rfl | hs <;> by_cases h_even : T.isEven s <;>
      simp [div_eq_mul_inv, sub_mul, *] <;> field
  have h_circle : ∑ s : ZMod N, telescope (s - 1) = ∑ s : ZMod N, telescope s :=
    (Equiv.subRight 1).sum_comp telescope
  rw [dotProduct, Fintype.sum_prod_type_right, sum_congr rfl fun s _ ↦ h_letter s]
  simp [sum_add_distrib, h_circle, -permStep_apply]

/-- There is an integral vector `σ ≥ 0` of degree `∑ b, σ (b, s)` at most `P ^ (2 (a + 1)) - 1` in
each letter `s` that lies in `T.defectCone a (-1)`: its defect, at every letter, is at most `-1`
along `(a, a + 1)` and at most `0` along the other simple roots `(b, b + 1)`. -/
lemma FrobeniusCycle.exists_mem_defectCone_sum_le (T : FrobeniusCycle N W K) (a : Fin k) :
    ∃ σ ∈ T.defectCone a (-1),
      0 ≤ σ ∧
      (∀ x : Fin k × ZMod N, ∃ z : ℤ, σ x = z) ∧
      ∀ s : ZMod N, ∑ b : Fin k, σ (b, s) ≤ (T.P ^ (2 * (a.val + 1)) - 1 : ℝ) := by
  -- Let `μ = (P ^ (2 a), …, P ^ 2, 1, 0, …, 0)`, and let `ν` be `μ` at even and `P μ` at odd
  -- letters. Then `σ = permStep ν` is `(P ^ 2 - 1) μ` at even and `0` at odd letters.
  have hP_sq : (0 : ℝ) ≤ T.P ^ 2 - 1 := sub_nonneg.2 (one_le_pow₀ T.one_lt_P.le)
  let μ (b : Fin k) : ℝ := if b ≤ a then (T.P ^ 2) ^ (a.val - b) else 0
  let ν (x : Fin k × ZMod N) : ℝ := (if T.isEven x.2 then 1 else T.P : ℝ) * μ x.1
  have hμ_nonneg (b : Fin k) : 0 ≤ μ b := ite_nonneg (by positivity) le_rfl
  have hμ_sum : ∑ b : Fin k, μ b = ∑ j ∈ range (a.val + 1), (T.P ^ 2 : ℝ) ^ j := by
    simp only [μ, Fin.le_def]
    rw [Fin.sum_univ_eq_sum_range fun j : ℕ ↦ if j ≤ a.val then _ ^ (a.val - j) else (0 : ℝ),
      ← sum_filter, show (range k).filter (· ≤ a.val) = range (a.val + 1) by grind]
    exact sum_range_reflect (fun j : ℕ ↦ (T.P ^ 2 : ℝ) ^ j) (a.val + 1)
  have hμ_succ (b b' : Fin k) (hb : b.val + 1 = b') :
      μ b = T.P ^ 2 * μ b' + if b = a then 1 else 0 := by
    rcases lt_trichotomy b a with h_lt | rfl | h_gt
    · simp only [μ, ite_eq_left h_lt.le, ite_eq_left (show b' ≤ a by omega), ite_eq_right h_lt.ne,
        show a.val - b = (a.val - b') + 1 by omega]
      ring
    · simp [μ, show ¬b' ≤ b by omega]
    · simp [μ, h_gt.ne', show ¬b' ≤ a by omega, h_gt.not_ge]
  have hσ (b : Fin k) (i : ZMod N) :
      permStep T.isEven T.P 1 ν (b, i) = if T.isEven i then (T.P ^ 2 - 1) * μ b else 0 := by
    by_cases h_even : T.isEven i <;> simp [ν, T.isEven_succ, h_even]; ring
  refine ⟨permStep T.isEven T.P 1 ν, fun i b b' hb ↦ ?_, fun (b, i) ↦ ?_, fun (b, i) ↦ ?_,
    fun s ↦ ?_⟩
  · -- The defects are `P ^ 2 μ b' - μ b` at even and `P (μ b' - μ b)` at odd letters.
    have h_gap : 0 ≤ (T.P ^ 2 - 1) * μ b' := mul_nonneg hP_sq (hμ_nonneg b')
    rw [defectWeight_dotProduct_permStep]
    by_cases h_even : T.isEven i
    · simp only [rootVar, hσ, ν, h_even, ite_true, hμ_succ b b' hb]
      split_ifs <;> linarith
    · simp only [rootVar, hσ, ν, h_even, Bool.false_eq_true, ite_false, hμ_succ b b' hb]
      split_ifs <;> nlinarith
  · rw [hσ]
    exact ite_nonneg (mul_nonneg hP_sq (hμ_nonneg b)) le_rfl
  · refine ⟨if T.isEven i ∧ b ≤ a then (T.P ^ 2 - 1) * (T.P ^ 2) ^ (a.val - b) else 0, ?_⟩
    simp only [hσ, μ]
    by_cases h_even : T.isEven i <;> by_cases hb : b ≤ a <;> simp [h_even, hb]
  · simp only [hσ]
    split_ifs
    · rw [← Finset.mul_sum, hμ_sum, mul_geom_sum, pow_mul]
    · rw [sum_const_zero]
      exact sub_nonneg.2 (one_le_pow₀ T.one_lt_P.le)

/-- The slab `degreeSlab k D` is the set of vectors `β ≥ 0` with degree `∑ b, β (b, s)` in
`[D s - 1, D s]` for each letter `s`. Let `h ≥ 0`, and let `σ ≥ 0` lie in `T.defectCone a (-1)`.
Adding `h σ` to a vector `β` of `T.defectCone a h` in the slab of degrees in `[d - 1, d]` gives a
vector of `T.defectCone a 0` in the slab whose degrees are raised by those of `h σ`. -/
lemma FrobeniusCycle.smul_add_mem_defectCone_inter_degreeSlab (T : FrobeniusCycle N W K)
    {a : Fin k} {σ β : Fin k × ZMod N → ℝ} {h d : ℝ} (h_factor : 0 ≤ h)
    (hσ_cone : σ ∈ T.defectCone a (-1)) (hσ_nonneg : 0 ≤ σ)
    (hβ : β ∈ T.defectCone a h ∩ degreeSlab k fun _ : ZMod N ↦ d) :
    h • σ + β ∈
      T.defectCone a 0 ∩ degreeSlab k fun s : ZMod N ↦ d + ∑ b : Fin k, (h • σ) (b, s) := by
  obtain ⟨h_cone, h_nonneg, h_deg⟩ := hβ
  refine ⟨fun i b b' hb ↦ ?_, add_nonneg (smul_nonneg h_factor hσ_nonneg) h_nonneg, fun s ↦ ?_⟩
  · have hβ_le : T.defectWeight i b b' ⬝ᵥ β ≤ if b = a then h else 0 := h_cone i b b' hb
    have hσ_le : h * T.defectWeight i b b' ⬝ᵥ σ ≤ h * if b = a then -1 else 0 :=
      mul_le_mul_of_nonneg_left (hσ_cone i b b' hb) h_factor
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, ite_self]
    split_ifs at hβ_le hσ_le <;> linarith
  · obtain ⟨h_low, h_up⟩ := h_deg s
    simp only [Pi.add_apply, sum_add_distrib]
    constructor <;> linarith

/-! ### The count -/

/-- Let `T` be a Frobenius cycle from the local ring `W` to the field `K` of characteristic `T.p`:
ring maps `ι s : W → K`, one for each letter `s ∈ ℤ/N`, with `ι (s + 1) ≡ ι s ^ P` modulo the prime
`T.p`. Here `P = T.P` is a power of `T.p`, the residue field of `W` has `q = T.q = P ^ N` elements,
and the letters are alternately even and odd (`T.isEven`). A matrix `g ∈ GL_k(W)` acts on
polynomials in the variables `x (b, s)`, `b < k`, by the linear substitution `T.polyAction g`, given
in the letter `s` by `ι s g` for even `s` and by `ι s` of the inverse transpose of `g` for odd `s`.
The defect of a vector `β` indexed by `(b, s) ∈ Fin k × ZMod N`, at the letter `i` along the root
`(b, b')`, is the linear form with coefficients `T.defectWeight i b b'`, namely
`β v + ∑ s, ± P ^ ((s - i) mod N) * (β (b', s) - β (b, s)) / (q - 1)`, with the sign `+` at even
`s`, and `v = (b', i)` for even `i`, `v = (b, i)` for odd `i`. Let `m` be a power of `q`, let
`a' = a + 1` and `2 (k + 1) ≤ t`, let `L = levi W (twoBlock k a')` be the group of block diagonal
matrices with blocks `a'` and `k - a'`, and let `g ∈ L`. Let the `F u` lie in the space of forms of
degree `n` in each letter whose translates by `L` have coefficient in the ideal `⊥`, that is `0`, at
every exponent of defect above `3 t` along `(a, a')` at some letter. Pack them into
`powerPacking a n m F = ∑ u, F u (x ^ m) * x ^ γ u`, where `γ u = residueExponent a u` is the vector
`u` of residues modulo `m` with `m (k - ⌊(∑ b, u (b, s)) / m⌋)` added at each index `(a, s)`. If an
exponent `α` of the translate of this polynomial by `g` has defect at most `0` along the simple
roots `(b, b + 1)` inside the blocks, then `α / m` has degree in `[n + k, n + k + 1]` in each letter
and lies in `T.defectCone a (4 t)`: its defect is at most `4 t` along `(a, a')` and at most `0`
along the other simple roots. -/
lemma FrobeniusCycle.div_mem_defectCone_inter_degreeSlab (T : FrobeniusCycle N W K) [CharP K T.p]
    {a a' : Fin k} (ha : a.val + 1 = a') {n m j : ℕ} (hm : m = T.q ^ j)
    {t : ℝ} (ht : 2 * (k + 1) ≤ t) {F : (Fin k × ZMod N → Fin m) → Exponents N k n → K}
    (hF : ∀ u : Fin k × ZMod N → Fin m, F u ∈ T.defectConditions n a a' ⊥ (3 * t))
    {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k a')) {α : Fin k × ZMod N →₀ ℕ}
    (hα : (T.polyAction g (powerPacking a n m F)).coeff α ≠ 0)
    (h_nonpos : ∀ (i : ZMod N) (b b' : Fin k), b.val + 1 = b' → twoBlock k a' b = twoBlock k a' b' →
      weight (T.defectWeight i b b') α ≤ 0) :
    (fun y : Fin k × ZMod N ↦ (α y : ℝ) / m) ∈
      T.defectCone a (4 * t) ∩ degreeSlab k fun _ : ZMod N ↦ n + k + 1 := by
  have hm_pos : (0 : ℝ) < m := by simpa [hm] using pow_pos (one_pos.trans T.one_lt_q) j
  refine ⟨fun i b b' hb ↦ ?_, fun _ ↦ by positivity, fun s ↦ ?_⟩
  · have h_dot : (T.defectWeight i b b' ⬝ᵥ fun y ↦ (α y : ℝ) / m) =
        weight (T.defectWeight i b b') α / m := by
      simp [dotProduct, weight_eq_sum, sum_div, mul_div_assoc', mul_comm]
    rw [h_dot, div_le_iff₀' hm_pos]
    split_ifs with hba
    · obtain rfl : b' = a' := by omega
      rw [hba]
      calc weight (T.defectWeight i a b') α ≤ m * (3 * t + 2 * (k + 1)) :=
            T.weight_defectWeight_le_of_coeff_polyAction_powerPacking hm hF hg hα i
        _ ≤ m * (4 * t) := mul_le_mul_of_nonneg_left (by linarith) hm_pos.le
    · have h_block : twoBlock k a' b = twoBlock k a' b' := by grind [twoBlock, Fin.val_inj]
      simpa using h_nonpos i b b' hb h_block
  · obtain ⟨h_low, h_up⟩ := T.sum_mem_Icc_of_coeff_polyAction_powerPacking hm hα s
    rw [← sum_div, ← cast_sum, Set.mem_Icc, le_div_iff₀' hm_pos, div_le_iff₀' hm_pos,
      add_sub_cancel_right]
    beta_reduce
    exact ⟨mod_cast h_low, mod_cast h_up⟩

open Pointwise in
/-- Let `T` be a Frobenius cycle (`New.FrobeniusCycle`) from the local ring `W` to the field `K` of
characteristic `T.p`. It consists of ring maps `ι s : W → K`, one for each letter `s ∈ ℤ/N`, with
`ι (s + 1) ≡ ι s ^ P` modulo the prime `T.p`. Here `P = T.P` is a power of `T.p`, the residue field
of `W` has `q = T.q = P ^ N` elements, and the letters are alternately even and odd (`T.isEven`). A
matrix `g ∈ GL_k(W)` acts on polynomials in the variables `x (b, s)`, `b < k`, by the linear
substitution `T.polyAction g`. In the letter `s` it is given by `ι s g` for even `s` and by `ι s` of
the inverse transpose of `g` for odd `s`. Let `β` be a vector indexed by `(b, s) ∈ Fin k × ZMod N`.
Its defect at the letter `i` along the root `(b, b')` is the linear form with coefficients
`T.defectWeight i b b'`, namely `β v + ∑ s, ± P ^ ((s - i) mod N) * (β (b', s) - β (b, s)) / (q -
1)`. The sign is `+` at even `s`, and `v = (b', i)` for even `i`, `v = (b, i)` for odd `i`. Let `m`
be a power of `q`, let `a' = a + 1` and `t ≥ 2 (k + 1)`. Let `L = levi W (twoBlock k a')` be the
group of block diagonal matrices with blocks `a'` and `k - a'`. Let
`S = T.defectConditions n a a' ⊥ (3 t)` be the space of forms of degree `n` in each letter whose
translates by `L` have coefficient in the ideal `⊥`, that is `0`, at every exponent whose defect
along `(a, a')` is above `3 t` at some letter. Let `σ ≥ 0` be an integral vector of defect at most
`-1` along `(a, a')` and at most `0` along the other simple roots. Let `D s` be `n + k + 1` plus the
degree of `4 t σ` in the letter `s`. Then `m ^ (k N) * dim S` is at most a product of two factors.
The first is the index in `L` of its intersection with the lower Iwahori subgroup
`parahoric W Fin.val`: the matrices whose `(i, j)` entry lies in the maximal ideal when `i < j`. The
second is the number of points of `m⁻¹ ℤ ^ (k N)` in the cone `T.defectCone a 0` of Pieri's
inequalities, cut by the slab of vectors `β ≥ 0` with degrees in `[D s - 1, D s]`. This cone
consists of the vectors whose defect is at most `0` along all simple roots `(b, b + 1)` at all
letters. -/
lemma FrobeniusCycle.finrank_defectConditions_mul_pow_le (T : FrobeniusCycle N W K) [CharP K T.p]
    {a a' : Fin k} (ha : a.val + 1 = a') (n : ℕ) {t : ℕ} (ht : 2 * (k + 1) ≤ t)
    {m j : ℕ} (hm : m = T.q ^ j)
    {σ : Fin k × ZMod N → ℝ} (hσ_cone : σ ∈ T.defectCone a (-1)) (hσ_nonneg : 0 ≤ σ)
    (hσ_int : ∀ x : Fin k × ZMod N, ∃ z : ℤ, σ x = z) {D : ZMod N → ℝ}
    (hD : D = fun s : ZMod N ↦ (n + k + 1 : ℝ) + ∑ b : Fin k, ((4 * t : ℝ) • σ) (b, s)) :
    finrank K (T.defectConditions n a a' ⊥ (3 * t)) * m ^ card (Fin k × ZMod N) ≤
      (parahoric W Fin.val).relIndex (levi W (twoBlock k a')) *
        Nat.card ↥((T.defectCone a 0 ∩ degreeSlab k D) ∩ (m : ℝ)⁻¹ •
          (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k × ZMod N))) :
            Set (Fin k × ZMod N → ℝ))) := by
  -- Pack `m ^ (k N)` forms into one polynomial and list the coefficients of its translates by
  -- representatives `R` of the flags at the exponents `α` with `4 t σ + α / m` in `Λ`. This linear
  -- map is injective.
  set Y : Set (Fin k × ZMod N → ℝ) := T.defectCone a 0 ∩ degreeSlab k D
  set Λ : Set (Fin k × ZMod N → ℝ) := Y ∩ (m : ℝ)⁻¹ •
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k × ZMod N))) : Set (Fin k × ZMod N → ℝ))
  set S : Submodule K (Exponents N k n → K) := T.defectConditions n a a' ⊥ (3 * t)
  have : Finite (IsLocalRing.ResidueField W) := T.finite_residueField
  have hm_pos : 0 < m := by simpa [hm] using pow_pos (pos_of_gt (mod_cast T.one_lt_q : 1 < T.q)) j
  have : NeZero m := ⟨hm_pos.ne'⟩
  obtain ⟨R, hR, -⟩ :=
    ((parahoric W Fin.val).subgroupOf (levi W (twoBlock k a'))).exists_isComplement_right 1
  have : Fintype R := hR.finite_right.fintype
  have : Fintype Λ := ((ZSpan.setFinite_inter _ (isBounded_inter_degreeSlab ..)).subset
    (inf_le_inf_left _ (ZSpan.smul _ (NeZero.ne _)).le)).fintype
  let pack : ((Fin k × ZMod N → Fin m) → S) →ₗ[K] MvPolynomial (Fin k × ZMod N) K :=
    powerPacking a n m ∘ₗ S.subtype.compLeft _
  -- The exponent `m (y - 4 t σ)` of a point `y` of `Λ`, with negative entries replaced by `0`.
  let expAt (y : Λ) : Fin k × ZMod N →₀ ℕ :=
    equivFunOnFinite.symm fun z ↦ ⌊(y.val z - 4 * t * σ z) * m⌋₊
  let Φ : ((Fin k × ZMod N → Fin m) → S) →ₗ[K] R × Λ → K :=
    LinearMap.pi fun (x, y) ↦ lcoeff K (expAt y) ∘ₗ (T.polyAction x).toLinearMap ∘ₗ pack
  suffices h_ker : ∀ F : (Fin k × ZMod N → Fin m) → S, Φ F = 0 → F = 0 by
    simpa [relIndex, ← hR.card_right, mul_comm, finrank_pi_fintype] using
      Φ.finrank_le_finrank_of_injective ((injective_iff_map_eq_zero _).2 h_ker)
  intro F hF
  ext u β
  by_contra hβ
  have h_ne : powerPacking a n m (fun v ↦ (F v).val) ≠ 0 := fun h_zero ↦ hβ <| by
    simpa [h_zero] using (coeff_powerPacking (a := a) (F := fun v ↦ (F v).val) u β).symm
  obtain ⟨x, α, hα, h_nonpos⟩ := T.exists_coeff_ne_zero_weight_defectWeight_nonpos hR h_ne
  have h_cone : (fun y : Fin k × ZMod N ↦ (α y : ℝ) / m) ∈
      T.defectCone a (4 * t) ∩ degreeSlab k fun _ : ZMod N ↦ n + k + 1 :=
    T.div_mem_defectCone_inter_degreeSlab ha hm (mod_cast ht) (fun v ↦ (F v).property)
      x.val.property hα h_nonpos
  -- The shifted point lies in `Y`; as the shift is integral it lies in `Λ`, so the coefficient at
  -- `α` is an entry of `Φ F = 0`.
  have h_lattice : (4 * t : ℝ) • σ + (fun y : Fin k × ZMod N ↦ (α y : ℝ) / m) ∈ Λ := by
    refine ⟨by simpa only [Y, hD] using
      T.smul_add_mem_defectCone_inter_degreeSlab (by positivity) hσ_cone hσ_nonneg h_cone,
      BoxIntegral.unitPartition.mem_smul_span_iff.2 fun y ↦ ?_⟩
    obtain ⟨z, hz⟩ := hσ_int y
    exact ⟨m * (4 * t * z) + α y, by simp [hz, field]⟩
  have h_exp : expAt ⟨_, h_lattice⟩ = α := by ext z; simp [expAt, field]
  have h_entry : (T.polyAction x (pack F)).coeff (expAt ⟨_, h_lattice⟩) = 0 :=
    congrFun hF (x, ⟨_, h_lattice⟩)
  exact hα (by rwa [h_exp] at h_entry)

/-- Let `T` be a Frobenius cycle from the local ring `W` to the field `K` of characteristic `T.p`:
ring maps `ι s : W → K`, one for each letter `s ∈ ℤ/N`, with `ι (s + 1) ≡ ι s ^ P` modulo the prime
`T.p`. Here `P = T.P` is a power of `T.p`, the residue field of `W` has `q = T.q = P ^ N` elements,
and the letters are alternately even and odd (`T.isEven`). A matrix `g ∈ GL_k(W)` acts on
polynomials in the variables `x (b, s)`, `b < k`, by the linear substitution `T.polyAction g`, given
in the letter `s` by `ι s g` for even `s` and by `ι s` of the inverse transpose of `g` for odd `s`.
The defect of a vector `β` indexed by `(b, s) ∈ Fin k × ZMod N`, at the letter `i` along the root
`(b, b')`, is the linear form with coefficients `T.defectWeight i b b'`, namely
`β v + ∑ s, ± P ^ ((s - i) mod N) * (β (b', s) - β (b, s)) / (q - 1)`, with the sign `+` at even
`s`, and `v = (b', i)` for even `i`, `v = (b, i)` for odd `i`. Let `a' = a + 1` and `t ≥ 2 (k + 1)`,
and let `L = levi W (twoBlock k a')` be the group of block diagonal matrices with blocks `a'` and
`k - a'`. Let `S = T.defectConditions n a a' ⊥ (3 t)` be the space of forms of degree `n` in each
letter whose translates by `L` have coefficient in the ideal `⊥`, that is `0`, at every exponent of
defect above `3 t` along `(a, a')` at some letter. There are degrees `D s` in
`[1, n + 4 t P ^ (2 a')]` such that `dim S` is at most the index in `L` of its intersection with the
lower Iwahori subgroup `parahoric W Fin.val` of matrices that are lower triangular modulo the
maximal ideal, times the volume of the cone `T.defectCone a 0` of Pieri's inequalities (defect at
most `0` along all simple roots `(b, b + 1)` at all letters) cut by the slab of vectors `β ≥ 0` with
degrees in `[D s - 1, D s]`. -/
lemma FrobeniusCycle.exists_finrank_defectConditions_le_volume (T : FrobeniusCycle N W K)
    [CharP K T.p] {a a' : Fin k} (ha : a.val + 1 = a') (n : ℕ) {t : ℕ} (ht : 2 * (k + 1) ≤ t) :
    ∃ D : ZMod N → ℝ,
      (∀ s : ZMod N, D s ∈ Set.Icc 1 (n + 4 * t * T.P ^ (2 * a'.val) : ℝ)) ∧
      finrank K (T.defectConditions n a a' ⊥ (3 * t)) ≤
        (parahoric W Fin.val).relIndex (levi W (twoBlock k a')) *
          volume.real (T.defectCone a 0 ∩ degreeSlab k D) := by
  obtain ⟨σ, hσ_cone, hσ_nonneg, hσ_int, hσ_le⟩ := T.exists_mem_defectCone_sum_le a
  let D (s : ZMod N) : ℝ := n + k + 1 + ∑ b : Fin k, ((4 * t : ℝ) • σ) (b, s)
  refine ⟨D, fun s ↦ ?_, ?_⟩
  · have h_shift : 4 * t * ∑ b : Fin k, σ (b, s) ≤ 4 * t * (T.P ^ (2 * a'.val) - 1) := by
      grw [hσ_le s, ha]
    have h_nonneg : 0 ≤ 4 * t * ∑ b : Fin k, σ (b, s) :=
      mul_nonneg (by positivity) (sum_nonneg fun b _ ↦ hσ_nonneg (b, s))
    have ht_real : (2 * (k + 1) : ℝ) ≤ t := mod_cast ht
    simp only [D, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    constructor <;> linarith
  -- The set `Y` is bounded and convex, so the number of its points in `m⁻¹ ℤ ^ (k N)`, divided
  -- by `m ^ (k N)`, tends to its volume. It suffices to bound the dimension along `m = q ^ j`.
  set Y : Set (Fin k × ZMod N → ℝ) := T.defectCone a 0 ∩ degreeSlab k D
  have h_meas : MeasurableSet Y := by
    simp only [Y, defectCone, degreeSlab, dotProduct]
    measurability
  have h_frontier : volume (frontier Y) = 0 :=
    (T.convex_defectCone_inter_degreeSlab a 0 D).addHaar_frontier _
  have h_limit := Filter.Tendsto.const_mul
    ((parahoric W Fin.val).relIndex (levi W (twoBlock k a')) : ℝ)
    (tendsto_card_div_pow_atTop_volume Y (isBounded_inter_degreeSlab ..) h_meas h_frontier)
  refine ge_of_tendsto_of_frequently h_limit
    (frequently_atTop'.2 fun j ↦ ⟨T.q ^ j, j.lt_pow_self (mod_cast T.one_lt_q), ?_⟩)
  rw [← mul_div_assoc, le_div_iff₀ (pow_pos (mod_cast pow_pos (one_pos.trans T.one_lt_q) j) _),
    ← cast_pow, ← cast_mul, ← cast_mul, cast_le]
  exact T.finrank_defectConditions_mul_pow_le ha n ht rfl hσ_cone hσ_nonneg hσ_int rfl

end New

end FlagsAndVolume

/-! ## The volume of a slab and the dimension of the forms of bounded defect -/

section BoundedDefect

open Finset Module MeasureTheory Measure Real Nat Subgroup Set Matrix

namespace New

variable {N k : ℕ}
  {W K : Type} [NeZero N] [CommRing W] [IsLocalRing W] [Field K]

/-- The slab of nonnegative vectors in `ℝ ^ (n + 1)` with sum in `[d - 1, d]`, where `d ≤ D`, has
volume at most `|Dⁿ / n!|`. -/
lemma volume_sum_mem_Icc_le {n : ℕ} {d D : ℝ} (hd : d ≤ D) :
    volume {y : Fin n.succ → ℝ | (∀ b : Fin n.succ, 0 ≤ y b) ∧ univ.sum y ∈ Set.Icc (d - 1) d} ≤
      ‖D ^ n / n !‖ₑ := by
  -- Slice along the first coordinate `x`. A nonempty slice has `0 ≤ x ≤ D` and lies in the slab
  -- for `d - x ≤ D - x`; integrating `(D - x) ^ n / n !` gives `D ^ (n + 1) / (n + 1)!`.
  induction n generalizing d D with
  | zero =>
    refine (measure_mono (t := Set.univ.pi fun _ : Fin 1 ↦ Set.Icc (d - 1) d) fun y hy ↦ by
      simpa [Set.pi] using hy.right).trans ?_
    simp [volume_pi_pi, -Set.pi_univ_Icc]
  | succ n ih =>
    set S : Set (Fin (n + 1).succ → ℝ) :=
      {y | (∀ b, 0 ≤ y b) ∧ univ.sum y ∈ Icc (d - 1) d}
    let slice (x : ℝ) : Set (Fin n.succ → ℝ) := {y : Fin n.succ → ℝ | Fin.cons x y ∈ S}
    have mem_slice (x : ℝ) (y : Fin n.succ → ℝ) :
        y ∈ slice x ↔ 0 ≤ x ∧ (∀ b, 0 ≤ y b) ∧ univ.sum y ∈ Icc (d - x - 1) (d - x) := by
      simp [slice, S, Fin.sum_cons, Fin.forall_fin_succ (n := n.succ)]
      grind
    have h_support : (fun x ↦ volume (slice x)).support ⊆ .uIcc D 0 := fun x hx ↦ by
      obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hx
      obtain ⟨hx_nonneg, hy_nonneg, -, h_sum_le⟩ := (mem_slice x y).1 hy
      exact Set.mem_uIcc.2 (.inr ⟨hx_nonneg, by linarith [univ.sum_nonneg fun b _ ↦ hy_nonneg b]⟩)
    calc
      volume S = ∫⁻ x, volume (slice x) := by
        rw [← (volume_preserving_piFinSuccAbove _ 0).symm.measure_preimage_equiv, volume_eq_prod,
          volume.prod_apply (by measurability)]
        simp [slice, Set.preimage, Fin.consEquiv]
      _ = ∫⁻ x in .uIoc D 0, volume (slice x) := by
        rw [setLIntegral_congr uIoc_ae_eq_interval, setLIntegral_eq_of_support_subset h_support]
      _ ≤ ∫⁻ x in .uIoc D 0, ‖(D - x) ^ n / n !‖ₑ := lintegral_mono fun x ↦
        (measure_mono fun y hy ↦ ((mem_slice x y).1 hy).right).trans (ih (sub_le_sub_right hd x))
      _ = ‖D ^ (n + 1) / (n + 1)!‖ₑ := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm (Continuous.integrableOn_uIoc (by fun_prop))]
        simp [← ofReal_norm, integral_div, abs_sub_comm D, integral_pow_abs_sub_uIoc, factorial,
          abs_of_nonneg (show (0 : ℝ) ≤ n + 1 by positivity), div_div]

/-- If `D s ≤ B` for all `N` letters `s`, then the slab of nonnegative vectors with `k + 1` entries
in each letter and degree in `[D s - 1, D s]` has volume at most `|B ^ k / k !| ^ N`. -/
lemma volume_degreeSlab_le {k : ℕ} {D : ZMod N → ℝ} {B : ℝ} (h_deg : ∀ s : ZMod N, D s ≤ B) :
    volume (degreeSlab (k + 1) D) ≤ ‖B ^ k / k !‖ₑ ^ N := by
  let block (s : ZMod N) : Set (Fin k.succ → ℝ) :=
    {y | (∀ b, 0 ≤ y b) ∧ univ.sum y ∈ Icc (D s - 1) (D s)}
  calc
    volume (degreeSlab (k + 1) D) ≤ volume (Set.univ.pi block) := by
      have h_subset : degreeSlab (k + 1) D ⊆ (fun β s b ↦ β (b, s)) ⁻¹' Set.univ.pi block :=
        fun β ⟨hβ_nonneg, hβ_deg⟩ s _ ↦ ⟨fun b ↦ hβ_nonneg (b, s), hβ_deg s⟩
      exact (measure_mono h_subset).trans
        ((measurePreserving_flip.comp measurePreserving_curry).measure_preimage_le _)
    _ = ∏ s : ZMod N, volume (block s) := volume_pi_pi block
    _ ≤ ∏ _s : ZMod N, ‖B ^ k / k !‖ₑ :=
        prod_le_prod fun s _ ↦ volume_sum_mem_Icc_le (h_deg s)
    _ = ‖B ^ k / k !‖ₑ ^ N := by simp

/-- There are at least `n ^ k / k !` monomials of degree `n` in `k + 1` variables. -/
lemma pow_div_factorial_le_card_monomials (k n : ℕ) :
    (n ^ k / k ! : ℝ) ≤ Fintype.card (Monomials (Fin (k + 1)) n) := by
  calc (n ^ k / k ! : ℝ) ≤ ((n + k + 1 - k : ℕ) : ℝ) ^ k / k ! := by gcongr; lia
    _ ≤ ((n + k).choose k : ℝ) := pow_le_choose k (n + k)
    _ = Fintype.card (Monomials (Fin (k + 1)) n) := by
        simp [card_finsuppAntidiag_nat_eq_choose, ← choose_symm_add, add_comm]

omit [NeZero N] in
/-- Let `q = T.P ^ N` be the number of elements of the residue field of the local ring `W`; the
Frobenius cycle `T` enters only through this number. The index in `GL_k(W)` of the parahoric
subgroup with blocks `r` and `k - r`, times the number of flags of its Levi subgroup `L`, is at most
`∏ (q ^ (l + 1) - 1) / (q - 1)` over `l < k`. -/
lemma FrobeniusCycle.index_mul_relIndex_le (T : FrobeniusCycle N W K) (r : ℕ) :
    ((parahoric W (twoBlock k r)).index *
        (parahoric W Fin.val).relIndex (levi W (twoBlock k r)) : ℝ) ≤
      ∏ l : Fin k, (((T.P : ℝ) ^ N) ^ (l.val + 1) - 1) / (T.P ^ N - 1) := by
  have : Finite (IsLocalRing.ResidueField W) := T.finite_residueField
  have h_iff {τ : Fin k → ℕ} {g : GL (Fin k) W} :
      g ∈ parahoric W τ ↔ ∀ ⦃i j : Fin k⦄, τ i < τ j → ¬IsUnit (g i j) := by
    simp [parahoric, parabolic, BlockTriangular]
  -- The entries of the Levi subgroup between the blocks vanish, and
  -- `twoBlock k r i < twoBlock k r j` implies `i < j`.
  have h_levi : levi W (twoBlock k r) ≤ parahoric W (twoBlock k r) :=
    fun g hg ↦ h_iff.2 fun i j h_lt ↦ by simp [show g i j = 0 from hg i j h_lt.ne]
  have h_iwahori_le : parahoric W Fin.val ≤ parahoric W (twoBlock k r) := fun g hg ↦
    h_iff.2 fun i j h_lt ↦ h_iff.1 hg (by grind [twoBlock] : i.val < j.val)
  calc ((parahoric W (twoBlock k r)).index *
          (parahoric W Fin.val).relIndex (levi W (twoBlock k r)) : ℝ)
      ≤ (parahoric W (twoBlock k r)).index *
          (parahoric W Fin.val).relIndex (parahoric W (twoBlock k r)) := by
        gcongr
        exact relIndex_le_of_le_right h_levi index_ne_zero_of_finite
    _ = (parahoric (k := k) W Fin.val).index := by
        rw [mul_comm, ← cast_mul, relIndex_mul_index h_iwahori_le]
    _ ≤ (parabolic (R := IsLocalRing.ResidueField W)
          (OrderDual.toDual ∘ (Fin.val : Fin k → ℕ))).index := by
        grw [parahoric, index_comap, relIndex_le_of_le_right le_top index_ne_zero_of_finite,
          relIndex_top_right]
    _ ≤ ∏ l : Fin k, (((T.P : ℝ) ^ N) ^ (l.val + 1) - 1) / (T.P ^ N - 1) := by
        grw [index_borel_le, T.card_residueField, cast_pow]

/-- The image of `ν` under `New.permStep` with trivial permutations, that is, the vector
`± (P ν (b, s + 1) - ν (b, s))` with the sign `+` at even letters, has defect at most `0` along all
simple roots if and only if `ν` lies in `New.pieriCone`, the cone of Pieri's inequalities in the
coordinates `ν`. The index `a'` does not matter, as the bound is `0` at every root. -/
lemma FrobeniusCycle.permStep_mem_defectCone_iff (T : FrobeniusCycle N W K) {a' : Fin k}
    (ν : Fin k × ZMod N → ℝ) :
    permStep T.isEven T.P 1 ν ∈ T.defectCone a' 0 ↔ ν ∈ pieriCone T.isEven (T.P : ℝ) := by
  change (∀ (i : ZMod N) (b b' : Fin k), b.val + 1 = b' →
      T.defectWeight i b b' ⬝ᵥ permStep T.isEven T.P 1 ν ≤ if b = a' then (0 : ℝ) else 0) ↔
    ∀ (i : ZMod N) (b b' : Fin k), b.val + 1 = b' →
      permStep T.isEven T.P 1 ν ((if T.isEven i then b' else b), i) ≤ ν (b, i) - ν (b', i)
  refine forall₄_congr fun i b b' hb ↦ ?_
  rw [defectWeight_dotProduct_permStep, ite_self, sub_nonpos, rootVar]

/-- For a Frobenius cycle `T` with `q = T.P ^ N`, the cone `T.defectCone a 0` of Pieri's
inequalities fills the part `∏ (q - 1) / (q ^ (l + 1) - 1)`, over `l < k`, of the volume of every
slab of vectors `β ≥ 0` with degrees in `[D s - 1, D s]`. -/
lemma FrobeniusCycle.prod_mul_volume_defectCone_inter_degreeSlab (T : FrobeniusCycle N W K)
    {a : Fin k} (D : ZMod N → ℝ) :
    (∏ l : Fin k, (((T.P : ℝ) ^ N) ^ (l.val + 1) - 1) / (T.P ^ N - 1)) *
      volume.real (T.defectCone a 0 ∩ degreeSlab k D) = volume.real (degreeSlab k D) :=
  prod_mul_volume_real_inter_degreeSlab T.one_lt_P D T.permStep_mem_defectCone_iff

/-- Few forms have bounded defect. Let `T` be a Frobenius cycle from the local ring `W` to the field
`K` of characteristic `T.p`: ring maps `ι s : W → K`, one for each letter `s ∈ ℤ/N`, with
`ι (s + 1) ≡ ι s ^ P` modulo the prime `T.p`. Here `P = T.P` is a power of `T.p`, the residue field
of `W` has `q = T.q = P ^ N` elements, and the letters are alternately even and odd (`T.isEven`). A
matrix `g ∈ GL_k(W)` acts on polynomials in the variables `x (b, s)`, `b < k`, by the linear
substitution `T.polyAction g`, given in the letter `s` by `ι s g` for even `s` and by `ι s` of the
inverse transpose of `g` for odd `s`. The defect of a vector `β` indexed by
`(b, s) ∈ Fin k × ZMod N`, at the letter `i` along the root `(b, b')`, is the linear form with
coefficients `T.defectWeight i b b'`, namely
`β v + ∑ s, ± P ^ ((s - i) mod N) * (β (b', s) - β (b, s)) / (q - 1)`, with the sign `+` at even
`s`, and `v = (b', i)` for even `i`, `v = (b, i)` for odd `i`. Let `a' = a + 1` and `t ≥ 2 (k + 1)`,
and let `L = levi W (twoBlock k a')` be the group of block diagonal matrices with blocks `a'` and
`k - a'`. Let `S = T.defectConditions n a a' ⊥ (3 t)` be the space of forms of degree `n` in each
letter whose translates by `L` have coefficient in the ideal `⊥`, that is `0`, at every exponent of
defect above `3 t` along `(a, a')` at some letter. Let `θ ≤ 1`, and let `n > 0` satisfy
`8 N k t P ^ (2 a') ≤ θ n`. Then the index in `GL_k(W)` of the parahoric subgroup of these blocks
(upper right block in the maximal ideal) times `dim S` is at most `1 + θ` times the number of
`N`-tuples of monomials of degree `n` in `k` variables. -/
lemma FrobeniusCycle.index_mul_finrank_defectConditions_le (T : FrobeniusCycle N W K) {a a' : Fin k}
    [CharP K T.p] (ha : a.val + 1 = a') {n t : ℕ} {θ : ℝ} (hn : 0 < n) (ht : 2 * (k + 1) ≤ t)
    (hθ : θ ≤ 1) (h_large : 8 * N * k * t * T.P ^ (2 * a'.val) ≤ θ * n) :
    (parahoric W (twoBlock k a')).index * finrank K (T.defectConditions n a a' ⊥ (3 * t)) ≤
      (1 + θ) * Fintype.card (Monomials (Fin k) n) ^ N := by
  -- The index times the number of flags of the Levi subgroup is at most the number of all flags,
  -- which cancels the share of the cone in the slab. The degrees of the slab are at most `n + E`.
  obtain ⟨D, hD, h_flags⟩ := T.exists_finrank_defectConditions_le_volume ha n ht
  set E : ℝ := 4 * t * T.P ^ (2 * a'.val) with hE_def
  have hE_le : 2 * N * k * E ≤ θ * n := by linarith
  have hE : 0 ≤ E := by positivity
  have hn_real : (0 : ℝ) < n := cast_pos.2 hn
  have h_deg (s : ZMod N) : D s ≤ rexp (E / n) * n :=
    calc D s ≤ (E / n + 1) * n := (hD s).2.trans_eq (by field)
      _ ≤ rexp (E / n) * n := mul_le_mul_of_nonneg_right (add_one_le_exp _) hn_real.le
  clear_value E -- the estimates below treat `E` as an atom
  obtain _ | k' := k
  · exact a.elim0
  let x : ℝ := N * (k' * (E / n))
  have h_exp : rexp x ≤ 1 + θ := by
    have hx_le : 2 * x ≤ θ :=
      calc 2 * x = 2 * N * k' * E / n := by ring
        _ ≤ 2 * N * (k' + 1 : ℕ) * E / n := by gcongr; exact k'.le_succ
        _ ≤ θ := (div_le_iff₀ hn_real).2 hE_le
    have h_bound : rexp x ≤ 1 + x * 2 := by
      simpa [one_add_one_eq_two] using
        exp_bound' (show 0 ≤ x by positivity) (show x ≤ 1 by linarith) one_pos
    linarith
  calc ((parahoric W (twoBlock (k' + 1) a')).index *
          finrank K (T.defectConditions n a a' ⊥ (3 * t)) : ℝ)
      ≤ (parahoric W (twoBlock (k' + 1) a')).index *
          (parahoric W Fin.val).relIndex (levi W (twoBlock (k' + 1) a')) *
          volume.real (T.defectCone a 0 ∩ degreeSlab (k' + 1) D) := by grw [h_flags, mul_assoc]
    _ ≤ volume.real (degreeSlab (k' + 1) D) := by
        grw [T.index_mul_relIndex_le, T.prod_mul_volume_defectCone_inter_degreeSlab]
    _ ≤ rexp x * (n ^ k' / k' !) ^ N := by
        refine (ENNReal.toReal_le_of_le_ofReal (b := ((rexp (E / n) * n) ^ k' / k' !) ^ N)
          (by positivity) ?_).trans_eq ?_
        · rw [ENNReal.ofReal_pow (by positivity), ← enorm_of_nonneg (by positivity)]
          exact volume_degreeSlab_le h_deg
        · rw [mul_pow, mul_div_assoc, mul_pow, ← exp_nat_mul, ← exp_nat_mul]
    _ ≤ (1 + θ) * Fintype.card (Monomials (Fin (k' + 1)) n) ^ N := by
        gcongr
        · exact (exp_pos _).le.trans h_exp
        · exact pow_div_factorial_le_card_monomials k' n

end New

end BoundedDefect
