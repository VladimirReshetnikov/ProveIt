import Lib.General.Algebra.MultivariatePolynomials
import New.UpperBound.ElementaryDivisors.TwistingData

/-!
# Few forms have only deep translates

Let `T` be a Frobenius cycle over a field `K` of characteristic `p`. The space
`New.FrobeniusCycle.deepForms` consists of the forms all of whose translates have only monomials of
depth at least `δ`. Such a form vanishes to order `δ` at many points, which are cut out by equations
with small leading powers, so it has a monomial of large weighted degree. The sum of the weighted
degrees of all monomials therefore bounds the sum of the dimensions of these spaces. With
`New.FrobeniusCycle.exists_originFunctions_factorization_det_dvd`, the bound leads to the theorem on
elementary divisors, `New.FrobeniusCycle.elementary_divisors`.

Notions from other files:
* `New.FrobeniusCycle N W K`: a prime `p` with a power `P`, ring maps `embedding s : W → K` for the
  letters `s` in `ZMod N`, which are alternately even and odd, and a residue field of `W` with
  `q = P ^ N` elements.
* `New.FrobeniusCycle.deepIndicator`: the indicator of the variables `(b, s)` that are deep for `r`,
  that is, `s` is even and `r ≤ b`, or `s` is odd and `b < r`.
* `New.Exponents N k n`, `New.polyOfCoeffs`: the exponents of the monomials in the variables
  `(b, s)` of degree `n` in each letter, and the polynomial with given coefficients at them.
* `New.FrobeniusCycle.polyAction`: the action of `GL_k(W)` on polynomials in the variables `(b, s)`.

## Main definitions and results

* `New.FrobeniusCycle.entryRow`, `New.FrobeniusCycle.entryCol`: for `k = 2 r + m`, the row `< r` and
  the column `≥ r` of the position in a `k × k` matrix named by `t` in `Fin r × Fin (m + 1)`.
* `New.FrobeniusCycle.entryFormValue`: the point attached to residues `y t` at the positions. Its
  coordinates are linear forms in lifts of the `y t`, with coefficients
  `New.FrobeniusCycle.entryCoeff`, each zero or a variable up to sign.
* `New.FrobeniusCycle.exists_le_weight_of_mem_deepForms`: a non-zero form in
  `New.FrobeniusCycle.deepForms` has a monomial of large weight.
* `New.FrobeniusCycle.sum_finrank_deepForms_le`: the dimensions of the spaces of forms all of whose
  translates have depth at least `1, 2, …, M` add up to at most `New.FrobeniusCycle.divisorConstant`
  times the number of exponents.

## Relation to the literature

See `New.UpperBound.ElementaryDivisors.DefectCount` for related work.
-/

noncomputable section

/-! ## Deep forms have a monomial of large weight -/

namespace New.FrobeniusCycle

open MvPolynomial Matrix Finset Finsupp IsLocalRing Fintype Ideal

section DeepForms

variable {N k : ℕ} {W K : Type} [CommRing W] [IsLocalRing W] [Field K] (T : FrobeniusCycle N W K)

theorem deepIndicator_eq_zero_or_eq_one (r : ℕ) (v : Fin k × ZMod N) :
    T.deepIndicator r v = 0 ∨ T.deepIndicator r v = 1 :=
  (ite_eq_or_eq _ 1 0).symm

/-- For every `r` and every index `b`, the variable `(b, s)` is deep for half of the letters `s` in
`ZMod N`: even and odd letters (`T.isEven`) alternate, and `T.deepIndicator r (b, s)` is `1` if `s`
is even and `r ≤ b`, or `s` is odd and `b < r`, and `0` otherwise. -/
theorem sum_deepIndicator [NeZero N]
    (r : ℕ) (b : Fin k) : ∑ s : ZMod N, T.deepIndicator r (b, s) = N / 2 := by
  -- Shifting `s` by one swaps deep and shallow, so twice the sum is `N`.
  have h_pair (s : ZMod N) : T.deepIndicator r (b, s + 1) + T.deepIndicator r (b, s) = 1 := by
    cases h_even : T.isEven s <;> by_cases hb : r ≤ b <;>
      simp [deepIndicator, T.isEven_succ, h_even, hb]
  have h_shift : ∑ s : ZMod N, T.deepIndicator r (b, s + 1) = ∑ s, T.deepIndicator r (b, s) :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) fun s ↦ T.deepIndicator r (b, s)
  have h_twice : ∑ s : ZMod N, (T.deepIndicator r (b, s + 1) + T.deepIndicator r (b, s)) = N := by
    simp [h_pair]
  simp only [sum_add_distrib, h_shift] at h_twice
  lia

/-- Even and odd letters alternate, so for every `b` the letter `i - j` is even for one of
`j = 2 b` and `j = 2 b + 1`. -/
theorem exists_div_two_eq_and_isEven_sub (i : ZMod N) (b : ℕ) :
    ∃ j : ℕ, j / 2 = b ∧ T.isEven (i - j) := by
  have h_succ : T.isEven (i - (2 * b : ℕ)) = !T.isEven (i - (2 * b + 1 : ℕ)) := by
    rw [← T.isEven_succ, Nat.cast_succ, sub_add_eq_sub_sub, sub_add_cancel]
  cases h_even : T.isEven (i - (2 * b : ℕ))
  · exact ⟨2 * b + 1, by lia, by rwa [h_even, eq_comm, Bool.not_eq_false'] at h_succ⟩
  · exact ⟨2 * b, by lia, h_even⟩

/-- Elements of the local ring `W` with the same image under the ring map `T.embedding s` to the
field `K` have the same residue. -/
theorem residue_eq_of_embedding_eq {s : ZMod N} {u v : W}
    (huv : T.embedding s u = T.embedding s v) :
    residue W u = residue W v := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  exact fun h_unit ↦ (h_unit.map (T.embedding s)).ne_zero (by rw [map_sub, huv, sub_self])

variable [NeZero N]

/-- The degree given to the variable `v = (b, s)` in the count of common zeros behind
`New.FrobeniusCycle.exists_le_weight_of_mem_deepForms`, a power of `P = T.P`: it is `P ^ (2 r)` if
`v` is deep for `r` (`T.deepIndicator r v = 1`) and `2 r ≤ b`, `P` if `v` is deep and `b < 2 r`, and
`1` if `v` is not deep. -/
def deepOrder (r : ℕ) (v : Fin k × ZMod N) : ℕ :=
  T.P ^ (T.deepIndicator r v * if 2 * r ≤ v.1 then 2 * r else 1)

/-- For `k = 2 r + m`, the product of the degrees `T.deepOrder r v` over all variables is at most
`q ^ (r (m + 1))`, the number of families of `r (m + 1)` residues of `W`, whose residue field has
`q = T.q = P ^ N` elements. -/
theorem prod_deepOrder_le {r m : ℕ} (hm : 2 * r + m = k) :
    ∏ v : Fin k × ZMod N, T.deepOrder r v ≤ T.q ^ (r * (m + 1)) := by
  subst hm
  -- Each index `b` has `N / 2` deep variables; `2 r` indices are below `2 r`, and `m` are not.
  have h_sum : ∑ v : Fin (2 * r + m) × ZMod N,
      (T.deepIndicator r v * if 2 * r ≤ v.1 then 2 * r else 1) =
        2 * r * (N / 2) + m * (N / 2 * (2 * r)) := by
    rw [sum_prod_type, Fin.sum_univ_add]
    simp [← Finset.sum_mul, sum_deepIndicator, Nat.not_le_of_lt (Fin.is_lt _)]
  calc ∏ v : Fin (2 * r + m) × ZMod N, T.deepOrder r v
      = T.P ^ (N / 2 * 2 * (r * (m + 1))) := by
        simp only [deepOrder, prod_pow_eq_pow_sum, h_sum]
        ring
    _ ≤ T.P ^ (N * (r * (m + 1))) := by
        gcongr
        exacts [mod_cast T.one_lt_P.le, N.div_mul_le_self 2]
    _ = T.q ^ (r * (m + 1)) := by rw [q, pow_mul T.P]

/-- If `F` lies in `T.deepForms k n r τ`, the coefficient of its translate by `g` (the matrix of `g`
on coefficient vectors is `T.letterRep n g`) vanishes at every monomial `β` whose degree in the
variables that are deep for `r` is below `τ`. -/
theorem letterRep_mulVec_eq_zero_of_mem_deepForms {n r τ : ℕ} {F : Exponents N k n → K}
    (hF : F ∈ T.deepForms k n r τ) (g : GL (Fin k) W) {β : Exponents N k n}
    (hβ : T.depth k n r β < τ) : (T.letterRep n g *ᵥ F) β = 0 := by
  -- With a single block, the Levi subgroup is all of `GL_k(W)`.
  exact Ideal.mem_bot.1 (hF g (fun i j hij ↦ absurd rfl hij) β hβ)

/-- Let `F` lie in `T.deepForms k n r τ`. If a ring map `ψ` sends the translates by `g⁻¹` of the
deep variables into an ideal `𝔪`, then it sends the form with coefficients `F` into `𝔪 ^ τ`. -/
theorem map_polyOfCoeffs_mem_pow_of_mem_deepForms {n r τ : ℕ} {F : Exponents N k n → K}
    (hF : F ∈ T.deepForms k n r τ) {L : Type} [CommRing L]
    (ψ : MvPolynomial (Fin k × ZMod N) K →+* L) (𝔪 : Ideal L) (g : GL (Fin k) W)
    (h_var : ∀ v : Fin k × ZMod N, ψ (T.polyAction g⁻¹ (X v)) ∈ 𝔪 ^ T.deepIndicator r v) :
    ψ (polyOfCoeffs F) ∈ 𝔪 ^ τ := by
  -- `F` is the translate by `g⁻¹` of its translate `G` by `g`, whose monomials are deep.
  let G : Exponents N k n → K := T.letterRep n g *ᵥ F
  have hF_eq : F = T.letterRep n g⁻¹ *ᵥ G := by simp [G, ← map_mul]
  have h_expand : ψ (polyOfCoeffs F) = ∑ β : Exponents N k n,
      ψ (C (G β)) * ∏ v : Fin k × ZMod N, ψ (T.polyAction g⁻¹ (X v)) ^ exponentOf β v := by
    rw [hF_eq, ← polyAction_polyOfCoeffs]
    simp [polyOfCoeffs, monomial_eq]
  rw [h_expand]
  refine sum_mem fun β _ ↦ ?_
  obtain h_deep | h_shallow := le_or_gt τ (T.depth k n r β)
  · have h_pow : 𝔪 ^ T.depth k n r β =
        ∏ v : Fin k × ZMod N, (𝔪 ^ T.deepIndicator r v) ^ exponentOf β v := by
      simp [depth, weight_eq_sum, ← prod_pow_eq_pow_sum, pow_mul']
    refine pow_le_pow_right h_deep (mul_mem_left _ _ ?_)
    rw [h_pow]
    exact prod_mem_prod fun v _ ↦ pow_mem_pow (h_var v) _
  · simp [show G β = 0 from T.letterRep_mulVec_eq_zero_of_mem_deepForms hF g h_shallow]

/-- For a ring map `x` from the polynomials to `L`, the ring map to polynomials over `L` that keeps
the variables that are deep for `r` and sends the constants and the other variables to their images
under `x`. -/
def specializeShallow {L : Type} [CommRing L] (r : ℕ) (x : MvPolynomial (Fin k × ZMod N) K →+* L) :
    MvPolynomial (Fin k × ZMod N) K →+* MvPolynomial (Fin k × ZMod N) L :=
  eval₂Hom (C.comp (x.comp C)) fun v : Fin k × ZMod N ↦
    if T.deepIndicator r v = 0 then C (x (X v)) else X v

omit [NeZero N] in
/-- If `x` is injective, so is `T.specializeShallow r x`. This is the ring map that keeps the
variables deep for `r` and reads the constants and the other variables in `L` through `x`. A
variable `X (b, s)` is deep for `r` if `T.isEven s` and `r ≤ b`, or if `s` is odd and `b < r`. -/
theorem specializeShallow_injective {L : Type} [CommRing L] (r : ℕ)
    {x : MvPolynomial (Fin k × ZMod N) K →+* L} (hx : Function.Injective x) :
    Function.Injective (T.specializeShallow r x) := by
  have h_factor : x = (eval (x ∘ X)).comp (T.specializeShallow r x) := by
    ext <;> simp [specializeShallow, apply_ite]
  rw [h_factor, RingHom.coe_comp] at hx
  exact hx.of_comp

/-- If `x` is injective, the ring map `T.specializeShallow r x` does not send the polynomial with
coefficients `F ≠ 0` to zero. -/
theorem specializeShallow_polyOfCoeffs_ne_zero {L : Type} [CommRing L] {n : ℕ} (r : ℕ)
    {x : MvPolynomial (Fin k × ZMod N) K →+* L} (hx : Function.Injective x)
    {F : Exponents N k n → K} (hF_ne : F ≠ 0) : T.specializeShallow r x (polyOfCoeffs F) ≠ 0 := by
  obtain ⟨β, hβ⟩ : ∃ β : Exponents N k n, F β ≠ 0 := Function.ne_iff.1 hF_ne
  have h_coeff : (polyOfCoeffs F).coeff (exponentOf β) = F β := by simp [polyOfCoeffs]
  rw [map_ne_zero_iff _ (T.specializeShallow_injective r hx), MvPolynomial.ne_zero_iff]
  exact ⟨exponentOf β, h_coeff.trans_ne hβ⟩

/-- The ring map `T.specializeShallow r x` keeps the deep variables and reads the others in `L`
through `x`. Each monomial `α` of its value at the polynomial with coefficients `F` is the deep part
(the exponents at the variables with `T.deepIndicator r v ≠ 0`) of the exponent vector
`exponentOf β` of a monomial `β` with `F β ≠ 0`. -/
theorem exists_eq_of_mem_support_specializeShallow {L : Type} [CommRing L] {n r : ℕ}
    {x : MvPolynomial (Fin k × ZMod N) K →+* L} {F : Exponents N k n → K}
    {α : Fin k × ZMod N →₀ ℕ} (hα : α ∈ (T.specializeShallow r x (polyOfCoeffs F)).support) :
    ∃ β : Exponents N k n, F β ≠ 0 ∧
      ∀ v : Fin k × ZMod N, α v = if T.deepIndicator r v = 0 then 0 else exponentOf β v := by
  let deep : Finset (Fin k × ZMod N) := {v | ¬T.deepIndicator r v = 0}
  let deepPart (β : Exponents N k n) : Fin k × ZMod N →₀ ℕ :=
    Finsupp.indicator deep fun v _ ↦ exponentOf β v
  let c (β : Exponents N k n) : L :=
    x (C (F β)) * x (∏ v with T.deepIndicator r v = 0, X v ^ exponentOf β v)
  have h_expand : T.specializeShallow r x (polyOfCoeffs F) =
      ∑ β : Exponents N k n, C (c β) * ∏ v ∈ deep, X v ^ exponentOf β v := by
    simp [polyOfCoeffs, specializeShallow, prod_fintype, prod_ite, c, deep, mul_assoc]
  have h_coeff : ∑ β : Exponents N k n, (if α = deepPart β then c β else 0) ≠ 0 := by
    simpa [h_expand, coeff_sum, coeff_prod_X_pow] using hα
  obtain ⟨β, h_eq, hc⟩ : ∃ β : Exponents N k n, α = deepPart β ∧ c β ≠ 0 := by
    simpa using exists_ne_zero_of_sum_ne_zero h_coeff
  exact ⟨β, fun h_zero ↦ by simp [c, h_zero] at hc,
    fun v ↦ by simp [h_eq, deepPart, deep, Finsupp.indicator_apply]⟩

/-- Let the variable `v u b` determine `b`, and let the exponents `e u` be positive and distinct.
The determinant of the matrix of the powers `X (v u b) ^ e u` is a signed sum of distinct
monomials, so it is not zero. -/
lemma _root_.New.det_X_pow_ne_zero {ι σ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    [Nontrivial R] {v : ι → ι → σ} (hv_index : ∀ u u' b b' : ι, v u b = v u' b' → b = b')
    {e : ι → ℕ} (he_inj : Function.Injective e) (he_pos : ∀ u : ι, e u ≠ 0) :
    (of fun u b : ι ↦ (X (v u b) : MvPolynomial σ R) ^ e u).det ≠ 0 := by
  classical
  -- `d π` is the exponent of the monomial of the permutation `π`.
  let d (π : Equiv.Perm ι) : σ →₀ ℕ := ∑ b : ι, Finsupp.single (v (π b) b) (e (π b))
  have d_apply (π : Equiv.Perm ι) (b : ι) :
      d π (v b b) = if v (π b) b = v b b then e (π b) else 0 := by
    simp only [d, Finsupp.finsetSum_apply, Finsupp.single_apply]
    exact Finset.sum_eq_single b (fun b' _ hb' ↦ ite_eq_right (mt (hv_index (π b') b b' b) hb'))
      (by simp)
  have h_distinct (π : Equiv.Perm ι) (hπ : d π = d 1) : π = 1 := by
    ext b
    have h_exponent : (if v (π b) b = v b b then e (π b) else 0) = e b := by
      simpa [d_apply] using DFunLike.congr_fun hπ (v b b)
    grind [he_inj.eq_iff]
  have h_coeff : (of fun u b : ι ↦ (X (v u b) : MvPolynomial σ R) ^ e u).det.coeff (d 1) = 1 := by
    have h_expand : (of fun u b : ι ↦ (X (v u b) : MvPolynomial σ R) ^ e u).det =
        ∑ π : Equiv.Perm ι, π.sign • monomial (d π) 1 := by
      simp [det_apply, d, X_pow_eq_monomial, monomial_sum_one]
    rw [h_expand, coeff_sum, Finset.sum_eq_single 1 (fun π _ hπ ↦ by
      simp [coeff_monomial, mt (h_distinct π) hπ]) (by simp)]
    simp
  exact fun h_zero ↦ by simp [h_zero] at h_coeff

end DeepForms

section Points

variable {N k : ℕ} {W K : Type} [CommRing W] [IsLocalRing W] [Field K] (T : FrobeniusCycle N W K)

/-!
The pairs in `Fin r × Fin (m + 1)` name the positions where a `k × k` matrix `A` over `W` may have
non-zero entries.
-/

/-- For `k = 2 r + m`, the pair `t = (a, l)` with `a < r` and `l ≤ m` names a position of a `k × k`
matrix in the row `a`. -/
def entryRow {r m : ℕ} (hm : 2 * r + m = k) (t : Fin r × Fin (m + 1)) : Fin k := ⟨t.1, by lia⟩

/-- For `k = 2 r + m`, the pair `t = (a, l)` names a position of a `k × k` matrix in the column
`a + r` if `l = 0`, and in the column `k - l ≥ 2 r` otherwise. -/
def entryCol {r m : ℕ} (hm : 2 * r + m = k) (t : Fin r × Fin (m + 1)) : Fin k :=
  ⟨if t.2 = 0 then t.1 + r else k - t.2, by lia⟩

/-- Let the position `t = (a, l)` lie in the row `a` and the column `c`, which is `a + r` if
`l = 0` and `k - l` otherwise
(`entryRow`, `entryCol`), and let `s` be the letter (second component) of `v`. This polynomial is
`X (a, s)` if `s` is even and `v = (c, s)`, it is `-X (c, s)` if `s` is odd and `v = (a, s)`, and it
is `0` otherwise; `T.rootVar` picks the index by the parity of `s`. For a matrix `A` over `W`
supported on the positions, the translate of `X v` by `(1 + A)⁻¹` is `X v` minus a linear form in
the entries of `ι_s(A)`, where `ι_s = T.embedding s`, and this is its coefficient at `t`. -/
noncomputable def entryCoeff {r m : ℕ} (hm : 2 * r + m = k) (v : Fin k × ZMod N)
    (t : Fin r × Fin (m + 1)) : MvPolynomial (Fin k × ZMod N) K :=
  (if T.rootVar (entryRow hm t) (entryCol hm t) v.2 = v then
    X (T.rootVar (entryCol hm t) (entryRow hm t) v.2) else 0) * if T.isEven v.2 then 1 else -1

/-- The span over `L` of the vectors `t ↦ x (T.entryCoeff hm v t) ^ P ^ j`, for the variables
`v = (b, s)` and the `j` with `s + j = i` and `P ^ j < T.deepOrder r v`. Let `A` be a matrix over
`W` supported on the positions `t`, and `ι_s = T.embedding s`. In characteristic `p`, the `P ^ j`-th
power of the linear form with coefficients `T.entryCoeff hm v` in the entries of `ι_s(A)` is a
linear form in the entries of `ι_i(A)`, and such a vector holds its coefficients, read in `L`
through `x`. -/
noncomputable def lowPowerForms {r m : ℕ} (hm : 2 * r + m = k) {L : Type} [Field L]
    (x : MvPolynomial (Fin k × ZMod N) K →+* L) (i : ZMod N) :
    Submodule L (Fin r × Fin (m + 1) → L) :=
  .span L {u : Fin r × Fin (m + 1) → L | ∃ (v : Fin k × ZMod N) (j : ℕ),
    v.2 + j = i ∧ T.P ^ j < T.deepOrder r v ∧ (x ∘ T.entryCoeff hm v) ^ T.P ^ j = u}

/-- If `x` embeds the polynomials over `K` in a field `L` and `l ≠ 0`, the space
`T.lowPowerForms hm x i` contains the unit vector at `(b, l)`. -/
lemma single_mem_lowPowerForms_of_ne_zero {r m : ℕ} (hm : 2 * r + m = k) {L : Type} [Field L]
    {x : MvPolynomial (Fin k × ZMod N) K →+* L} (hx : Function.Injective x) (i : ZMod N)
    (b : Fin r) {l : Fin (m + 1)} (hl : l ≠ 0) : Pi.single (b, l) 1 ∈ T.lowPowerForms hm x i := by
  -- The positions `(b', l)` give an `r × r` system, with one equation for each of the `r` integers
  -- `j = J u < 2 r` such that the letter `i - j` is even.
  choose J hJ_div hJ_even using T.exists_div_two_eq_and_isEven_sub i
  have hP : 1 < T.P := mod_cast T.one_lt_P
  -- The matrix of the system is invertible over `L`, so `Pi.single b 1` is in its row span.
  let M : Matrix (Fin r) (Fin r) (MvPolynomial (Fin k × ZMod N) K) :=
    of fun u b' ↦ X (entryRow hm (b', l), i - J u) ^ T.P ^ J u
  have h_det : M.det ≠ 0 := by
    have h_inj : Function.Injective fun u : Fin r ↦ T.P ^ J u := fun u u' h_eq ↦
      Fin.ext (by rw [← hJ_div u, Nat.pow_right_injective hP h_eq, hJ_div u'])
    refine det_X_pow_ne_zero (fun u u' b₁ b₂ h_var ↦ ?_) h_inj fun u ↦ by positivity
    simpa [entryRow, Fin.ext_iff] using congrArg Prod.fst h_var
  have h_unit : IsUnit (x.mapMatrix M) := by
    rw [isUnit_iff_isUnit_det, ← x.map_det]
    exact ((map_ne_zero_iff x hx).2 h_det).isUnit
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin r → L, μ ᵥ* x.mapMatrix M = Pi.single b 1 :=
    vecMul_surjective_iff_isUnit.2 h_unit _
  let row (u : Fin r) : Fin r × Fin (m + 1) → L :=
    (x ∘ T.entryCoeff hm (entryCol hm (b, l), i - J u)) ^ T.P ^ J u
  have row_mem (u : Fin r) : row u ∈ T.lowPowerForms hm x i := by
    have h_col : 2 * r ≤ entryCol hm (b, l) := by grind [entryCol]
    have h_order : T.deepOrder r (entryCol hm (b, l), i - J u) = T.P ^ (2 * r) := by
      simp [deepOrder, deepIndicator, hJ_even, h_col, show r ≤ entryCol hm (b, l) by lia]
    refine Submodule.subset_span ⟨(entryCol hm (b, l), i - J u), J u, by simp, ?_, rfl⟩
    rw [h_order]
    exact Nat.pow_lt_pow_right hP (by grind [hJ_div u])
  have row_apply (u : Fin r) (t : Fin r × Fin (m + 1)) :
      row u t = if t.2 = l then x (M u t.1) else 0 := by
    have h_same_col : entryCol hm t = entryCol hm (b, l) ↔ t.2 = l := by grind [entryCol]
    split_ifs with ht <;>
      simp [row, entryCoeff, M, rootVar, hJ_even, h_same_col, ht, entryRow, T.prime.ne_zero]
  have h_comb : Pi.single (b, l) 1 = ∑ u : Fin r, μ u • row u := by
    ext ⟨b', l'⟩
    by_cases hl' : l' = l
    · simpa [row_apply, hl', vecMul, dotProduct, Pi.single_apply] using (congrFun hμ b').symm
    · simp [row_apply, hl']
  rw [h_comb]
  exact Submodule.sum_mem _ fun u _ ↦ Submodule.smul_mem _ _ (row_mem u)

/-- If `x` embeds the polynomials over `K` in a field `L`, the space `T.lowPowerForms hm x i`
contains the unit vector at `(b, 0)`. -/
lemma single_zero_mem_lowPowerForms {r m : ℕ} (hm : 2 * r + m = k) {L : Type} [Field L]
    {x : MvPolynomial (Fin k × ZMod N) K →+* L} (hx : Function.Injective x) (i : ZMod N)
    (b : Fin r) : Pi.single (b, 0) 1 ∈ T.lowPowerForms hm x i := by
  -- Take `j = 0` and one deep variable `v` of the letter `i`: its vector is non-zero at `(b, 0)`,
  -- and its other non-zero entries lie at positions `(b', l)` with `l ≠ 0`.
  let v : Fin k × ZMod N := T.rootVar (entryRow hm (b, 0)) (entryCol hm (b, 0)) i
  let row : Fin r × Fin (m + 1) → L := x ∘ T.entryCoeff hm v
  have row_mem : row ∈ T.lowPowerForms hm x i := by
    have h_deep : T.deepIndicator r v = 1 := by grind [deepIndicator, rootVar, entryRow, entryCol]
    refine Submodule.subset_span ⟨v, 0, by simp [v], ?_, by simp [row]⟩
    rw [deepOrder, h_deep, one_mul]
    exact Nat.pow_lt_pow_right (mod_cast T.one_lt_P) (by grind [b.pos])
  have h_pivot : row (b, 0) ≠ 0 := by
    cases h_even : T.isEven i <;> simp [row, entryCoeff, v, h_even, map_eq_zero_iff x hx]
  have h_other (b' : Fin r) (hb' : b' ≠ b) : row (b', 0) = 0 := by
    suffices h_var : T.rootVar (entryRow hm (b', 0)) (entryCol hm (b', 0)) v.2 ≠ v by
      simp [row, entryCoeff, h_var]
    grind [rootVar, entryRow, entryCol]
  have h_solve : row (b, 0) • (Pi.single (b, 0) 1 : Fin r × Fin (m + 1) → L) =
      row - ∑ t : Fin r × Fin (m + 1) with t.2 ≠ 0, row t • Pi.single t 1 := by
    ext ⟨b', l⟩
    obtain rfl | hl := eq_or_ne l 0
    · by_cases hb : b' = b <;> simp [hb, h_other, Pi.single_apply]
    · simp [hl, Pi.single_apply]
  rw [← Submodule.smul_mem_iff _ h_pivot, h_solve]
  refine sub_mem row_mem (Submodule.sum_mem _ fun ⟨b', l⟩ h_mem ↦ Submodule.smul_mem _ _ ?_)
  exact T.single_mem_lowPowerForms_of_ne_zero hm hx i b' (by simpa using h_mem)

/-- If `x` embeds the polynomials over `K` in a field `L`, the space `T.lowPowerForms hm x i`
contains every vector. -/
lemma mem_lowPowerForms {r m : ℕ} (hm : 2 * r + m = k) {L : Type} [Field L]
    {x : MvPolynomial (Fin k × ZMod N) K →+* L} (hx : Function.Injective x) (i : ZMod N)
    (u : Fin r × Fin (m + 1) → L) : u ∈ T.lowPowerForms hm x i := by
  rw [pi_eq_sum_univ' u]
  refine Submodule.sum_mem _ fun ⟨b, l⟩ _ ↦ Submodule.smul_mem _ _ ?_
  obtain rfl | hl := eq_or_ne l 0
  exacts [T.single_zero_mem_lowPowerForms hm hx i b,
    T.single_mem_lowPowerForms_of_ne_zero hm hx i b hl]

/-- The point attached to the matrix `A` whose entries `(y t).out` at the positions `t` lift the
residues `y t`: its coordinate `v = (b, s)` is the linear form with coefficients `T.entryCoeff hm v`
in the entries of `ι_s(A)`, where `ι_s = T.embedding s`, read in `L` through `x`. -/
noncomputable def entryFormValue {r m : ℕ} (hm : 2 * r + m = k) {L : Type} [Field L]
    (x : MvPolynomial (Fin k × ZMod N) K →+* L) (y : Fin r × Fin (m + 1) → ResidueField W)
    (v : Fin k × ZMod N) : L :=
  (fun t : Fin r × Fin (m + 1) ↦ x (C (T.embedding v.2 (y t).out))) ⬝ᵥ x ∘ T.entryCoeff hm v

/-- In characteristic `p`, raising a coordinate of the point `T.entryFormValue hm x y` to the power
`P ^ j` raises its coefficients to that power and moves its letter `s` to `s + j`.

The Frobenius cycle `T` gives a power `P = T.P` of the prime `p = T.p`, ring maps
`ι_s = T.embedding s : W → K` on the local ring `W` for the letters `s` in `ZMod N`, and a parity
`T.isEven s` that alternates with `s`. For `k = 2 r + m`, a pair `t = (a, l)` in
`Fin r × Fin (m + 1)` names the position of a `k × k` matrix in the row `a` and the column `a + r`
if `l = 0` and `k - l` otherwise. -/
lemma entryFormValue_pow {r m : ℕ} (hm : 2 * r + m = k) {L : Type} [Field L]
    {x : MvPolynomial (Fin k × ZMod N) K →+* L} [CharP K T.p] [CharP L T.p]
    (y : Fin r × Fin (m + 1) → ResidueField W) (v : Fin k × ZMod N) (j : ℕ) :
    T.entryFormValue hm x y v ^ T.P ^ j =
      (x ∘ T.entryCoeff hm v) ^ T.P ^ j ⬝ᵥ
        fun t : Fin r × Fin (m + 1) ↦ x (C (T.embedding (v.2 + j) (y t).out)) := by
  have : Fact T.p.Prime := ⟨T.prime⟩
  have h_frob (u : W) : T.embedding (v.2 + j) u = T.embedding v.2 u ^ T.P ^ j := by
    simpa [CharP.cast_eq_zero, sub_eq_zero] using T.frobenius_pow_congr j v.2 u
  -- `T.P ^ j` is a power of `p`, so raising to it commutes with the sum and with the products.
  rw [entryFormValue, dotProduct_comm, dotProduct, ← pow_mul, sum_pow_char_pow]
  simp [dotProduct, pow_mul, mul_pow, h_frob]

/-- There is `g` in `GL_k(W)` such that the ring map `T.specializeShallow r x`, which keeps the deep
variables and reads the constants and the other variables in `L` through `x`, sends the translate by
`g⁻¹` of each deep variable `X v` to `X v - z v`.

The Frobenius cycle `T` gives a power `P = T.P` of the prime `p = T.p`, ring maps
`ι_s = T.embedding s : W → K` on the local ring `W` for the letters `s` in `ZMod N`, and a parity
`T.isEven s` that alternates with `s`. An element `g` of `GL_k(W)` translates polynomials by the
substitution `T.polyAction g`, which sends `X (b, s)` to `∑ c, g_s c b * X (c, s)`, where `g_s` is
`ι_s` applied to the entries of `g` for even `s` and of its inverse transpose for odd `s`.

For `k = 2 r + m`, a pair `t = (a, l)` in `Fin r × Fin (m + 1)` names the position of a `k × k`
matrix in the row `a` and the column `a + r` if `l = 0` and `k - l` otherwise. For residues `y t` of
`W` with lifts `(y t).out`, the point `z = T.entryFormValue hm x y` has the coordinate
`x (∑ t, C (ι_s (y t).out) * T.entryCoeff hm v t)` at `v = (b, s)`. -/
lemma exists_specializeShallow_polyAction_X_eq_sub [NeZero N]
    {r m : ℕ} (hm : 2 * r + m = k) {L : Type} [Field L]
    {x : MvPolynomial (Fin k × ZMod N) K →+* L} (y : Fin r × Fin (m + 1) → ResidueField W) :
    ∃ g : GL (Fin k) W, ∀ v : Fin k × ZMod N, T.deepIndicator r v ≠ 0 →
      T.specializeShallow r x (T.polyAction g⁻¹ (X v)) = X v - C (T.entryFormValue hm x y v) := by
  -- Take `g = 1 + A`, where `A` has the entry `(y t).out` at each position `t`.
  let A : Matrix (Fin k) (Fin k) W :=
    ∑ t : Fin r × Fin (m + 1), Matrix.single (entryRow hm t) (entryCol hm t) (y t).out
  have A_apply (a b : Fin k) : A a b = ∑ t : Fin r × Fin (m + 1),
      if entryRow hm t = a ∧ entryCol hm t = b then (y t).out else 0 := by
    simp [A, Matrix.sum_apply, Matrix.single]
  -- The positions lie in rows `< r` and columns `≥ r`, so `A ^ 2 = 0` and `1 - A` inverts `1 + A`.
  have h_row (t : Fin r × Fin (m + 1)) : entryRow hm t < r := by simp [entryRow]
  have h_col (t : Fin r × Fin (m + 1)) : r ≤ entryCol hm t := by grind [entryCol]
  have h_sq : A * A = 0 := by
    simp [A, univ.sum_mul_sum, fun t t' ↦ (Fin.lt_def.2 ((h_row t').trans_le (h_col t))).ne']
  let g : GL (Fin k) W :=
    ⟨1 + A, 1 - A, by simp [add_mul, mul_sub, h_sq], by simp [sub_mul, mul_add, h_sq]⟩
  have h_matrix (s : ZMod N) :
      T.letterMatrix s g⁻¹ = (if T.isEven s then 1 - A else 1 + Aᵀ).map (T.embedding s) := by
    simp [letterMatrix_apply, g]
  refine ⟨g, fun v hv ↦ ?_⟩
  have h_image : T.polyAction g⁻¹ (X v) =
      X v - ∑ t : Fin r × Fin (m + 1), C (T.embedding v.2 (y t).out) * T.entryCoeff hm v t := by
    have h_sum : ∑ t : Fin r × Fin (m + 1), C (T.embedding v.2 (y t).out) * T.entryCoeff hm v t =
        if T.isEven v.2 then ∑ b : Fin k, C (T.embedding v.2 (A b v.1)) * X (b, v.2)
          else -∑ b : Fin k, C (T.embedding v.2 (A v.1 b)) * X (b, v.2) := by
      cases h_even : T.isEven v.2 <;>
        simp [A_apply, entryCoeff, rootVar, h_even, univ.sum_mul, ite_and, Prod.ext_iff,
          Finset.sum_comm (α := Fin r × Fin (m + 1)), apply_ite (DFunLike.coe _)]
    rw [polyAction_X, h_matrix, h_sum]
    cases h_even : T.isEven v.2 <;>
      simp [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, Matrix.one_apply,
        apply_ite (DFunLike.coe _)]
  -- The coefficients involve only variables that are not deep.
  have h_coeff (t : Fin r × Fin (m + 1)) :
      T.specializeShallow r x (T.entryCoeff hm v t) = C (x (T.entryCoeff hm v t)) := by
    have h_zero : T.deepIndicator r (T.rootVar (entryCol hm t) (entryRow hm t) v.2) = 0 := by
      cases h_even : T.isEven v.2 <;> simp [deepIndicator, rootVar, h_even, h_row t, h_col t]
    rw [entryCoeff]
    split_ifs <;> simp [specializeShallow, h_zero]
  have h_X : T.specializeShallow r x (X v) = X v := by simp [specializeShallow, hv]
  have h_C (a : K) : T.specializeShallow r x (C a) = C (x (C a)) := by simp [specializeShallow]
  simp [h_image, h_coeff, h_X, h_C, entryFormValue, dotProduct]

end Points

section Weight

variable {N k : ℕ} {W K : Type} [CommRing W] [IsLocalRing W] [Field K] (T : FrobeniusCycle N W K)

/-- Suppose that for each `u` in `S` there are `v` and `e < o v` with `u ⬝ᵥ a y = z y v ^ e` for
all `y`. Then for each `u` in the span of `S` one polynomial has the value `u ⬝ᵥ a y` at `z y` for
all `y`, and its monomials have cost below `1`, where the variable `v` costs `1 / o v`. -/
lemma _root_.New.exists_eval_eq_dotProduct_of_mem_span {σ I Y L : Type*} [Fintype I] [Field L]
    {o : σ → ℕ} {z : Y → σ → L} {a : Y → I → L} {S : Set (I → L)}
    (hS : ∀ u ∈ S, ∃ (v : σ) (e : ℕ), e < o v ∧ ∀ y : Y, u ⬝ᵥ a y = z y v ^ e) {u : I → L}
    (hu : u ∈ Submodule.span L S) :
    ∃ g : MvPolynomial σ L,
      (∀ α ∈ g.support, weight (fun v : σ ↦ (o v : ℝ))⁻¹ α < 1) ∧
      ∀ y : Y, eval (z y) g = u ⬝ᵥ a y := by
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨v, e, h_lt, h_eval⟩ := hS u hu
    refine ⟨X v ^ e, fun α hα ↦ ?_, fun y ↦ by rw [h_eval, map_pow, eval_X]⟩
    obtain rfl : Finsupp.single v e = α := by simpa [X_pow_eq_monomial] using hα
    have h_cast : (e : ℝ) < o v := Nat.cast_lt.2 h_lt
    calc weight (fun v : σ ↦ (o v : ℝ))⁻¹ (Finsupp.single v e) = e / o v := by
          simp [weight_single, div_eq_mul_inv]
      _ < 1 := (div_lt_one (h_cast.trans_le' e.cast_nonneg)).2 h_cast
  | zero => exact ⟨0, by simp, by simp⟩
  | add u u' _ _ ih ih' =>
    obtain ⟨g, hg_cost, hg_eval⟩ := ih
    obtain ⟨g', hg'_cost, hg'_eval⟩ := ih'
    refine ⟨g + g', fun α hα ↦ ?_, fun y ↦ by simp [hg_eval, hg'_eval]⟩
    exact (mem_union.1 (MvPolynomial.support_add hα)).elim (hg_cost α) (hg'_cost α)
  | smul s u _ ih =>
    obtain ⟨g, hg_cost, hg_eval⟩ := ih
    exact ⟨s • g, fun α hα ↦ hg_cost α (MvPolynomial.support_smul hα), fun y ↦ by simp [hg_eval]⟩

/-- Let `x` embed the polynomials over `K` in a field `L`, both fields of characteristic `p`. Each
linear form `∑ t, u t * x (C (ι_i (y t).out))` is the value at the point `z` of a polynomial that
does not depend on `y` and whose monomials cost less than `1`, where the variable `v` costs
`1 / T.deepOrder r v`.

The Frobenius cycle `T` gives a power `P = T.P` of the prime `p = T.p`, ring maps
`ι_s = T.embedding s : W → K` on the local ring `W` for the letters `s` in `ZMod N`, and a parity
`T.isEven s` that alternates with `s`.

For `k = 2 r + m`, a pair `t = (a, l)` in `Fin r × Fin (m + 1)` names the position of a `k × k`
matrix in the row `a` and the column `a + r` if `l = 0` and `k - l` otherwise. For residues `y t` of
`W` with lifts `(y t).out`, the point `z = T.entryFormValue hm x y` has the coordinate
`x (∑ t, C (ι_s (y t).out) * T.entryCoeff hm v t)` at `v = (b, s)`. -/
lemma exists_eval_entryFormValue_eq_dotProduct [CharP K T.p] {r m : ℕ} (hm : 2 * r + m = k)
    {L : Type} [Field L] [CharP L T.p] {x : MvPolynomial (Fin k × ZMod N) K →+* L}
    (hx : Function.Injective x) (i : ZMod N) (u : Fin r × Fin (m + 1) → L) :
    ∃ g : MvPolynomial (Fin k × ZMod N) L,
      (∀ α ∈ g.support, weight (fun v : Fin k × ZMod N ↦ (T.deepOrder r v : ℝ))⁻¹ α < 1) ∧
      ∀ y : Fin r × Fin (m + 1) → ResidueField W, eval (T.entryFormValue hm x y) g =
        u ⬝ᵥ fun t : Fin r × Fin (m + 1) ↦ x (C (T.embedding i (y t).out)) := by
  refine exists_eval_eq_dotProduct_of_mem_span ?_ (T.mem_lowPowerForms hm hx i u)
  -- A generator is the entrywise power of the vector of some variable `v` by some small `P ^ j`.
  rintro _ ⟨v, j, rfl, (h_lt : T.P ^ j < T.deepOrder r v), rfl⟩
  exact ⟨v, T.P ^ j, h_lt, fun y ↦ (T.entryFormValue_pow hm y v j).symm⟩

/-- Let `x` embed the polynomials over `K` in a field `L`, both fields of characteristic `p`. For
each variable `v` there is a polynomial that does not depend on `y`, has the value
`z v ^ T.deepOrder r v` at the point `z`, and whose monomials cost less than `1`, where the variable
`w` costs `1 / T.deepOrder r w`.

The Frobenius cycle `T` gives a power `P = T.P` of the prime `p = T.p`, ring maps
`ι_s = T.embedding s : W → K` on the local ring `W` for the letters `s` in `ZMod N`, and a parity
`T.isEven s` that alternates with `s`.

For `k = 2 r + m`, a pair `t = (a, l)` in `Fin r × Fin (m + 1)` names the position of a `k × k`
matrix in the row `a` and the column `a + r` if `l = 0` and `k - l` otherwise. For residues `y t` of
`W` with lifts `(y t).out`, the point `z = T.entryFormValue hm x y` has the coordinate
`x (∑ t, C (ι_s (y t).out) * T.entryCoeff hm v t)` at `v = (b, s)`. -/
lemma exists_eval_entryFormValue_eq_pow_deepOrder [CharP K T.p] {r m : ℕ} (hm : 2 * r + m = k)
    {L : Type} [Field L] [CharP L T.p] {x : MvPolynomial (Fin k × ZMod N) K →+* L}
    (hx : Function.Injective x) (v : Fin k × ZMod N) :
    ∃ g : MvPolynomial (Fin k × ZMod N) L,
      (∀ α ∈ g.support, weight (fun w : Fin k × ZMod N ↦ (T.deepOrder r w : ℝ))⁻¹ α < 1) ∧
      ∀ y : Fin r × Fin (m + 1) → ResidueField W,
        eval (T.entryFormValue hm x y) g = T.entryFormValue hm x y v ^ T.deepOrder r v := by
  -- `T.deepOrder r v` is a power `P ^ j`, so the value is a linear form in the `ι_i (y t).out`,
  -- where `i` is the letter of `v` plus `j`.
  let j : ℕ := T.deepIndicator r v * if 2 * r ≤ v.1 then 2 * r else 1
  have h_pow (y : Fin r × Fin (m + 1) → ResidueField W) :
      T.entryFormValue hm x y v ^ T.deepOrder r v =
        (x ∘ T.entryCoeff hm v) ^ T.P ^ j ⬝ᵥ fun t ↦ x (C (T.embedding (v.2 + j) (y t).out)) :=
    T.entryFormValue_pow hm y v j
  obtain ⟨g, hg_cost, hg_eval⟩ := T.exists_eval_entryFormValue_eq_dotProduct hm hx (v.2 + j) _
  exact ⟨g, hg_cost, fun y ↦ (hg_eval y).trans (h_pow y).symm⟩

/-- Let `x` embed the polynomials over `K` in a field `L`, both fields of characteristic `p`. Then
the point `z` determines the residues `y t`.

The Frobenius cycle `T` gives a power `P = T.P` of the prime `p = T.p`, ring maps
`ι_s = T.embedding s : W → K` on the local ring `W` for the letters `s` in `ZMod N`, and a parity
`T.isEven s` that alternates with `s`. For `k = 2 r + m`, a pair `t = (a, l)` in
`Fin r × Fin (m + 1)` names the position of a `k × k` matrix in the row `a` and the column `a + r`
if `l = 0` and `k - l` otherwise. For residues `y t` of `W` with lifts `(y t).out`, the point
`z = T.entryFormValue hm x y` has the coordinate `x (∑ t, C (ι_s (y t).out) * T.entryCoeff hm v t)`
at `v = (b, s)`. -/
lemma entryFormValue_injective [CharP K T.p] {r m : ℕ} (hm : 2 * r + m = k)
    {L : Type} [Field L] [CharP L T.p] {x : MvPolynomial (Fin k × ZMod N) K →+* L}
    (hx : Function.Injective x) : Function.Injective (T.entryFormValue hm x) := by
  intro y y' h_point
  ext t
  -- The entry at `t` is the value of one polynomial at the point.
  obtain ⟨g, -, hg⟩ := T.exists_eval_entryFormValue_eq_dotProduct hm hx 0 (Pi.single t 1)
  have h_entry (y : Fin r × Fin (m + 1) → ResidueField W) :
      eval (T.entryFormValue hm x y) g = x (C (T.embedding 0 (y t).out)) := by simp [hg]
  have h_eq : T.embedding 0 (y t).out = T.embedding 0 (y' t).out :=
    C_injective (Fin k × ZMod N) K (hx (by rw [← h_entry, ← h_entry, h_point]))
  rw [← (y t).out_eq, ← (y' t).out_eq]
  exact T.residue_eq_of_embedding_eq h_eq

variable [NeZero N]

/-- If `F` lies in `T.deepForms k n r τ`, its form vanishes to order `τ` at the point `z` once
`T.specializeShallow r x` keeps the deep variables and reads the constants and the other variables
in `L` through `x`.

The Frobenius cycle `T` gives a power `P = T.P` of the prime `p = T.p`, ring maps
`ι_s = T.embedding s : W → K` on the local ring `W` for the letters `s` in `ZMod N`, and a parity
`T.isEven s` that alternates with `s`. The variable `X (b, s)`, of index `b < k` and letter `s`, is
deep for `r` if `s` is even and `r ≤ b`, or `s` is odd and `b < r`; `T.deepIndicator r` is the
indicator of these `(b, s)`. An element `g` of `GL_k(W)` translates polynomials by the substitution
`T.polyAction g`, which sends `X (b, s)` to `∑ c, g_s c b * X (c, s)`, where `g_s` is `ι_s` applied
to the entries of `g` for even `s` and of its inverse transpose for odd `s`. A function `F` on
`Exponents N k n` is the coefficient vector of the form `polyOfCoeffs F` over `K`, of degree `n` in
the `k` variables of each letter. It lies in `T.deepForms k n r τ` if all translates of the form
have only monomials of degree at least `τ` in the deep variables.

For `k = 2 r + m`, a pair `t = (a, l)` in `Fin r × Fin (m + 1)` names the position of a `k × k`
matrix in the row `a` and the column `c`, where `c = a + r` if `l = 0` and `c = k - l` otherwise.
The polynomial `T.entryCoeff hm v t` is `X (a, s)` if `v = (c, s)` with `s` even, `-X (c, s)` if
`v = (a, s)` with `s` odd, and `0` otherwise. For residues `y t` of `W` with lifts `(y t).out`, the
point `z = T.entryFormValue hm x y` has the coordinate
`x (∑ t, C (ι_s (y t).out) * T.entryCoeff hm v t)` at `v = (b, s)`. -/
lemma specializeShallow_polyOfCoeffs_mem_vanishingIdeal_pow {n r m τ : ℕ} (hm : 2 * r + m = k)
    {L : Type} [Field L] (x : MvPolynomial (Fin k × ZMod N) K →+* L)
    {F : Exponents N k n → K} (hF : F ∈ T.deepForms k n r τ)
    (y : Fin r × Fin (m + 1) → ResidueField W) :
    T.specializeShallow r x (polyOfCoeffs F) ∈ vanishingIdeal L {T.entryFormValue hm x y} ^ τ := by
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin k) W, ∀ v : Fin k × ZMod N, T.deepIndicator r v ≠ 0 →
      T.specializeShallow r x (T.polyAction g⁻¹ (X v)) = X v - C (T.entryFormValue hm x y v) :=
    T.exists_specializeShallow_polyAction_X_eq_sub hm y
  refine T.map_polyOfCoeffs_mem_pow_of_mem_deepForms hF _ _ g fun v ↦ ?_
  obtain h_shallow | h_deep := T.deepIndicator_eq_zero_or_eq_one r v
  · simp [h_shallow]
  · simp [hg v (h_deep.trans_ne one_ne_zero), h_deep]

/-- Let `K` have characteristic `p` and `2 r ≤ k`. A non-zero `F` in `T.deepForms k n r τ` has
`F β ≠ 0` for a monomial `β` of weight at least `τ`. The weight is the sum over the variables of the
exponent (`exponentOf β`) times `P ^ (-2 r)` for a deep variable with `2 r ≤ b`, `1 / P` for a deep
one with `b < 2 r`, and `0` for the others. -/
theorem exists_le_weight_of_mem_deepForms [CharP K T.p] {n r τ : ℕ}
    {F : Exponents N k n → K} (hk : 2 * r ≤ k)
    (hF : F ∈ T.deepForms k n r τ) (hF_ne : F ≠ 0) :
    ∃ β : Exponents N k n,
      F β ≠ 0 ∧
      τ ≤ (exponentOf β).weight fun v : Fin k × ZMod N ↦
          (T.deepIndicator r v / T.P ^ (if 2 * r ≤ v.1 then 2 * r else 1) : ℝ) := by
  -- Read `F` as a polynomial `f` in the deep variables over the field of rational functions. Each
  -- `1 + A`, with `A` in rows `< r` and columns `≥ r`, gives a zero of order `≥ τ`, and
  -- `exists_le_weight_of_mem_vanishingIdeal_pow` turns these zeros into a costly monomial. The
  -- variables that are not deep are carried along with degree `1`.
  have : Finite (ResidueField W) := T.finite_residueField
  have : Fintype (ResidueField W) := ofFinite (ResidueField W)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * r + m = k := hk.dest
  let L : Type := FractionRing (MvPolynomial (Fin k × ZMod N) K)
  let x : MvPolynomial (Fin k × ZMod N) K →+* L := algebraMap _ L
  have hx : Function.Injective x := IsFractionRing.injective _ _
  -- The variable `v` costs `1 / κ v`.
  let κ : Fin k × ZMod N → ℕ := T.deepOrder r
  have hκ (v : Fin k × ZMod N) : 0 < κ v := pow_pos (pow_pos T.prime.pos _) _
  let point : (Fin r × Fin (m + 1) → ResidueField W) → Fin k × ZMod N → L := T.entryFormValue hm x
  let cost : (Fin k × ZMod N →₀ ℕ) →+ ℝ := weight (fun v : Fin k × ZMod N ↦ (κ v : ℝ))⁻¹
  have h_eqs (v : Fin k × ZMod N) : ∃ g : MvPolynomial (Fin k × ZMod N) L,
      (∀ α ∈ g.support, cost α < 1) ∧ ∀ y, eval (point y) g = point y v ^ κ v :=
    T.exists_eval_entryFormValue_eq_pow_deepOrder hm hx v
  choose g hg_cost hg_eval using h_eqs
  have h_card : ∏ v, κ v ≤ Fintype.card (Fin r × Fin (m + 1) → ResidueField W) := by
    rw [card_fun, card_eq_nat_card, T.card_residueField]
    simpa [κ] using T.prod_deepOrder_le hm
  let f : MvPolynomial (Fin k × ZMod N) L := T.specializeShallow r x (polyOfCoeffs F)
  have h_ne : f ≠ 0 := T.specializeShallow_polyOfCoeffs_ne_zero r hx hF_ne
  have h_order (y : Fin r × Fin (m + 1) → ResidueField W) :
      f ∈ vanishingIdeal L {point y} ^ τ :=
    T.specializeShallow_polyOfCoeffs_mem_vanishingIdeal_pow hm x hF y
  obtain ⟨α, hα, h_cost⟩ : ∃ α ∈ f.support, τ ≤ cost α :=
    exists_le_weight_of_mem_vanishingIdeal_pow κ hκ point (T.entryFormValue_injective hm hx) h_card
      g hg_cost hg_eval τ f h_ne h_order
  obtain ⟨β, hβ, hαβ⟩ : ∃ β : Exponents N k n, F β ≠ 0 ∧
      ∀ v : Fin k × ZMod N, α v = if T.deepIndicator r v = 0 then 0 else exponentOf β v :=
    T.exists_eq_of_mem_support_specializeShallow hα
  -- `α` is the deep part of `exponentOf β`, so its cost is the weight of `β`.
  have h_term (v : Fin k × ZMod N) : (α v : ℝ) * (κ v : ℝ)⁻¹ =
      exponentOf β v * (T.deepIndicator r v / T.P ^ (if 2 * r ≤ v.1 then 2 * r else 1) : ℝ) := by
    obtain h_shallow | h_deep := T.deepIndicator_eq_zero_or_eq_one r v
    · simp [hαβ, h_shallow]
    · simp [hαβ, κ, deepOrder, h_deep]
  refine ⟨β, hβ, h_cost.trans_eq ?_⟩
  simp only [cost, weight_eq_sum, nsmul_eq_mul, Pi.inv_apply, h_term]

end Weight

end New.FrobeniusCycle

/-! ## Dimension counts for forms of large depth -/

section DepthCount

open Finset Module Finsupp Nat

/-- The number `N n (P ^ (-2 r) + r ^ 2 / (k P))`, for `N` letters, `k` variables and degree `n` in
each letter, the prime power `P = T.P`, and the index `r` at which deep and shallow variables change
places. In `New.FrobeniusCycle.sum_finrank_deepForms_le`, over a field of characteristic `p` and for
`0 < 2 r ≤ k`, it bounds, up to the factor of the number of exponents, the sum of the dimensions of
the spaces of forms all of whose translates are deep. -/
def New.FrobeniusCycle.divisorConstant {N : ℕ} {W R : Type} [CommRing W] [IsLocalRing W]
    [CommRing R] (T : FrobeniusCycle N W R) (k n r : ℕ) : ℝ :=
  N * n * (1 / T.P ^ (2 * r) + r ^ 2 / (k * T.P))

/-- `T.divisorConstant k n r` depends on `T` only through `P`, so it is unchanged when the Frobenius
cycle is pushed forward along a ring map. -/
lemma New.FrobeniusCycle.divisorConstant_map {N : ℕ} {W R R' : Type} [CommRing W] [IsLocalRing W]
    [CommRing R] [CommRing R'] (f : R →+* R') (T : FrobeniusCycle N W R) (k n r : ℕ) :
    (T.map f).divisorConstant k n r = T.divisorConstant k n r :=
  rfl

/-- By symmetry in the variables, the entry at any variable `x = (b, s)` has the mean `n / k` over
all exponents (`New.Exponents`: `N`-tuples of exponents of monomials of degree `n` in `k` variables,
read at `x` by `New.exponentOf`). -/
lemma New.mul_sum_exponentOf {N k : ℕ} [NeZero N] (n : ℕ) (x : Fin k × ZMod N) :
    k * ∑ β : Exponents N k n, (exponentOf β x : ℝ) =
      Fintype.card (Monomials (Fin k) n) ^ N * n := by
  -- Swapping two rows permutes the monomials.
  have h_symm (a b : Fin k) (s : ZMod N) : ∑ β : Exponents N k n, (exponentOf β (a, s) : ℝ) =
      ∑ β : Exponents N k n, (exponentOf β (b, s) : ℝ) := by
    let swapRows : Equiv.Perm (Monomials (Fin k) n) :=
      Equiv.Perm.subtypePerm (equivCongrLeft (Equiv.swap a b)).symm fun α ↦ by
        simp only [mem_finsuppAntidiag']
        simp
    have h_swap (β : Exponents N k n) : exponentOf (swapRows ∘ β) (a, s) = exponentOf β (b, s) := by
      simp [swapRows, exponentOf]
    rw [← swapRows.bijective.comp_left.sum_comp]
    simp only [h_swap]
  calc k * ∑ β : Exponents N k n, (exponentOf β x : ℝ)
      = ∑ b : Fin k, ∑ β : Exponents N k n, (exponentOf β (b, x.2) : ℝ) := by
        simp [h_symm _ x.1]
    _ = ∑ β : Exponents N k n, (n : ℝ) := by
        simp [Finset.sum_comm (γ := Fin k), exponentOf, ← cast_sum, ← degree_eq_sum,
          Monomials.degree_eq]
    _ = Fintype.card (Monomials (Fin k) n) ^ N * n := by simp

/-- If every nonzero vector of a subspace `S` of functions on `ι` is nonzero at some point of a
finite set `s`, then `dim S ≤ #s`. -/
lemma New.finrank_le_card_of_forall_exists_ne_zero {K ι : Type*} [Field K]
    {S : Submodule K (ι → K)} {s : Finset ι} (hS : ∀ F ∈ S, F ≠ 0 → ∃ β ∈ s, F β ≠ 0) :
    finrank K S ≤ #s := by
  rw [← Fintype.card_coe, ← finrank_fintype_fun_eq_card K]
  let res : S →ₗ[K] s → K := (LinearMap.funLeft K K ((↑) : s → ι)).domRestrict S
  refine res.finrank_le_finrank_of_injective
    ((injective_iff_map_eq_zero res).2 fun F hF ↦ Subtype.ext ?_)
  by_contra h_ne
  obtain ⟨β, hβ, h_value⟩ := hS F F.property h_ne
  exact h_value (by simpa [res] using congrFun hF ⟨β, hβ⟩)

variable {N k : ℕ} [NeZero N] {W K : Type} [CommRing W] [IsLocalRing W] [Field K]

/-- The variable `x = (b, s)` is deep if `s` is even and `r ≤ b`, or `s` is odd and `b < r`. Give a
deep variable the cost `1 / P ^ (2 r)` if `2 r ≤ b` and `1 / P` otherwise, and the other variables
the cost `0`. For `0 < 2 r ≤ k` the costs add up to at most `N (k / P ^ (2 r) + r ^ 2 / P)`. -/
lemma New.FrobeniusCycle.sum_deepIndicator_div_le (T : FrobeniusCycle N W K) {r : ℕ} (hr : 0 < r)
    (hk : 2 * r ≤ k) :
    ∑ x : Fin k × ZMod N, (T.deepIndicator r x / T.P ^ (if 2 * r ≤ x.1 then 2 * r else 1) : ℝ) ≤
      N * (k / T.P ^ (2 * r) + r ^ 2 / T.P) := by
  -- Each index `b` is deep in `N / 2` letters; at most `k` indices have `2 r ≤ b`, and `2 r`
  -- indices have `b < 2 r`.
  have h_row (b : Fin k) :
      ∑ s : ZMod N, (T.deepIndicator r (b, s) / T.P ^ (if 2 * r ≤ b.val then 2 * r else 1) : ℝ) =
        (N / 2 : ℕ) / T.P ^ (if 2 * r ≤ b.val then 2 * r else 1) := by
    rw [← T.sum_deepIndicator r b, cast_sum, Finset.sum_div]
  have hr_sq : (r : ℝ) ≤ r ^ 2 := mod_cast Nat.le_self_pow two_ne_zero r
  calc _ = #{b : Fin k | 2 * r ≤ b.val} * ((N / 2 : ℕ) / (T.P : ℝ) ^ (2 * r)) +
          2 * r * ((N / 2 : ℕ) / T.P) := by
        simp only [Fintype.sum_prod_type, h_row]
        simp [apply_ite, sum_ite, Fin.card_filter_val_lt, hk]
    _ ≤ k * (N / 2 / T.P ^ (2 * r)) + 2 * r * (N / 2 / T.P) := by
        grw [card_finset_fin_le, cast_div_le]
        norm_num
    _ = N * (k / T.P ^ (2 * r) / 2 + r / T.P) := by ring
    _ ≤ N * (k / T.P ^ (2 * r) + r ^ 2 / T.P) := by
        grw [← hr_sq, half_le_self (by positivity : (0 : ℝ) ≤ k / T.P ^ (2 * r))]

/-- Let `K` have characteristic `p` and `0 < 2 r ≤ k`. For every `M` the dimensions of the spaces
`T.deepForms k n r δ` for `1 ≤ δ ≤ M` add up to at most `T.divisorConstant k n r = N n (P ^ (-2
r) + r ^ 2 / (k P))` times the number of `N`-tuples of monomials of degree `n` in `k` variables. -/
lemma New.FrobeniusCycle.sum_finrank_deepForms_le (T : FrobeniusCycle N W K) [CharP K T.p] (n : ℕ)
    {r : ℕ} (hr : 0 < r) (hk : 2 * r ≤ k) (M : ℕ) :
    (∑ d ∈ range M, finrank K (T.deepForms k n r (d + 1)) : ℝ) ≤
      T.divisorConstant k n r * Fintype.card (Monomials (Fin k) n) ^ N := by
  -- Give a deep variable `x` (`T.deepIndicator r x = 1`) the cost `1 / P ^ (2 r)` or `1 / P`. A
  -- monomial of cost `t` is counted for at most `t` depths, and the mean cost is at most
  -- `T.divisorConstant k n r`.
  have hk_pos : (0 : ℝ) < k := cast_pos.2 (by lia)
  let c (x : Fin k × ZMod N) : ℝ :=
    T.deepIndicator r x / T.P ^ (if 2 * r ≤ x.1 then 2 * r else 1)
  let cost (β : Exponents N k n) : ℝ := (exponentOf β).weight c
  set total : ℝ := Fintype.card (Monomials (Fin k) n) ^ N
  have h_rank (d : ℕ) :
      finrank K (T.deepForms k n r (d + 1)) ≤ #{β : Exponents N k n | d < ⌊cost β⌋₊} := by
    refine finrank_le_card_of_forall_exists_ne_zero fun F hF hF_ne ↦ ?_
    obtain ⟨β, hβ, h_cost⟩ : ∃ β : Exponents N k n, F β ≠ 0 ∧ (d + 1 : ℕ) ≤ cost β :=
      T.exists_le_weight_of_mem_deepForms hk hF hF_ne
    exact ⟨β, mem_filter.2 ⟨mem_univ β, le_floor h_cost⟩, hβ⟩
  have h_count (β : Exponents N k n) : (#{d ∈ range M | d < ⌊cost β⌋₊} : ℝ) ≤ cost β := by
    have h_nonneg : 0 ≤ cost β := by
      simp only [cost, weight_eq_sum]
      positivity
    have h_subset : {d ∈ range M | d < ⌊cost β⌋₊} ⊆ range ⌊cost β⌋₊ := by grind
    exact (cast_le.2 ((card_le_card h_subset).trans_eq (card_range _))).trans (floor_le h_nonneg)
  have h_mean (x : Fin k × ZMod N) :
      ∑ β : Exponents N k n, (exponentOf β x : ℝ) = total * n / k := by
    rw [eq_div_iff hk_pos.ne', mul_comm, mul_sum_exponentOf]
  calc (∑ d ∈ range M, finrank K (T.deepForms k n r (d + 1)) : ℝ)
      ≤ ∑ d ∈ range M, (#{β : Exponents N k n | d < ⌊cost β⌋₊} : ℝ) :=
        sum_le_sum fun d _ ↦ cast_le.2 (h_rank d)
    _ = ∑ β : Exponents N k n, (#{d ∈ range M | d < ⌊cost β⌋₊} : ℝ) := by
        simp only [card_filter, cast_sum, Finset.sum_comm (s := range M)]
    _ ≤ ∑ β : Exponents N k n, cost β := sum_le_sum fun β _ ↦ h_count β
    _ = total * n / k * ∑ x : Fin k × ZMod N, c x := by
        simp only [cost, weight_eq_sum, nsmul_eq_mul, Finset.sum_comm (γ := Exponents N k n),
          ← Finset.sum_mul, h_mean, ← Finset.mul_sum]
    _ ≤ total * n / k * (N * (k / T.P ^ (2 * r) + r ^ 2 / T.P)) := by
        grw [T.sum_deepIndicator_div_le hr hk]
    _ = T.divisorConstant k n r * total := by
        rw [divisorConstant]
        field

end DepthCount

end
