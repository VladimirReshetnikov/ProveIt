import Lib.Base

/-!
# Orthogonality, Fourier inversion and matrix Gauss sums over a finite ring

Finite Fourier analysis on matrices over a finite commutative ring `R`, for a primitive additive
character `ψ` (no multiple `ψ (r * ·)` with `r ≠ 0` is trivial).

* `New.exists_isPrimitive_apply_eq_of_surjective`, `New.exists_primitive_residue_addChar`: a
  character of a ring `F` for which the subring `O` is self-dual induces a primitive character of a
  suitable quotient ring of `O`.
* `New.sum_addChar_dotProduct`, `New.sum_addChar_trace_mul`: orthogonality; the sum of `ψ` along
  a nonzero linear form on vectors or on matrices is `0`.
* `New.Exchange.matrixFourier`, `New.Exchange.matrixFourier_matrixFourier`: the transform
  `ρ ↦ ∑ v, f v * ψ (tr (ρ v))`, not normalised, and its inversion formula.
* `New.exists_sum_smul_addChar_trace_eq`: every function on matrices is a linear combination of
  the characters `y ↦ ψ (tr (y u))`.
* `New.Exchange.exists_matrixFourier_eq_mul_inv_det`: the transform of a function with
  `S (g d) = χ (det g) S d`, for a multiplicative character `χ` (zero off the units) that is
  primitive, `New.Exchange.IsPrimitiveMulChar`, and the modulus of the Gauss sum of `χ ∘ det`.

## Relation to the literature

Known; see `Lib.Weil.TameGaussSum` for sources.
-/

open Matrix Finset Fintype AddChar Function

/-- An additive character `ψ` sends a finite sum to the product of its values on the terms. -/
lemma AddChar.map_sum_eq_prod {ι A M : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, map_add_eq_mul, ih]

namespace New

variable {R F a N : Type*} [CommRing R]

/-- Let `O` be a subring of `F`, `π : O → R` a surjective ring homomorphism (`hπ_surj`) with kernel
`{x | g * x ∈ O}` (`hπ_ker`), and `ψ` an additive character of `F` such that `ψ (t * ·)` is
trivial on `O` exactly when `t ∈ O` (`hψ`). Then `π x ↦ ψ (g * x)` is a well-defined primitive
character of `R`. -/
lemma exists_isPrimitive_apply_eq_of_surjective [CommRing F] {O : Subring F} {π : O →+* R}
    {g : F} {ψ : AddChar F ℂ} (hπ_surj : Surjective π) (hπ_ker : ∀ x : O, π x = 0 ↔ g * x.val ∈ O)
    (hψ : ∀ t : F, (∀ s ∈ O, ψ (t * s) = 1) ↔ t ∈ O) :
    ∃ φ : AddChar R ℂ, φ.IsPrimitive ∧ ∀ x : O, φ (π x) = ψ (g * x) := by
  -- `x ↦ ψ (g * x)` is constant on the fibres of `π`, since `π x = π y` puts `g * (x - y)` in `O`.
  have h_factors : Function.FactorsThrough (fun x : O ↦ ψ (g * x)) π := by
    intro x y hxy
    have h_mem : g * (x - y : O).val ∈ O := (hπ_ker (x - y)).mp (by simp [hxy])
    exact eq_of_div_eq_one <| by
      simpa [mul_sub, map_sub_eq_div] using (hψ _).mpr h_mem 1 O.one_mem
  let φ : R → ℂ := Function.extend π (fun x : O ↦ ψ (g * x)) 1
  have hφ (x : O) : φ (π x) = ψ (g * x) := h_factors.extend_apply 1 x
  have h_add (r s : R) : φ (r + s) = φ r * φ s := by
    obtain ⟨x, rfl⟩ := hπ_surj r
    obtain ⟨y, rfl⟩ := hπ_surj s
    simp [← map_add, hφ, mul_add, map_add_eq_mul]
  let φ' : AddChar R ℂ :=
    { toFun := φ, map_zero_eq_one' := by simpa using hφ 0, map_add_eq_mul' := h_add }
  -- Primitivity: if `φ (π x * ·)` is trivial then `ψ (g * x * ·)` is trivial on `O`, so `π x = 0`.
  refine ⟨φ', fun r hr_ne h_triv ↦ ?_, hφ⟩
  obtain ⟨x, rfl⟩ := hπ_surj r
  have h_triv_O : ∀ s ∈ O, ψ (g * x * s) = 1 := fun s hs ↦ by
    simpa [← map_mul, hφ, φ', mul_assoc] using DFunLike.congr_fun h_triv (π ⟨s, hs⟩)
  exact hr_ne ((hπ_ker x).mpr ((hψ _).mp h_triv_O))

/-- `New.exists_isPrimitive_apply_eq_of_surjective` with its two conditions on `π` joined in
one hypothesis `hπ`: `π` is surjective, and its kernel is `{x | g * x ∈ O}`. Then `π x ↦ ψ (g * x)`
is a well-defined primitive character of `R`. -/
lemma exists_primitive_residue_addChar [CommRing F] {O : Subring F} {π : O →+* R} {g : F}
    {ψ : AddChar F ℂ} (hπ : Surjective π ∧ ∀ x : O, π x = 0 ↔ g * x.val ∈ O)
    (hψ : ∀ t : F, (∀ s ∈ O, ψ (t * s) = 1) ↔ t ∈ O) :
    ∃ φ : AddChar R ℂ, φ.IsPrimitive ∧ ∀ x : O, φ (π x) = ψ (g * x) :=
  exists_isPrimitive_apply_eq_of_surjective hπ.left hπ.right hψ

variable [Fintype R] [DecidableEq R] [Fintype a] [DecidableEq a] [Fintype N] [DecidableEq N]

/-! ### The Fourier transform on matrices -/

/-- The Fourier transform of a function `f` on `N × a` matrices, a function on `a × N` matrices:
`ρ ↦ ∑ v, f v * ψ (tr (ρ v))`, with no normalising factor. -/
noncomputable def Exchange.matrixFourier (ψ : AddChar R ℂ) (f : Matrix N a R → ℂ)
    (ρ : Matrix a N R) : ℂ :=
  ∑ v : Matrix N a R, f v * ψ (ρ * v).trace

variable (χ : MulChar R ℂ) in
/-- The multiplicative character `χ` of the finite ring `R` is primitive: for every `a ≠ 0` some
element `1 + c * a` has `χ`-value different from `0` (so it is a unit) and from `1`. That is,
for no nonzero `a` is `χ` trivial on the units congruent to `1` modulo `a`. -/
def Exchange.IsPrimitiveMulChar : Prop :=
  ∀ a ≠ (0 : R), ∃ c : R, χ (1 + c * a) ≠ 0 ∧ χ (1 + c * a) ≠ 1

variable {χ : MulChar R ℂ} {ψ : AddChar R ℂ}

/-- Orthogonality of characters along a linear form: for a primitive additive character `ψ` of `R`
and a vector `z` in `R^a`, the sum of `ψ (z ⬝ᵥ x)` over all `x` in `R^a` is the number of such `x`
if `z = 0` and `0` otherwise. -/
lemma sum_addChar_dotProduct (hψ : ψ.IsPrimitive) (z : a → R) :
    ∑ x : a → R, ψ (z ⬝ᵥ x) = if z = 0 then Fintype.card (a → R) else 0 := by
  -- The sum splits into a product over the coordinates; by primitivity the factor at `i` is
  -- `card R` if `z i = 0` and `0` otherwise.
  calc ∑ x, ψ (z ⬝ᵥ x)
    _ = ∑ x : a → R, ∏ i, ψ (z i * x i) := by simp only [dotProduct, AddChar.map_sum_eq_prod]
    _ = ∏ i, ∑ t, ψ (z i * t) := (Fintype.prod_sum fun i t ↦ ψ (z i * t)).symm
    _ = _ := by simp [mul_comm, sum_mulShift, hψ, Fintype.prod_ite_zero, funext_iff]

/-- Orthogonality of characters on matrices: for a primitive additive character `ψ` of `R` and an
`a × N` matrix `ρ`, the sum of `ψ (tr (ρ v))` over all `N × a` matrices `v` is the number of such
matrices if `ρ = 0` and `0` otherwise. -/
lemma sum_addChar_trace_mul (hψ : ψ.IsPrimitive) (ρ : Matrix a N R) :
    ∑ v : Matrix N a R, ψ (ρ * v).trace = if ρ = 0 then Fintype.card (Matrix N a R) else 0 := by
  -- `tr (ρ v)` is the dot product of the matrices `ρᵀ` and `v` read as vectors
  simpa [← vec_bijective.sum_comp, vec_dotProduct_vec, card_of_bijective vec_bijective]
    using sum_addChar_dotProduct hψ ρᵀ.vec

/-- Fourier inversion for matrices over a finite commutative ring R with a primitive additive
character ψ: applying the transform `New.Exchange.matrixFourier` twice to f gives y ↦ f(−y) times
the number of matrices. -/
lemma Exchange.matrixFourier_matrixFourier (hψ : ψ.IsPrimitive) (f : Matrix N a R → ℂ)
    (y : Matrix N a R) :
    matrixFourier ψ (matrixFourier ψ f) y = f (-y) * Fintype.card (Matrix a N R) := by
  -- Exchange the two sums: by `sum_addChar_trace_mul` the inner sum `∑ u, ψ (tr ((v + y) u))`
  -- vanishes unless `v = -y`.
  have h_inner (v : Matrix N a R) : ∑ u : Matrix a N R, ψ ((v + y) * u).trace =
      ((if v + y = 0 then Fintype.card (Matrix a N R) else 0 : ℕ) : ℂ) :=
    sum_addChar_trace_mul hψ (v + y)
  have h_exp (u : Matrix a N R) (v : Matrix N a R) :
      ψ (u * v).trace * ψ (y * u).trace = ψ ((v + y) * u).trace := by
    rw [← map_add_eq_mul, trace_mul_comm u v, ← trace_add, ← Matrix.add_mul]
  calc matrixFourier ψ (matrixFourier ψ f) y
      = ∑ u : Matrix a N R, ∑ v, f v * ψ ((v + y) * u).trace := by
        simp only [matrixFourier, sum_mul, mul_assoc, h_exp]
    _ = ∑ v, f v * ∑ u : Matrix a N R, ψ ((v + y) * u).trace := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = ∑ v, if v = -y then f v * Fintype.card (Matrix a N R) else 0 := by
        simp [h_inner, add_eq_zero_iff_eq_neg]
    _ = f (-y) * Fintype.card (Matrix a N R) := by simp

/-- For a primitive additive character ψ of a finite commutative ring R, every complex function
f on N × a matrices over R is a linear combination of the characters y ↦ ψ(tr(yu)), for u
ranging over the a × N matrices. -/
lemma exists_sum_smul_addChar_trace_eq (hψ : ψ.IsPrimitive) (f : Matrix N a R → ℂ) :
    ∃ c : Matrix a N R → ℂ,
      ∑ u : Matrix a N R, c u • (fun y : Matrix N a R ↦ ψ (y * u).trace) = f := by
  -- Fourier inversion: the coefficients are the transform of `t ↦ f (-t)`, normalised.
  refine ⟨Exchange.matrixFourier ψ fun t ↦ f (-t) / card (Matrix a N R), funext fun y ↦ ?_⟩
  simpa [Exchange.matrixFourier, card_ne_zero] using
    Exchange.matrixFourier_matrixFourier hψ (fun t ↦ f (-t) / card (Matrix a N R)) y

/-- The first step towards the matrix Gauss sums. Let `R` be a finite commutative ring and `χ` a
primitive multiplicative character of `R` (`IsPrimitiveMulChar`: for no nonzero `a` is `χ` trivial
on the units congruent to `1` modulo `a`). Let `S` be a function on square matrices over `R` with
`S (g d) = χ (det g) S d` for all invertible `g`. Then the Fourier transform
`matrixFourier ψ S y = ∑ d, S d ψ (tr (y d))` equals `χ⁻¹ (det y)` times its value at `1`; in
particular it vanishes where `y` is not invertible. The additive character `ψ` may be any. -/
lemma Exchange.matrixFourier_eq_inv_det_mul (hχ : IsPrimitiveMulChar χ) (S : Matrix a a R → ℂ)
    (hS : ∀ (g : GL a R) (d : Matrix a a R), S (g.val * d) = χ g.val.det * S d) (y : Matrix a a R) :
    matrixFourier ψ S y = χ⁻¹ y.det * matrixFourier ψ S 1 := by
  -- Substituting `d ↦ g d` in the sum gives `χ (det g) Ŝ (z g) = Ŝ z`.
  have h_shift (g : GL a R) (z : Matrix a a R) :
      χ g.val.det * matrixFourier ψ S (z * g) = matrixFourier ψ S z :=
    calc χ g.val.det * matrixFourier ψ S (z * g)
      _ = ∑ d, S (g.val * d) * ψ (z * (g.val * d)).trace := by
        simp [matrixFourier, hS, mul_sum, mul_assoc]
      _ = matrixFourier ψ S z := g.mulLeft_bijective.sum_comp fun d ↦ S d * ψ (z * d).trace
  -- `Ŝ` vanishes off the units: some `g` fixes `z` and has `χ (det g) ≠ 1`.
  have h_zero (z : Matrix a a R) (hz : ¬IsUnit z) : matrixFourier ψ S z = 0 := by
    -- over a finite ring a non-unit is a zero divisor
    obtain ⟨D, hD, i, j, hij⟩ : ∃ D : Matrix a a R, z * D = 0 ∧ ∃ i j : a, D i j ≠ 0 := by
      by_contra! h_reg
      exact hz (isLeftRegular_iff_right_eq_zero_of_mul.2
        fun D hD ↦ ext (h_reg D hD)).isUnit_of_finite
    obtain ⟨c, hc_ne_zero, hc_ne_one⟩ : ∃ c : R, χ (1 + c * D i j) ≠ 0 ∧ χ (1 + c * D i j) ≠ 1 :=
      hχ (D i j) hij
    -- `g = 1 + c v eᵢᵀ`, where `v` is column `j` of `D`; `z v = 0` and `det g = 1 + c vᵢ`
    let g : Matrix a a R := 1 + D * single j () (1 : R) * single () i c
    have hg_det : g.det = 1 + c * D i j := by simp [g, det_one_add_mul_comm, ← Matrix.mul_assoc]
    have hg_fix : z * g = z := by simp [g, mul_add, ← Matrix.mul_assoc, hD]
    have hg_unit : IsUnit g.det := by simpa [hg_det, χ.apply_eq_zero_iff] using hc_ne_zero
    have h_mul_eq : χ (1 + c * D i j) * matrixFourier ψ S z = matrixFourier ψ S z := by
      simpa [hg_det, hg_fix] using h_shift (.mk'' g hg_unit) z
    -- `χ (1 + c * D i j) ≠ 1`, so the transform at `z` is `0`
    exact (mul_left_eq_self₀.mp h_mul_eq).resolve_left hc_ne_one
  by_cases hy : IsUnit y
  · obtain ⟨g, rfl⟩ := hy
    simp [χ.inv_apply, ← h_shift g⁻¹ g]
  · rw [h_zero y hy, χ⁻¹.map_nonunit (by rwa [← isUnit_iff_isUnit_det]), zero_mul]

/-- The second step towards the matrix Gauss sums. Let `ψ` be primitive, `χ` primitive in the sense
of `New.Exchange.IsPrimitiveMulChar`, and `S` a function on square matrices with
`S (g d) = χ (det g) S d` for all invertible `g`. Let `γ` be the Gauss sum of `χ ∘ det`, the
transform `New.Exchange.matrixFourier ψ (χ ∘ det)` at the matrix `1`. Then the complex conjugate of
`γ` times the transform of `S` at `1` is `S 1` times the number of matrices. The proof applies
Fourier inversion to `New.Exchange.matrixFourier_eq_inv_det_mul`. -/
lemma Exchange.star_matrixFourier_det_mul (hψ : ψ.IsPrimitive) (hχ : IsPrimitiveMulChar χ)
    (S : Matrix a a R → ℂ)
    (hS : ∀ (g : GL a R) (d : Matrix a a R), S (g.val * d) = χ g.val.det * S d) :
    star (matrixFourier ψ (fun d : Matrix a a R ↦ χ d.det) 1) * matrixFourier ψ S 1 =
      S 1 * Fintype.card (Matrix a a R) := by
  -- Fourier inversion at `-1`; conjugation turns `χ` into `χ⁻¹` and `ψ t` into `ψ (-t)`
  calc star (matrixFourier ψ (fun d : Matrix a a R ↦ χ d.det) 1) * matrixFourier ψ S 1
    _ = matrixFourier ψ (fun y : Matrix a a R ↦ χ⁻¹ y.det * matrixFourier ψ S 1) (-1) := by
      simp [matrixFourier, sum_mul, mul_right_comm, ← χ.star_eq_inv, ψ.map_neg_eq_conj]
    _ = matrixFourier ψ (matrixFourier ψ S) (-1) := by
      rw [← funext (matrixFourier_eq_inv_det_mul hχ S hS)]
    _ = S 1 * card (Matrix a a R) := by simpa using matrixFourier_matrixFourier hψ S (-1)

/-- Gauss sums of matrices over a finite ring, both steps in one statement. Let `ψ` be primitive,
`χ` primitive in the sense of `New.Exchange.IsPrimitiveMulChar`, and `S` a function on square
matrices with `S (g d) = χ (det g) S d` for all invertible `g`. Write `Ŝ` for its Fourier transform
`New.Exchange.matrixFourier ψ S`. Then (a) `Ŝ y = χ⁻¹ (det y) Ŝ 1` for every `y`, so `Ŝ` vanishes at
non-invertible `y` (`New.Exchange.matrixFourier_eq_inv_det_mul`). (b) `γ Ŝ 1` equals `S 1` times
the number of matrices, where `γ` is the complex conjugate of the transform of `χ ∘ det` at the
matrix `1` (`New.Exchange.star_matrixFourier_det_mul`). -/
lemma Exchange.matrixFourier_eq_and_star_mul_eq (hψ : ψ.IsPrimitive) (hχ : IsPrimitiveMulChar χ)
    (S : Matrix a a R → ℂ)
    (hS : ∀ (g : GL a R) (d : Matrix a a R), S (g.val * d) = χ g.val.det * S d) :
    (∀ y : Matrix a a R, matrixFourier ψ S y = χ⁻¹ y.det * matrixFourier ψ S 1) ∧
    star (matrixFourier ψ (fun d : Matrix a a R ↦ χ d.det) 1) * matrixFourier ψ S 1 =
      S 1 * Fintype.card (Matrix a a R) :=
  ⟨matrixFourier_eq_inv_det_mul hχ S hS, star_matrixFourier_det_mul hψ hχ S hS⟩

/-- Gauss sums of square matrices over a finite ring `R`. Let `ψ` be primitive and `χ` primitive in
the sense of `New.Exchange.IsPrimitiveMulChar`, and let `n` be the cardinality of `a`. There is a
number `γ` with `|γ|² = #R ^ (n²)` such that every function `S` on `n × n` matrices with
`S (g u) = χ (det g) S u` for all invertible `g` has the Fourier transform `y ↦ γ χ⁻¹(det y) S 1`,
which is zero where `y` is not invertible.

The value of `|γ|²` comes from Fourier inversion
(`New.Exchange.star_matrixFourier_det_mul`), applied to `χ ∘ det`. -/
lemma Exchange.exists_matrixFourier_eq_mul_inv_det (hψ : ψ.IsPrimitive)
    (hχ : IsPrimitiveMulChar χ) :
    ∃ γ : ℂ,
      ‖γ‖ ^ 2 = (Fintype.card R : ℝ) ^ Fintype.card a ^ 2 ∧
      ∀ S : Matrix a a R → ℂ,
        (∀ (g : GL a R) (u : Matrix a a R), S (g.val * u) = χ g.val.det * S u) →
        ∀ y : Matrix a a R, matrixFourier ψ S y = γ * χ⁻¹ y.det * S 1 := by
  -- `γ` is the transform of `χ ∘ det` at `1`; Fourier inversion gives `γ̄ Ŝ(1) = S(1) #Mₙ(R)`.
  let γ : ℂ := matrixFourier ψ (fun u : Matrix a a R ↦ χ u.det) 1
  have h_conj_mul : star γ * γ = Fintype.card (Matrix a a R) := by
    simpa using star_matrixFourier_det_mul hψ hχ (fun u : Matrix a a R ↦ χ u.det) (by simp)
  have h_card : Fintype.card (Matrix a a R) = Fintype.card R ^ Fintype.card a ^ 2 := by
    rw [Fintype.card_congr Matrix.of.symm, Fintype.card_fun, Fintype.card_fun, ← pow_mul, sq]
  have h_norm : ‖γ‖ ^ 2 = card (Matrix a a R) := by simpa [sq] using congrArg norm h_conj_mul
  have h_ne : star γ ≠ 0 := left_ne_zero_of_mul (h_conj_mul.trans_ne (by simp))
  refine ⟨γ, by rw [h_norm, h_card, Nat.cast_pow], fun S hS y ↦ ?_⟩
  obtain ⟨h_formula, h_inversion⟩ :
      (∀ y : Matrix a a R, matrixFourier ψ S y = χ⁻¹ y.det * matrixFourier ψ S 1) ∧
        star γ * matrixFourier ψ S 1 = S 1 * Fintype.card (Matrix a a R) :=
    matrixFourier_eq_and_star_mul_eq hψ hχ S hS
  have h_one : matrixFourier ψ S 1 = γ * S 1 :=
    mul_left_cancel₀ h_ne (by rw [h_inversion, ← mul_assoc, h_conj_mul, mul_comm])
  rw [h_formula y, h_one, mul_left_comm, mul_assoc]

end New
