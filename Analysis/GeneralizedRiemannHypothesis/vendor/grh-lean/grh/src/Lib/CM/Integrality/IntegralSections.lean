import Lib.CM.FormalGroup.IntegralParameter

/-!
# The integrality principle in one variable

* `New.CMLattice.mem_span_monomialSection`: a section with integral torsion values is an integral
  combination of monomials; `New.CMLattice.exists_polynomial_of_even` treats even sections.
* `New.CMLattice.exists_taylorVia_eq_theta_pow_mul`: its Taylor series lies in `θ ^ m 𝒪[[y]]`.

Write the section as `θ ^ m (P₀(x) + y P₁(x))`, where `P₁ = 0` if the section is even, and
interpolate at the nodes `x(tᵢ)`, where `tᵢ = t / 2 ^ i` and `i ≥ 1`. The numbers `θ[tᵢ]`, `x'(tᵢ)`
and `x(tᵢ) - x(tⱼ)` for `i ≠ j` are units.

Notions from other files:

For a lattice `Λ = C.Λ` with a point `t = C.t` of order two modulo `Λ`:
* `θ` is the normalised twisted translate of the sigma function `σ` by `t`; it vanishes on `t + Λ`.
* `x = translatedX` is `℘(z + t) - ℘(t)` and `y = translatedY` is `(℘'(z + t) - a₁ x(z)) / 2`, where
  `a₁ = C.a₁` is a constant of `C` with `‖ιₚ a₁‖ ≤ 1`; off `t + Λ`,
  `x' ^ 2 = x (4 x ^ 2 + a₁ ^ 2 x + 4)`.
* `sections m` is the space of theta functions of degree `m`; the monomial of `(a, b, c)` is
  `θ ^ (a + 2 b + 3 c) x ^ b y ^ c` off `t + Λ`, with degree
  `monomialDeg (a, b, c) = a + 2 b + 3 c`, and `spanningExponents m` is the set of triples with
  `c ≤ 1` and `a + 2 b + 3 c = m`.
* The value `G[u]` is the value at `0` of the translate of `G` by `u`, twisted by the degree `m`
  (written `torsionValue m G u`); it is called a torsion value if `u` is a torsion point, and
  `HasIntegralValues` says that all torsion values have norm at most `1` in `ℂ_p`, under the ring
  homomorphism `ιₚ : ℂ →+* ℂ_[p]` fixed by the instance `PadicPlace p`.

## Relation to the literature

Known result: integral expansions of theta functions of CM elliptic curves, at ordinary primes
`p ≥ 5`. Here `p` is arbitrary, but `d` is a prime congruent to `7` modulo `8`. Source: Bannai and
Kobayashi, Algebraic theta functions and the p-adic interpolation of Eisenstein-Kronecker numbers,
Duke Math. J. 153 (2010), 229-295, after Norman and Mazur–Tate.

Known result: for a lattice with complex multiplication, the value of the Siegel function at a
torsion point is a unit if two different prime ideals divide the annihilator of the point. Only the
points `t / 2 ^ i` are treated, by doubling. Source: Ramachandra and Robert; Kubert and Lang,
*Modular Units*.
-/

open PowerSeries

namespace New

/-- Lagrange interpolation: if the points `x i` are integral and any two have difference of norm
`1`, then a polynomial with integral values at all of them has integral coefficients. -/
lemma norm_coeff_le_one_of_norm_eval_le_one {p : ℕ} [Fact p.Prime] {x : ℕ → ℂ_[p]}
    (hx : ∀ i : ℕ, ‖x i‖ ≤ 1) (h_sub : ∀ i j : ℕ, i ≠ j → ‖x i - x j‖ = 1) {P : Polynomial ℂ_[p]}
    (hP : ∀ i : ℕ, ‖P.eval (x i)‖ ≤ 1) (n : ℕ) : ‖P.coeff n‖ ≤ 1 := by
  -- `S` holds the polynomials with coefficients in `valRingCp p`, that is, of norm at most `1`.
  let S : Subring (Polynomial ℂ_[p]) := Polynomial.liftsRing (valRingCp p).subtype
  have hC {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) : Polynomial.C a ∈ S := ⟨.C ⟨a, ha⟩, Polynomial.map_C _⟩
  have hX : Polynomial.X ∈ S := ⟨Polynomial.X, Polynomial.map_X _⟩
  have h_inj : Function.Injective x := fun i j h ↦
    by_contra fun hij ↦ by simpa [h] using h_sub i j hij
  -- The denominators `x i - x j` in the interpolation formula are units.
  have h_mem : P ∈ S := by
    rw [Lagrange.eq_interpolate (s := Finset.range (P.natDegree + 1)) h_inj.injOn
      (P.degree_le_natDegree.trans_lt (mod_cast by simp))]
    simp only [Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor]
    refine sum_mem fun i _ ↦ mul_mem (hC (hP i)) (prod_mem fun j hj ↦ ?_)
    refine mul_mem (hC ?_) (sub_mem hX (hC (hx j)))
    rw [norm_inv, h_sub i j (Finset.ne_of_mem_erase hj).symm, inv_one]
  obtain ⟨Q, rfl⟩ := h_mem
  rw [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  exact (Q.coeff n).property

namespace CMLattice
variable {d : ℕ} (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p] {f : ℂ → ℂ} {m : ℕ}

/-! ### Sections as polynomials in `x` and `y` -/

/-- The difference `y(z) - y(-z)` is the derivative of `x = translatedX`, where
`y = translatedY`. -/
lemma translatedY_sub_translatedY_neg (z : ℂ) :
    C.translatedY z - C.translatedY (-z) = deriv C.translatedX z := by
  rw [deriv_translatedX, translatedY, translatedY, translatedX_neg,
    show -z + C.t = -(z + C.t) + (⟨C.t + C.t, C.two_t_mem⟩ : C.Λ) by ring,
    PeriodPair.derivWeierstrassP_add_coe, PeriodPair.derivWeierstrassP_neg]
  ring

/-- A section of degree `m` is `θ ^ m (P₀(x) + y P₁(x))` off `t + Λ`, where `x = translatedX`,
`y = translatedY`, and `P₀`, `P₁` are polynomials whose terms `x ^ i`, `y x ^ i` have pole order
at most `m`. -/
lemma exists_eq_theta_pow_mul_eval (hf : f ∈ C.sections m) :
    ∃ P₀ P₁ : Polynomial ℂ, (∀ i : ℕ, P₀.coeff i ≠ 0 → 2 * i ≤ m) ∧
      (∀ i : ℕ, P₁.coeff i ≠ 0 → 2 * i + 3 ≤ m) ∧
      ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m *
        (P₀.eval (C.translatedX z) + C.translatedY z * P₁.eval (C.translatedX z)) := by
  -- It suffices to treat zero, sums, and multiples of one monomial.
  refine Submodule.closure_induction ⟨0, 0, by simp⟩ ?_ ?_ (C.sections_le_span_monomialSection m hf)
  · rintro F G - - ⟨P₀, P₁, hP₀, hP₁, hF⟩ ⟨Q₀, Q₁, hQ₀, hQ₁, hG⟩
    refine ⟨P₀ + Q₀, P₁ + Q₁, by grind [Polynomial.coeff_add], by grind [Polynomial.coeff_add],
      fun z hz ↦ ?_⟩
    rw [Pi.add_apply, hF z hz, hG z hz, Polynomial.eval_add, Polynomial.eval_add]
    ring
  · rintro c _ ⟨⟨j, k, e⟩, h_mem, rfl⟩
    obtain ⟨he, rfl⟩ : e ≤ 1 ∧ monomialDeg (j, k, e) = m := mk_mem_spanningExponents.1 h_mem
    -- The monomial of `(j, k, e)` contributes `c x ^ k` to `P₀` if `e = 0`, and to `P₁` if `e = 1`.
    obtain rfl | rfl : e = 0 ∨ e = 1 := Nat.le_one_iff_eq_zero_or_eq_one.1 he
    · refine ⟨.monomial k c, 0, by grind [Polynomial.coeff_monomial], by simp, fun z hz ↦ ?_⟩
      simp [C.monomialSection_eq _ z hz, mul_left_comm]
    · refine ⟨0, .monomial k c, by simp, by grind [Polynomial.coeff_monomial], fun z hz ↦ ?_⟩
      simp [C.monomialSection_eq _ z hz, mul_comm, mul_assoc]

lemma exists_translatedX_eq (c : ℂ) : ∃ z : ℂ, z + C.t ∉ C.Λ ∧ C.translatedX z = c := by
  let a : ℂ := c + C.weierstrassP C.t
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b ^ 2 = 4 * a ^ 3 - C.g₂ * a - C.g₃ :=
    IsSepClosed.exists_pow_nat_eq _ 2
  obtain ⟨w, hw, hw_eq, -⟩ := C.exists_weierstrassP_eq_of_cubic a b hb
  exact ⟨w - C.t, by simpa using hw, by simp [translatedX, hw_eq, a]⟩

/-- If an even function `f` is `θ ^ m (P₀(x) + y P₁(x))` off `t + Λ`, where `x = translatedX` and
`y = translatedY`, then `P₁ = 0`. -/
lemma eq_zero_of_even_of_eq_theta_pow_mul_eval {P₀ P₁ : Polynomial ℂ} (hf_even : f.Even)
    (h_eq : ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m *
      (P₀.eval (C.translatedX z) + C.translatedY z * P₁.eval (C.translatedX z))) : P₁ = 0 := by
  -- As `θ` and `x` are even, the odd part `x' P₁(x) / 2` of the bracket vanishes.
  have h_odd (z : ℂ) (hz : z + C.t ∉ C.Λ) :
      deriv C.translatedX z * P₁.eval (C.translatedX z) = 0 := by
    have h_neg : f z = C.θ z ^ m * (P₀.eval (C.translatedX z) +
        C.translatedY (-z) * P₁.eval (C.translatedX z)) := by
      simpa only [hf_even z, theta_neg, translatedX_neg] using
        h_eq (-z) (by rwa [← theta_eq_zero_iff, theta_neg, theta_eq_zero_iff])
    refine mul_left_cancel₀ (pow_ne_zero m (mt C.theta_eq_zero_iff.1 hz)) ?_
    rw [← translatedY_sub_translatedY_neg]
    linear_combination h_neg - h_eq z hz
  -- Multiply by `x'`, whose square is `x Q(x)`; as `x` takes every value, `X Q P₁ = 0`.
  let Q : Polynomial ℂ := 4 * .X ^ 2 + .C (C.a₁ ^ 2) * .X + 4
  have hQ (c : ℂ) : Q.eval c = 4 * c ^ 2 + C.a₁ ^ 2 * c + 4 := by simp [Q]
  have hQ_ne : Q ≠ 0 := fun h ↦ by simpa [h] using hQ 0
  have h_prod : Polynomial.X * Q * P₁ = 0 := by
    refine Polynomial.funext fun c ↦ ?_
    obtain ⟨z, hz, rfl⟩ := C.exists_translatedX_eq c
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, hQ, Polynomial.eval_zero,
      ← C.deriv_translatedX_sq hz, sq, mul_assoc, h_odd z hz, mul_zero]
  exact (mul_eq_zero_iff_left (mul_ne_zero Polynomial.X_ne_zero hQ_ne)).1 h_prod

/-- An even section of degree `m` is `θ ^ m P(x)` off `t + Λ`, with `x = translatedX` and
`2 i ≤ m` for every term `x ^ i` of `P`. -/
lemma exists_eq_theta_pow_mul_eval_of_even (hf : f ∈ C.sections m) (hf_even : f.Even) :
    ∃ P : Polynomial ℂ, (∀ i : ℕ, P.coeff i ≠ 0 → 2 * i ≤ m) ∧
      ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m * P.eval (C.translatedX z) := by
  obtain ⟨P₀, P₁, h_deg, -, h_eq⟩ := C.exists_eq_theta_pow_mul_eval hf
  obtain rfl : P₁ = 0 := C.eq_zero_of_even_of_eq_theta_pow_mul_eval hf_even h_eq
  exact ⟨P₀, h_deg, fun z hz ↦ by simpa using h_eq z hz⟩

lemma monomialDeg_sub_sub {i e : ℕ} (h_le : 2 * i + 3 * e ≤ m) :
    monomialDeg (m - 2 * i - 3 * e, i, e) = m := by
  grind

/-- A section that agrees off `t + Λ` with an entire function `g` equals `g`. -/
lemma eq_of_mem_sections_of_eq_off_translate (hf : f ∈ C.sections m) {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (h_eq : ∀ z : ℂ, z + C.t ∉ C.Λ → f z = g z) : f = g :=
  funext (C.eq_of_eq_off_lattice C.t hf.left hg h_eq)

/-- If every exponent `i` of `P` has `2 i + 3 e ≤ m`, then `θ ^ m y ^ e P(x)` is the combination of
the monomials of degree `m` with the coefficients of `P`, off `t + Λ`. Here `x = translatedX`
and `y = translatedY`. -/
lemma theta_pow_mul_eval_eq_sum {P : Polynomial ℂ} {e : ℕ}
    (hP : ∀ i : ℕ, P.coeff i ≠ 0 → 2 * i + 3 * e ≤ m) {z : ℂ} (hz : z + C.t ∉ C.Λ) :
    C.θ z ^ m * (C.translatedY z ^ e * P.eval (C.translatedX z)) =
      ∑ i ∈ P.support, P.coeff i * C.monomialSection (m - 2 * i - 3 * e, i, e) z := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [C.monomialSection_eq _ z hz, monomialDeg_sub_sub (hP i (Polynomial.mem_support_iff.1 hi))]
  ring

/-- If `P` has degree at most `m / 2`, then `θ ^ m P(x)`, with `x = translatedX`, is the
combination of the monomials of `(m - 2 i, i, 0)`, `i ≤ m / 2`, with the coefficients of `P`, off
`t + Λ`. -/
lemma theta_pow_mul_eval_eq_sum_range {P : Polynomial ℂ} (hP : 2 * P.natDegree ≤ m) {z : ℂ}
    (hz : z + C.t ∉ C.Λ) :
    C.θ z ^ m * P.eval (C.translatedX z) =
      ∑ i ∈ Finset.range (m / 2 + 1), P.coeff i * C.monomialSection (m - 2 * i, i, 0) z := by
  rw [Polynomial.eval_eq_sum_range' (n := m / 2 + 1) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [C.monomialSection_eq _ z hz, show monomialDeg (m - 2 * i, i, 0) = m by grind]
  ring

/-- Let `e ≤ 1`, and let `P` have coefficients integral in `ℂ_p` and `2 i + 3 e ≤ m` for each of its
exponents `i`. Then `θ ^ m translatedY ^ e P(translatedX)` agrees off `t + Λ` with an entire
function that is an integral combination of the monomials of the triples `(a, b, c)` with `c ≤ 1`
and degree `a + 2 b + 3 c = m` (the set `spanningExponents m`). -/
lemma exists_mem_span_monomialSection_eq_theta_pow_mul_eval {P : Polynomial ℂ} {e : ℕ} (he : e ≤ 1)
    (h_deg : ∀ i : ℕ, P.coeff i ≠ 0 → 2 * i + 3 * e ≤ m) (h_int : ∀ i : ℕ, ‖ιₚ (P.coeff i)‖ ≤ 1) :
    ∃ g ∈ Submodule.span ((valRingCp p).comap ιₚ) (C.monomialSection '' spanningExponents m),
      Differentiable ℂ g ∧ ∀ z : ℂ, z + C.t ∉ C.Λ →
        g z = C.θ z ^ m * (C.translatedY z ^ e * P.eval (C.translatedX z)) := by
  refine ⟨∑ i ∈ P.support, P.coeff i • C.monomialSection (m - 2 * i - 3 * e, i, e),
    sum_mem fun i hi ↦ ?_, by fun_prop, fun z hz ↦ ?_⟩
  · exact Submodule.smul_mem _ (⟨P.coeff i, h_int i⟩ : (valRingCp p).comap ιₚ)
      (Submodule.subset_span (Set.mem_image_of_mem C.monomialSection (mk_mem_spanningExponents.2
        ⟨he, monomialDeg_sub_sub (h_deg i (Polynomial.mem_support_iff.1 hi))⟩)))
  · simp only [C.theta_pow_mul_eval_eq_sum h_deg hz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- If `f = θ ^ m P(x)` off `t + Λ`, with `x = translatedX`, then the same identity holds for the
Taylor series at `0`, with `ιₚ` applied to the coefficients. -/
lemma taylorVia_eq_of_eq_theta_pow_mul_eval {P : Polynomial ℂ}
    (h_eq : ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m * P.eval (C.translatedX z)) :
    taylorVia ιₚ f = taylorVia ιₚ C.θ ^ m * (P.map ιₚ).aeval (taylorVia ιₚ C.translatedX) := by
  have h_eval : map ιₚ (P.aeval (taylorAtZero C.translatedX)) =
      (P.map ιₚ).aeval (taylorVia ιₚ C.translatedX) :=
    Polynomial.map_aeval_eq_aeval_map (RingHom.ext fun c ↦ (map_C ιₚ c).symm) P _
  simp (disch := fun_prop) only [taylorVia, C.taylorAtZero_congr h_eq, taylorAtZero_mul,
    taylorAtZero_pow, taylorAtZero_eval, map_mul, map_pow, h_eval]

/-! ### Units at the points `t / 2 ^ i`

The lemmas of this part prove the case of the theorem on Siegel units (Ramachandra, Robert) that is
used. The proof follows the pair `w(u) = (ιₚ θ[u] ^ 2, ιₚ σ[u] ^ 2)` of elements of `ℂ_p`, that is
`squarePair u`, under doubling. -/

lemma torsionValue_theta_neg (u : ℂ) : C.torsionValue 1 C.θ (-u) = C.torsionValue 1 C.θ u := by
  rw [torsionValue_eq, torsionValue_eq, theta_neg, norm_neg]

variable {C} in
/-- Let `f` have integral torsion values in degree `m`, and let `u` be a torsion point where
`θ[u]` is a unit. If `f(u) = θ(u) ^ m c`, then `c` is integral. -/
lemma HasIntegralValues.norm_le_one_of_eq_theta_pow_mul (h_int : C.HasIntegralValues m f)
    {u c : ℂ} (hu : C.IsTorsion u) (hθ : ‖ιₚ (C.torsionValue 1 C.θ u)‖ = 1)
    (h_eq : f u = C.θ u ^ m * c) : ‖ιₚ c‖ ≤ 1 := by
  simpa [C.torsionValue_eq_mul_theta_pow h_eq, hθ] using h_int u hu

/-- If `u + t` is not a period, the second coordinate of the pair
`squarePair u = (ιₚ θ[u] ^ 2, ιₚ σ[u] ^ 2)` is `ιₚ (x(u))` times the first, where
`x = translatedX`. -/
lemma squarePair_snd {u : ℂ} (hu : u + C.t ∉ C.Λ) :
    (C.squarePair u).2 = (C.squarePair u).1 * ιₚ (C.translatedX u) := by
  have h_sq : (C.σ ^ 2) u = C.θ u ^ (2 * 1) * C.translatedX u := by
    rw [Pi.pow_apply, C.sigma_sq_eq_translatedX_mul_theta_sq hu, mul_comm]
  simp only [squarePair, ← map_pow, ← map_mul]
  rw [← torsionValue_pow, C.torsionValue_eq_mul_theta_pow h_sq]

/-- The points `tᵢ = t / 2 ^ i`, where `t` is the chosen point of order two modulo the lattice. -/
noncomputable def halvingPoint (i : ℕ) : ℂ := C.t / 2 ^ i

lemma two_pow_mul_halvingPoint (i : ℕ) : 2 ^ i * C.halvingPoint i = C.t :=
  mul_div_cancel₀ C.t (pow_ne_zero i two_ne_zero)

lemma two_mul_halvingPoint_succ (i : ℕ) : 2 * C.halvingPoint (i + 1) = C.halvingPoint i := by
  simp [halvingPoint, pow_succ, field]

lemma two_pow_mul_two_t_mem (i : ℕ) : 2 ^ i * (C.t + C.t) ∈ C.Λ := by
  simpa only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using nsmul_mem C.two_t_mem (2 ^ i)

lemma two_pow_mul_halvingPoint_mem {i j : ℕ} (hij : i < j) : 2 ^ j * C.halvingPoint i ∈ C.Λ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = i + k + 1 := Nat.exists_eq_add_of_lt hij
  have h_eq : 2 ^ (i + k + 1) * C.halvingPoint i = 2 ^ k * (C.t + C.t) := by
    linear_combination 2 ^ (k + 1) * C.two_pow_mul_halvingPoint i
  simpa only [h_eq] using C.two_pow_mul_two_t_mem k

lemma isTorsion_halvingPoint (i : ℕ) : C.IsTorsion (C.halvingPoint i) :=
  ⟨2 ^ (i + 1), by positivity, mod_cast C.two_pow_mul_halvingPoint_mem (lt_add_one i)⟩

variable [PrimeSevenModEight d]

/-- If numbers `a ∈ [0, 1]` and `b ≤ 1` satisfy `a ^ 2 b = 1`, then `a = 1`. -/
lemma eq_one_of_sq_mul_eq_one {a b : ℝ} (ha₀ : 0 ≤ a) (ha : a ≤ 1) (hb : b ≤ 1)
    (h_eq : a ^ 2 * b = 1) : a = 1 := by
  nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg a)]

/-- If `2 ^ j v` is a period and `tⱼ = t / 2 ^ j`, then the pairs `w(tⱼ)` and `w(v)`, where
`w = squarePair`, reduce to distinct points of the projective line (their determinant is a unit):
doubling `j` times takes the first to `(0 : 1)` and the second to `(1 : 0)`. -/
lemma norm_det_squarePair_halvingPoint {j : ℕ} {v : ℂ} (hv : 2 ^ j * v ∈ C.Λ) :
    ‖(C.squarePair (C.halvingPoint j)).1 * (C.squarePair v).2 -
      (C.squarePair (C.halvingPoint j)).2 * (C.squarePair v).1‖ = 1 := by
  have h_norm : ‖(doublingForms (ιₚ C.a₁))^[j] (C.squarePair (C.halvingPoint j))‖ = 1 := by
    rw [← squarePair_two_pow_mul, norm_squarePair_two_pow_mul,
      C.norm_squarePair (C.isTorsion_halvingPoint j), one_pow]
  have h_fst : ((doublingForms (ιₚ C.a₁))^[j] (C.squarePair (C.halvingPoint j))).1 = 0 := by
    rw [← squarePair_two_pow_mul, two_pow_mul_halvingPoint, squarePair_fst_eq_zero_iff]
    exact C.two_t_mem
  have h_snd : ((doublingForms (ιₚ C.a₁))^[j] (C.squarePair v)).2 = 0 := by
    rwa [← squarePair_two_pow_mul, squarePair_snd_eq_zero_iff]
  exact norm_det_eq_one_of_iterate_doublingForms C.norm_a₁_le_one
    (C.norm_squarePair (C.isTorsion_halvingPoint j))
    (C.norm_squarePair ⟨2 ^ j, by positivity, mod_cast hv⟩) h_norm h_fst h_snd

/-- With `tᵢ = t / 2 ^ i` the torsion value `θ[tᵢ₊₁]` is a unit, as `w(tᵢ₊₁)`, where
`w = squarePair`, does not reduce to `w(t₀) = (0 : 1)`.

This is a local analogue of the unit property of Siegel units (Ramachandra, Robert), only for `θ` at
the points `t / 2 ^ (i + 1)`, at the chosen place above `p`, with `d` prime `≡ 7 mod 8`. -/
lemma norm_torsionValue_theta_halvingPoint (i : ℕ) :
    ‖ιₚ (C.torsionValue 1 C.θ (C.halvingPoint (i + 1)))‖ = 1 := by
  have h_zero : (C.squarePair (C.halvingPoint 0)).1 = 0 :=
    C.squarePair_fst_eq_zero_iff.2 (by simpa [halvingPoint] using C.two_t_mem)
  have h_det : ‖(C.squarePair (C.halvingPoint (i + 1))).1‖ *
      ‖(C.squarePair (C.halvingPoint 0)).2‖ = 1 := by
    simpa [h_zero] using
      C.norm_det_squarePair_halvingPoint (C.two_pow_mul_halvingPoint_mem (Nat.succ_pos i))
  have h_le : ‖ιₚ (C.torsionValue 1 C.θ (C.halvingPoint (i + 1)))‖ ≤ 1 :=
    C.hasIntegralValues_theta _ (C.isTorsion_halvingPoint _)
  have h_snd : ‖(C.squarePair (C.halvingPoint 0)).2‖ ≤ 1 :=
    (norm_snd_le _).trans (C.norm_squarePair (C.isTorsion_halvingPoint 0)).le
  rw [show ‖(C.squarePair (C.halvingPoint (i + 1))).1‖ =
    ‖ιₚ (C.torsionValue 1 C.θ (C.halvingPoint (i + 1)))‖ ^ 2 from norm_pow _ _] at h_det
  exact eq_one_of_sq_mul_eq_one (norm_nonneg _) h_le h_snd h_det

/-- Let `C` be a CM lattice (`d` a prime `≡ 7 mod 8`) with point `t` of order two, let
`tᵢ = t / 2 ^ i`, and let `ιₚ : ℂ → ℂ_p` be the chosen `p`-adic place. The torsion value `σ[tᵢ]`
(value at 0 of the degree-1 twisted translate of `C.σ` by `tᵢ`) has norm 1, as `w(tᵢ)`, where
`w = squarePair`, does not reduce to `w(2 t) = (1 : 0)`.

This is a local form of the unit property of Siegel units (Ramachandra, Robert), only at the points
`t / 2 ^ i` of these CM lattices and at the chosen place above `p`. -/
lemma norm_torsionValue_sigma_halvingPoint (i : ℕ) :
    ‖ιₚ (C.torsionValue 1 C.σ (C.halvingPoint i))‖ = 1 := by
  have h_zero : (C.squarePair (C.t + C.t)).2 = 0 := C.squarePair_snd_eq_zero_iff.2 C.two_t_mem
  have h_det : ‖(C.squarePair (C.halvingPoint i)).2‖ * ‖(C.squarePair (C.t + C.t)).1‖ = 1 := by
    simpa [h_zero] using C.norm_det_squarePair_halvingPoint (C.two_pow_mul_two_t_mem i)
  have h_le : ‖ιₚ (C.torsionValue 1 C.σ (C.halvingPoint i))‖ ≤ 1 :=
    C.hasIntegralValues_sigma _ (C.isTorsion_halvingPoint _)
  have h_fst : ‖(C.squarePair (C.t + C.t)).1‖ ≤ 1 :=
    (norm_fst_le _).trans (C.norm_squarePair (.of_mem C.two_t_mem)).le
  rw [show ‖(C.squarePair (C.halvingPoint i)).2‖ =
    ‖ιₚ (C.torsionValue 1 C.σ (C.halvingPoint i))‖ ^ 2 from norm_pow _ _] at h_det
  exact eq_one_of_sq_mul_eq_one (norm_nonneg _) h_le h_fst h_det

omit [PrimeSevenModEight d] in
/-- A point `u` with `‖θ[u]‖ = 1` does not lie in `t + Λ = -t + Λ`, the zero set of `θ`. -/
lemma add_t_notMem_of_norm_eq_one {u : ℂ} (hθ : ‖ιₚ (C.torsionValue 1 C.θ u)‖ = 1) :
    u + C.t ∉ C.Λ :=
  fun h ↦ by simp [torsionValue_eq, C.theta_eq_zero_iff.2 h] at hθ

/-- At a torsion point `u` where `θ[u]` is a unit, `x(u) = translatedX u` is integral in `ℂ_p`. -/
lemma norm_translatedX_le_one {u : ℂ} (hu : C.IsTorsion u)
    (hθ : ‖ιₚ (C.torsionValue 1 C.θ u)‖ = 1) : ‖ιₚ (C.translatedX u)‖ ≤ 1 := by
  refine (C.hasIntegralValues_sigma.pow 2).norm_le_one_of_eq_theta_pow_mul hu hθ ?_
  rw [Pi.pow_apply, C.sigma_sq_eq_translatedX_mul_theta_sq (C.add_t_notMem_of_norm_eq_one hθ),
    mul_comm]

/-- At a torsion point `u` where `θ[u]` is a unit, `y(u) = translatedY u` is integral in `ℂ_p`. -/
lemma norm_translatedY_le_one {u : ℂ} (hu : C.IsTorsion u)
    (hθ : ‖ιₚ (C.torsionValue 1 C.θ u)‖ = 1) : ‖ιₚ (C.translatedY u)‖ ≤ 1 := by
  refine C.hasIntegralValues_translatedYThetaCube.norm_le_one_of_eq_theta_pow_mul hu hθ ?_
  rw [C.translatedYThetaCube_eq_translatedY_mul_theta_cube (C.add_t_notMem_of_norm_eq_one hθ),
    mul_comm]

/-- The numbers `x(tᵢ₊₁)`, where `x = translatedX` and `tᵢ = t / 2 ^ i`, are distinct modulo the
maximal ideal of the integers of `ℂ_p`. -/
lemma norm_translatedX_halvingPoint_sub {i j : ℕ} (hij : i ≠ j) :
    ‖ιₚ (C.translatedX (C.halvingPoint (i + 1))) -
      ιₚ (C.translatedX (C.halvingPoint (j + 1)))‖ = 1 := by
  wlog h_lt : i < j generalizing i j with h_symm
  · simpa [norm_sub_rev] using h_symm hij.symm (hij.lt_or_gt.resolve_left h_lt)
  let w (k : ℕ) : ℂ_[p] × ℂ_[p] := C.squarePair (C.halvingPoint (k + 1))
  let x (k : ℕ) : ℂ_[p] := ιₚ (C.translatedX (C.halvingPoint (k + 1)))
  have h_fst (k : ℕ) : ‖(w k).1‖ = 1 := by
    simp only [w, squarePair, norm_pow, norm_torsionValue_theta_halvingPoint, one_pow]
  have h_snd (k : ℕ) : (w k).2 = (w k).1 * x k :=
    C.squarePair_snd (C.add_t_notMem_of_norm_eq_one (C.norm_torsionValue_theta_halvingPoint k))
  calc ‖x i - x j‖ = ‖(w j).1 * (w i).1 * (x i - x j)‖ := by simp [h_fst]
    _ = ‖(w j).1 * (w i).2 - (w j).2 * (w i).1‖ := by
      rw [h_snd, h_snd, mul_sub, mul_assoc, mul_right_comm, mul_right_comm (w j).1 (x j)]
    _ = 1 :=
      C.norm_det_squarePair_halvingPoint (C.two_pow_mul_halvingPoint_mem (Nat.succ_lt_succ h_lt))

/-- For `tᵢ = t / 2 ^ i` the number `x'(tᵢ₊₁) = σ[tᵢ] / θ[tᵢ₊₁] ^ 4` is a unit, where
`x = translatedX`. -/
lemma norm_deriv_translatedX_halvingPoint (i : ℕ) :
    ‖ιₚ (deriv C.translatedX (C.halvingPoint (i + 1)))‖ = 1 := by
  have hθ : ‖ιₚ (C.torsionValue 1 C.θ (C.halvingPoint (i + 1)))‖ = 1 :=
    C.norm_torsionValue_theta_halvingPoint i
  have h_double : C.torsionValue 1 C.σ (C.halvingPoint i) =
      C.torsionValue 1 C.θ (C.halvingPoint (i + 1)) ^ 4 *
        deriv C.translatedX (C.halvingPoint (i + 1)) := by
    rw [← two_mul_halvingPoint_succ, torsionValue_two_mul]
    refine C.torsionValue_eq_mul_theta_pow ?_
    rw [C.sigma_two_mul_eq (C.add_t_notMem_of_norm_eq_one hθ), mul_comm]
  simpa [h_double, hθ] using C.norm_torsionValue_sigma_halvingPoint i

/-! ### Interpolation and the integrality principle -/

/-- A polynomial whose values at the nodes `translatedX (t / 2 ^ (i + 1))` are integral in `ℂ_p`
has integral coefficients. -/
lemma norm_coeff_le_one_of_norm_eval_halvingPoint_le_one {P : Polynomial ℂ}
    (hP : ∀ i : ℕ, ‖ιₚ (P.eval (C.translatedX (C.halvingPoint (i + 1))))‖ ≤ 1) (n : ℕ) :
    ‖ιₚ (P.coeff n)‖ ≤ 1 := by
  simpa using norm_coeff_le_one_of_norm_eval_le_one (P := P.map ιₚ)
    (fun i ↦ C.norm_translatedX_le_one (C.isTorsion_halvingPoint (i + 1))
      (C.norm_torsionValue_theta_halvingPoint i))
    (fun i j ↦ C.norm_translatedX_halvingPoint_sub) (by simpa using hP) n

/-- Let `C` be a CM lattice for a prime `d ≡ 7 mod 8`, with point `t` of order two, and let
`ιₚ : ℂ → ℂ_p` be a `p`-adic place. Suppose `f z = θ z ^ m (P₀(x z) + y z · P₁(x z))` whenever
`z + t ∉ Λ`, where `x = translatedX` is `℘(z + t) - ℘(t)` and `y = translatedY` is
`½(℘'(z + t) - a₁ x(z))`. Suppose also that `f` has integral torsion values in degree `m`, meaning
every torsion value `f[u]` has `‖ιₚ f[u]‖ ≤ 1`. Then every coefficient of `P₀` and `P₁` has image
under `ιₚ` of norm at most `1`. -/
lemma norm_coeff_le_one_of_hasIntegralValues {P₀ P₁ : Polynomial ℂ}
    (h_eq : ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m *
      (P₀.eval (C.translatedX z) + C.translatedY z * P₁.eval (C.translatedX z)))
    (h_int : C.HasIntegralValues m f) :
    (∀ n : ℕ, ‖ιₚ (P₀.coeff n)‖ ≤ 1) ∧ ∀ n : ℕ, ‖ιₚ (P₁.coeff n)‖ ≤ 1 := by
  -- Bound the values of `P₁` and then of `P₀` at the points `x(v i)`, and interpolate.
  -- Membership in `valRingCp p` is by definition having norm at most `1`.
  let v (i : ℕ) : ℂ := C.halvingPoint (i + 1)
  let F (u : ℂ) : ℂ := P₀.eval (C.translatedX u) + C.translatedY u * P₁.eval (C.translatedX u)
  have hθ (i : ℕ) : ‖ιₚ (C.torsionValue 1 C.θ (v i))‖ = 1 :=
    C.norm_torsionValue_theta_halvingPoint i
  have hv (i : ℕ) : C.IsTorsion (v i) := C.isTorsion_halvingPoint (i + 1)
  have hF {u : ℂ} (hu : C.IsTorsion u) (hθu : ‖ιₚ (C.torsionValue 1 C.θ u)‖ = 1) :
      ιₚ (F u) ∈ valRingCp p :=
    h_int.norm_le_one_of_eq_theta_pow_mul hu hθu (h_eq u (C.add_t_notMem_of_norm_eq_one hθu))
  have h₁ (i : ℕ) : ‖ιₚ (P₁.eval (C.translatedX (v i)))‖ ≤ 1 := by
    have h_diff : deriv C.translatedX (v i) * P₁.eval (C.translatedX (v i)) =
        F (v i) - F (-v i) := by
      simp only [F, ← translatedY_sub_translatedY_neg, translatedX_neg]
      ring
    have h_le : ‖ιₚ (deriv C.translatedX (v i) * P₁.eval (C.translatedX (v i)))‖ ≤ 1 := by
      rw [h_diff, map_sub]
      exact sub_mem (hF (hv i) (hθ i)) (hF (hv i).neg (by rw [torsionValue_theta_neg, hθ]))
    rwa [map_mul, norm_mul, norm_deriv_translatedX_halvingPoint, one_mul] at h_le
  have h₀ (i : ℕ) : ‖ιₚ (P₀.eval (C.translatedX (v i)))‖ ≤ 1 := by
    have h_sum : ιₚ (P₀.eval (C.translatedX (v i))) + ιₚ (C.translatedY (v i)) *
        ιₚ (P₁.eval (C.translatedX (v i))) ∈ valRingCp p := by
      simpa only [F, map_add, map_mul] using hF (hv i) (hθ i)
    exact (add_mem_cancel_right
      (mul_mem (C.norm_translatedY_le_one (hv i) (hθ i)) (h₁ i))).1 h_sum
  exact ⟨C.norm_coeff_le_one_of_norm_eval_halvingPoint_le_one h₀,
    C.norm_coeff_le_one_of_norm_eval_halvingPoint_le_one h₁⟩

/-- Let `d` be a prime `≡ 7 (mod 8)` and fix a `p`-adic place `ιₚ`. Let `f` be a section of degree
`m` (a theta function for `Λ` of degree `m`) with integral torsion values: for every torsion point
`u`, the value `f[u]` satisfies `‖ιₚ f[u]‖ ≤ 1`. Then `f` is a combination, with coefficients
integral in `ℂ_p`, of the monomials of the triples `(a, b, c)` with `c ≤ 1` and degree
`a + 2 b + 3 c = m` (the set `spanningExponents m`); off `t + Λ` these monomials are
`θ ^ m translatedX ^ b translatedY ^ c`. The scalars are the complex numbers whose image under `ιₚ`
lies in the valuation ring `valRingCp p`. -/
lemma mem_span_monomialSection {f : ℂ → ℂ} {m : ℕ} (hf : f ∈ C.sections m)
    (h_int : C.HasIntegralValues m f) :
    f ∈ Submodule.span ((valRingCp p).comap ιₚ) (C.monomialSection '' spanningExponents m) := by
  obtain ⟨P₀, P₁, h_deg₀, h_deg₁, h_eq⟩ := C.exists_eq_theta_pow_mul_eval hf
  obtain ⟨h_int₀, h_int₁⟩ := C.norm_coeff_le_one_of_hasIntegralValues h_eq h_int
  -- The summands `θ ^ m P₀(x)` and `θ ^ m y P₁(x)` extend to entire `g₀` and `g₁` in the span.
  obtain ⟨g₀, hg₀_mem, hg₀_diff, hg₀⟩ :=
    C.exists_mem_span_monomialSection_eq_theta_pow_mul_eval zero_le_one h_deg₀ h_int₀
  obtain ⟨g₁, hg₁_mem, hg₁_diff, hg₁⟩ :=
    C.exists_mem_span_monomialSection_eq_theta_pow_mul_eval le_rfl h_deg₁ h_int₁
  have h_off (z : ℂ) (hz : z + C.t ∉ C.Λ) : f z = (g₀ + g₁) z := by
    rw [Pi.add_apply, h_eq z hz, hg₀ z hz, hg₁ z hz]
    ring
  rw [C.eq_of_mem_sections_of_eq_off_translate hf (hg₀_diff.add hg₁_diff) h_off]
  exact add_mem hg₀_mem hg₁_mem

/-- The polynomial `R` is an integral expansion of `f` in degree `m` in the monomials
`θ ^ (m - 2 i) σ ^ (2 i)`, which are `θ ^ m x ^ i` off `t + Λ`, where `x = translatedX`. -/
structure IsIntegralEvenExpansion (m : ℕ) (f : ℂ → ℂ) (R : Polynomial ℂ) : Prop where
  /-- The coefficients of `R` are integral in `ℂ_p`. -/
  norm_coeff_le_one : ∀ i : ℕ, ‖ιₚ (R.coeff i)‖ ≤ 1
  /-- The degree of `R` is at most `m / 2`. -/
  two_mul_natDegree_le : 2 * R.natDegree ≤ m
  /-- The function `f` is `∑ Rᵢ θ ^ (m - 2 i) σ ^ (2 i)`, the sum being over `i ≤ m / 2`. -/
  eq_sum : ∀ z : ℂ, f z = ∑ i ∈ Finset.range (m / 2 + 1),
    R.coeff i * C.monomialSection (m - 2 * i, i, 0) z
  /-- The Taylor series of `f` at `0`, with `ιₚ` applied to the coefficients, is `θ ^ m R(x)`. -/
  taylorVia_eq :
    taylorVia ιₚ f = taylorVia ιₚ C.θ ^ m * (R.map ιₚ).aeval (taylorVia ιₚ C.translatedX)

/-- Let `C` be a CM lattice for a prime `d ≡ 7 mod 8`, with point `t` of order two, and let `ιₚ` be
a `p`-adic place. Let `f` be an even section of degree `m` (a theta function for `Λ` with hermitian
form `m H` and multiplier `χ ^ m`) whose torsion values all have `ιₚ`-norm at most `1`. Then
`f = ∑ Rᵢ θ ^ (m - 2 i) σ ^ (2 i)` for a polynomial `R` with `ιₚ`-integral coefficients and degree
at most `m / 2`, and the Taylor series of `f` at `0` is that of `θ ^ m R(x)`, where
`x(z) = ℘(z + t) - ℘(t)` is `translatedX`; these are the clauses of `IsIntegralEvenExpansion`. -/
lemma exists_polynomial_of_even {f : ℂ → ℂ} {m : ℕ} (hf : f ∈ C.sections m)
    (h_int : C.HasIntegralValues m f) (hf_even : f.Even) :
    ∃ R : Polynomial ℂ, C.IsIntegralEvenExpansion m f R := by
  obtain ⟨R, h_deg, h_eq⟩ : ∃ R : Polynomial ℂ, (∀ i : ℕ, R.coeff i ≠ 0 → 2 * i ≤ m) ∧
      ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m * R.eval (C.translatedX z) :=
    C.exists_eq_theta_pow_mul_eval_of_even hf hf_even
  -- This is the form `θ ^ m (P₀(x) + y P₁(x))` with `P₀ = R` and `P₁ = 0`.
  have hR_int : ∀ i : ℕ, ‖ιₚ (R.coeff i)‖ ≤ 1 :=
    (C.norm_coeff_le_one_of_hasIntegralValues (P₁ := 0) (by simpa using h_eq) h_int).left
  have h_natDegree : 2 * R.natDegree ≤ m := by
    rcases eq_or_ne R 0 with rfl | hR
    · simp
    · exact h_deg R.natDegree (Polynomial.leadingCoeff_ne_zero.2 hR)
  have h_off (z : ℂ) (hz : z + C.t ∉ C.Λ) : f z = ∑ i ∈ Finset.range (m / 2 + 1),
      R.coeff i * C.monomialSection (m - 2 * i, i, 0) z :=
    (h_eq z hz).trans (C.theta_pow_mul_eval_eq_sum_range h_natDegree hz)
  exact ⟨R, hR_int, h_natDegree,
    congrFun (C.eq_of_mem_sections_of_eq_off_translate hf (by fun_prop) h_off),
    C.taylorVia_eq_of_eq_theta_pow_mul_eval h_eq⟩

/-- Let `f` be a combination, with coefficients integral in `ℂ_p`, of monomials of degree `m`.
Then `f` is analytic at `0` and its Taylor series lies in `θ ^ m 𝒪[[y]]`, where
`𝒪[[y]] = integralSeriesRing` is the ring of integral power series in the Taylor series of
`y = translatedY`. -/
lemma exists_taylorVia_eq_theta_pow_mul_of_mem_span {s : Set (ℕ × ℕ × ℕ)}
    (h_deg : ∀ x ∈ s, monomialDeg x = m)
    (hf : f ∈ Submodule.span ((valRingCp p).comap ιₚ) (C.monomialSection '' s)) :
    AnalyticAt ℂ f 0 ∧ ∃ u ∈ C.integralSeriesRing, taylorVia ιₚ f = taylorVia ιₚ C.θ ^ m * u := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    -- A monomial is `θ ^ m x ^ b y ^ c`, and `x = translatedX` and `y` lie in `𝒪[[y]]`.
    obtain ⟨⟨a, b, c⟩, h_mem, rfl⟩ := hg
    have h_coord : taylorVia ιₚ C.translatedX ^ b * taylorVia ιₚ C.translatedY ^ c ∈
        C.integralSeriesRing :=
      mul_mem (pow_mem C.taylorVia_translatedX_mem_integralSeriesRing b)
        (pow_mem C.isSeriesGenerator_translatedY.generator_mem c)
    refine ⟨by fun_prop, _, h_coord, ?_⟩
    simp [← h_deg _ h_mem, taylorVia, taylorAtZero_monomialSection_eq]
  | zero => exact ⟨analyticAt_const, 0, zero_mem _, by simp [Pi.zero_def]⟩
  | add g₁ g₂ _ _ h₁ h₂ =>
    obtain ⟨hg₁, u₁, hu₁, h_eq₁⟩ := h₁
    obtain ⟨hg₂, u₂, hu₂, h_eq₂⟩ := h₂
    refine ⟨hg₁.add hg₂, u₁ + u₂, add_mem hu₁ hu₂, ?_⟩
    rw [mul_add, ← h_eq₁, ← h_eq₂, Pi.add_def, taylorVia, taylorAtZero_add hg₁ hg₂, map_add]
  | smul a g _ h =>
    obtain ⟨hg, u, hu, h_eq⟩ := h
    refine ⟨analyticAt_const.mul hg, ιₚ (a : ℂ) • u,
      C.isSeriesGenerator_translatedY.smul_mem a.property hu, ?_⟩
    rw [show a • g = fun z : ℂ ↦ (a : ℂ) * g z from rfl, mul_smul_comm, ← h_eq, taylorVia,
      taylorAtZero_mul analyticAt_const hg, taylorAtZero_const, map_mul, map_C, smul_eq_C_mul]

/-- Let `d` be a prime congruent to 7 mod 8. Let `f` be a section of degree `m` (a theta function
for `Λ` with hermitian form `m H` and multiplier `χ ^ m`) whose torsion values `f[u]` at all torsion
points `u` satisfy `‖ιₚ f[u]‖ ≤ 1`. Then the Taylor series of `f` at `0`, with `ιₚ` applied to its
coefficients, is the `m`-th power of that of the degree-one theta function `θ` times an element of
`integralSeriesRing`, the ring `𝒪[[y]]` of integral power series in the series of
`y(z) = ½(℘′(z + t) − a₁ x(z))` (`translatedY`), where `x(z) = ℘(z + t) − ℘(t)` and `t` is the
chosen point of order two. -/
lemma exists_taylorVia_eq_theta_pow_mul (hf : f ∈ C.sections m) (h_int : C.HasIntegralValues m f) :
    ∃ u ∈ C.integralSeriesRing, taylorVia ιₚ f = taylorVia ιₚ C.θ ^ m * u :=
  (C.exists_taylorVia_eq_theta_pow_mul_of_mem_span
    (fun ⟨_, _, _⟩ hx ↦ (mk_mem_spanningExponents.1 hx).right)
    (C.mem_span_monomialSection hf h_int)).right

end CMLattice

end New
