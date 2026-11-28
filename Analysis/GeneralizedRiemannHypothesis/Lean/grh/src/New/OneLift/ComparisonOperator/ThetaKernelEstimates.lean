import Lib.DiscreteSeries.Holomorphic.ModelFunction
import Lib.DiscreteSeries.Holomorphic.PeaksAwayFromCusp
import New.OneLift.ComparisonOperator.ExchangeData

/-!
# Decay of Fock matrix coefficients, sparse theta sums and the isolation estimate

This file holds the estimates behind the theorem that products span. The Heisenberg matrix
coefficients of a homogeneous Fock vector decay faster than any power. So in a theta sum over a
sparse lattice the term of `0` dominates, and a mean over additive characters produces such a sum.
Bounds for integrals of matrix coefficients of holomorphic discrete series then give the isolation
estimate `New.Data.norm_apply_one_le_of_forall_isPeak`, the last step of the proof: the mean over a
circle of peaks.

## Main definitions and results

* `New.Fock.norm_fockInner_realHeisenbergOp_le`: the decay of the coefficient `⟨v, ϱ(y) ω(σ) v⟩` in
  `y`.
* `New.Rows.firstMinimum_mul_le_hom`: the first minimum of `Hom (S, T)` is bounded below by the
  product of the first minima of `S` and `T`, up to an explicit constant.
* `New.Rows.exists_norm_modKernel_sub_fockInner_le`: for a suitable finite datum `Ψ` modulo `𝔪`, the
  theta kernel at real translates of `(g, h)` differs from a Fock matrix coefficient by a small
  error if the lattice of `Hom (S, T)` has no short vectors.
* `New.Data.integral_norm_holMinorsPi_mul_pow_le`: the integral of the basic function of a weight
  with a large gap against a power of the norm, compared with a squared `L²` norm.
* `New.Data.norm_apply_one_le_of_forall_isPeak`: let a bounded function `K₀` be close, for every
  peak of a holomorphic `F`, to a holomorphic `K` whose weighted integral against the translate of
  `F` vanishes. Then `K₀ 1` is small.

Notions from other files:
* `New.Fock.fockSpace`: The Fock space: integrable functions c on ℂ^ι with c(x) = ∫ c(y)β(y,x)e(x−y)
  dy, β the Heisenberg bicharacter, e the Gaussian exp(−|x|²/2), under the L¹ norm.
* `New.Fock.fockInner`: The bounded sesquilinear form on the Fock space, conjugate-linear in the
  first variable, (c, c′) ↦ ∫ c̄ c′.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.GInf`: The archimedean unitary group G_∞ for signs s: one copy of the complex unitary group
  U(diag s) for each infinite place of E.
* `New.IsPosFirstOrder`: The order o has distinct values and puts every index of sign +1 before
  every index of sign −1.
* `New.Space.vecAtPoint`: the adelic vector x⁻¹y of a rational vector y at the point x of a space;
  the lattice `New.Space.baseLattice` consists of the y for which it has integral finite part.
* `New.realCoord`: the Fock coordinates of an adelic vector: its components at the infinite places
  τ, times √(2π Im τ(j)), with j the element fixed by the Weil data.

## Relation to the literature

See `New.OneLift.ComparisonOperator.ProductsSpan` for related work. See
`Lib.Weil.DualPair.ThetaLiftConvergence` and `Lib.Adelic.Reduction.FiniteVolume` for sources.
-/

/-!
## Decay of Heisenberg matrix coefficients of homogeneous Fock vectors

One estimate, `New.Fock.norm_fockInner_realHeisenbergOp_le`: for a homogeneous polynomial P and v =
v_P in the Fock space, the coefficient ⟨v, ϱ(y)ω(σ)v⟩ decays faster than any power of |y|, with
explicit constants and polynomial growth in ‖σ‖. Here ϱ = `New.Fock.realHeisenbergOp` is the
Heisenberg action, ω = `New.Fock.realWeil` the Weil representation of U(ε), and v_P =
`New.Fock.polyVector` ε P.
-/

section FockCoeffDecay

open MeasureTheory Real Fintype MvPolynomial Matrix.Norms.L2Operator New.Heisenberg IsVacuum Rep
  WithLp

/-- For `σ` in `U(ε)` and vectors `x`, `y`, the points `x` and `σ x + y` cannot both be
small: `|y|² ≤ 2 ‖σ‖² (|x|² + |σ x + y|²)`, with Euclidean norms and the ℓ² operator norm. -/
lemma New.Fock.norm_sq_le_norm_sq_add_norm_mulVec_add_sq {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {ε : ι → ℤˣ} (σ : USign (n := ι) ε) (x y : ι → ℂ) :
    ‖toLp 2 y‖ ^ 2 ≤ 2 * ‖(σ : Matrix ι ι ℂ)‖ ^ 2 *
      (‖toLp 2 x‖ ^ 2 + ‖toLp 2 ((σ : Matrix ι ι ℂ).mulVec x) + toLp 2 y‖ ^ 2) := by
  set M : Matrix ι ι ℂ := ↑σ
  have Mx_le : ‖toLp 2 (M.mulVec x)‖ ≤ ‖M‖ * ‖toLp 2 x‖ := M.l2_opNorm_mulVec (toLp 2 x)
  calc ‖toLp 2 y‖ ^ 2 ≤ (‖M‖ * ‖toLp 2 (M.mulVec x) + toLp 2 y‖ + ‖M‖ * ‖toLp 2 x‖) ^ 2 := by
        grw [norm_le_add_norm_add' (toLp 2 (M.mulVec x)), ← Mx_le, ← U.one_le_norm σ, one_mul]
    _ ≤ 2 * ((‖M‖ * ‖toLp 2 (M.mulVec x) + toLp 2 y‖) ^ 2 + (‖M‖ * ‖toLp 2 x‖) ^ 2) := add_sq_le
    _ = _ := by ring

/-- Let ι be nonempty, P a complex polynomial with P(cx) = c^d P(x) for real c, v = v_P its Fock
vector (`polyVector`), σ in U(ε), and y ≠ 0 in ℂ^ι. For natural numbers A ≥ d + |ι| and n,
|⟨v, ϱ(y)ω(σ)v⟩| ≤ (4(A + n))^n |y|^{−2n} ‖σ‖^{|ι| + 2n} ⟨v, v⟩.
Here ϱ = `realHeisenbergOp` is the Heisenberg action on the Fock space and ω = `realWeil` the Weil
representation of U(ε), |y| = `‖toLp 2 y‖` is the Euclidean norm, ‖σ‖ the ℓ² operator norm of the
matrix of σ, and ⟨v, v⟩ is real. -/
theorem New.Fock.norm_fockInner_realHeisenbergOp_le {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    {ε : ι → ℤˣ} {P : MvPolynomial ι ℂ} {v : fockSpace ε} {y : ι → ℂ} (σ : USign (n := ι) ε)
    (hv : v = polyVector ε P) {d A n : ℕ}
    (hP : ∀ (c : ℝ) (x : ι → ℂ), eval (c • x) P = c ^ d * eval x P) (hA : d + card ι ≤ A)
    (hy : 0 < ‖toLp 2 y‖) :
    ‖fockInner v (realHeisenbergOp y (realWeil σ v))‖ ≤
      ‖(σ : Matrix ι ι ℂ)‖ ^ (card ι + 2 * n) * (fockInner v v).re * (4 * (A + n)) ^ n *
        ‖toLp 2 y‖⁻¹ ^ (2 * n) := by
  -- The coefficient is at most `‖σ‖^|ι| ∫ ‖v x‖ ‖v (σ x + y)‖ dx`. Dilating by `c = √(n/A + 1)`
  -- takes a Gaussian factor out of `v`, which is small at `x` or at `σ x + y`; the rest is bounded
  -- by `2ab ≤ a² + b²`, which does the work of the Cauchy–Schwarz inequality as `a²` and `b²` have
  -- the same integral. The dilation costs the factor `c^(2(d + |ι|)) ≤ eⁿ`.
  have A_ne : A ≠ 0 := by linarith [card_pos (α := ι)]
  let c : ℝ := √(n / A + 1)
  let v_scaled : fockSpace ε := (c : ℂ) ^ d • v
  let G (x : ι → ℂ) : ℝ := ‖v_scaled (c⁻¹ • x)‖ ^ 2
  let K : ℝ := (4 * (A + n) * ((‖(σ : Matrix ι ι ℂ)‖ / ‖toLp 2 y‖) ^ 2 / exp 1)) ^ n
  -- Homogeneity of `P`, and `1 - c⁻² = n / (n + A)`.
  have norm_v (x : ι → ℂ) :
      ‖v x‖ = ‖v_scaled (c⁻¹ • x)‖ / exp (‖toLp 2 x‖ ^ 2 / (n + A) / 2) ^ n := by
    simp (disch := positivity) [v_scaled, *, realVac, star_dotProduct_self_eq_norm_sq, sq, c,
      ← exp_nat_mul, mul_assoc, ← exp_add, field, star_trivial, Complex.norm_exp]
  have G_int : Integrable G (normalizedVolume ι) :=
    (integrable_norm_sq v_scaled).comp_smul (by positivity)
  have preserving : MeasurePreserving (σ • · + y) (normalizedVolume ι) (normalizedVolume ι) :=
    ((realAction ε).2 σ).add_right _ y
  -- Undoing the dilation gives `c^(2d)` from `v_scaled` and the Jacobian `c^(2|ι|)`.
  have G_le : ∫ x, G x ∂normalizedVolume ι ≤ exp n * ∫ x, ‖v x‖ ^ 2 ∂normalizedVolume ι := by
    have exponent_le : ((card ι + d : ℕ) : ℝ) * (n / A) ≤ n := by
      grw [add_comm, hA]
      simp [field]
    have c_pow : (c ^ 2) ^ (card ι + d) ≤ exp n := by
      grw [sq_sqrt (by positivity), add_one_le_exp, ← exp_nat_mul, exponent_le]
    calc _ = (c ^ 2) ^ card ι * ((c ^ 2) ^ d * ∫ x, ‖v x‖ ^ 2 ∂normalizedVolume ι) := by
          -- ↓ changes variables before simp rewrites inside the integral.
          simp [G, ↓(normalizedVolume ι).integral_comp_inv_smul (‖v_scaled ·‖ ^ 2), v_scaled,
            mul_pow, integral_const_mul, pow_mul, finrank_real_of_complex, pow_right_comm _ d]
      _ ≤ _ := by grw [← mul_assoc, ← pow_add, c_pow]
  -- As `x` and `σ x + y` are not both small, the two denominators multiply to at least `K⁻¹`.
  have pointwise (x : ι → ℂ) :
      ‖v x‖ * ‖v ((σ : Matrix ι ι ℂ).mulVec x + y)‖ ≤ K / 2 * (G x + G (σ • x + y)) := by
    let e : ℝ := ‖toLp 2 x‖ ^ 2 / (n + A) / 2 +
      ‖toLp 2 ((σ : Matrix ι ι ℂ).mulVec x) + toLp 2 y‖ ^ 2 / (n + A) / 2
    have one_le :
        1 ≤ exp e * (4 * (A + n) * ((‖(σ : Matrix ι ι ℂ)‖ / ‖toLp 2 y‖) ^ 2 / exp 1)) := by
      grw [← exp_one_mul_le_exp]
      simp only [e]
      field_simp
      linear_combination 2 * (n + A) * norm_sq_le_norm_sq_add_norm_mulVec_add_sq σ x y
    calc _ = ‖v_scaled (c⁻¹ • x)‖ * ‖v_scaled (c⁻¹ • (σ • x + y))‖ / exp e ^ n := by
          simp [norm_v, unitary_smul_eq_mulVec, e, exp_add, mul_pow, div_mul_div_comm]
      _ ≤ (G x + G (σ • x + y)) / 2 / exp e ^ n := by
          gcongr
          linarith [two_mul_le_add_sq ‖v_scaled (c⁻¹ • x)‖ ‖v_scaled (c⁻¹ • (σ • x + y))‖]
      _ ≤ (G x + G (σ • x + y)) / 2 / exp e ^ n * (exp e ^ n * K) := by
          grw [← mul_pow, ← one_le_pow₀ one_le, mul_one]
      _ = _ := by field_simp
  -- By the reproducing property of the vacuum, the integrand below has the norm just bounded.
  have integrand_le (x : ι → ℂ) :
      ‖v x * fockInner (realHeisenbergOp (-y) v)
        (realHeisenbergOp ((σ : Matrix ι ι ℂ).mulVec x) vacElem)‖ ≤
        K / 2 * (G x + G (σ • x + y)) := by
    rw [← conj_modelInner, modelInner_heisenbergOp_vacElem]
    simpa [norm_eq_one] using pointwise x
  -- Move `realHeisenbergOp y` to the left and write `realWeil σ v` as an integral of translated
  -- vacua.
  have coeff_eq : ‖fockInner v (realHeisenbergOp y (realWeil σ v))‖ = ‖realMultiplier σ‖ *
      ‖∫ x, v x * fockInner (realHeisenbergOp (-y) v)
        (realHeisenbergOp ((σ : Matrix ι ι ℂ).mulVec x) vacElem)
        ∂normalizedVolume ι‖ := by
    rw [← modelInner_heisenbergOp (-y), mul, neg_add_cancel, Rep.rho_zero_apply]
    simp [weilRep, map_integrated_eq_integral, realAction, self_eq_one]
  -- The multiplier has norm at most `‖σ‖^|ι|`, and both terms of the bound have integral `∫ G`,
  -- since `x ↦ σ x + y` preserves the measure.
  rw [coeff_eq]
  calc _ ≤ ‖(σ : Matrix ι ι ℂ)‖ ^ card ι * (K / 2 *
        (exp n * ∫ x, ‖v x‖ ^ 2 ∂normalizedVolume ι + exp n * ∫ x,
          ‖v x‖ ^ 2 ∂normalizedVolume ι)) := by
        have G_int' : Integrable (G ∘ (σ • · + y)) _ :=
          preserving.integrable_comp_of_integrable G_int
        grw [norm_integral_le_of_norm_le ((G_int.add G_int').const_mul (K / 2))
          (.of_forall integrand_le), integral_const_mul, integral_add' G_int G_int',
          preserving.hasLaw.integral_comp G_int.aestronglyMeasurable, norm_realMultiplier_le, G_le]
    _ = _ := by
      simp [modelInner_self, K, mul_pow, pow_mul, div_pow, pow_add, field, one_add_one_eq_two]

end FockCoeffDecay

/-!
## First minimum of Hom(S, T) and sparse theta sums

`New.Space.firstMinimum V` is the length of a shortest nonzero vector of the lattice of `V`, cut off
at `1`. A point `g` enters by moving the space, as in `V.move g`. `New.modKernel S T a b 𝔪 Ψ Q` is
the theta kernel of `(S, T)` for the characters `a`, `b`, the function `Ψ` on matrices modulo `𝔪`
and the polynomial `Q`.
-/

namespace New.Rows

open NumberField Matrix ComplexConjugate Fock WeilData Norms.L2Operator Fintype Space G
  EuclideanSpace Complex BigOperators Modulus Finset Prod Set AddChar Circle

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  [Fintype n'] [DecidableEq n'] {s' : n' → ℤˣ}
  {S : Space E n s} (T : Space E n' s')

/-- For a space `V` let `λ(V) = V.firstMinimum` be the minimum of `1` and the length of a shortest
nonzero vector of the lattice of `V`. If the natural number `N ≠ 0` lies in the different of `E`,
then `λ(S) λ(T) / (C |n'| |n|) ≤ λ(Hom (S, T))`, where `C = shortBasisConst E n N = 6 N (f |n|)²`
and `f` is the number of infinite places of `E`. -/
theorem firstMinimum_mul_le_hom [Nonempty n] [Nonempty n']
    {S : Space E n s} (T : Space E n' s') {N : ℕ} [NeZero N]
    (hN_mem : ↑N ∈ differentIdeal ℤ (𝓞 E)) :
    S.firstMinimum * T.firstMinimum / (shortBasisConst E n N * Fintype.card n' * Fintype.card n) ≤
      (S.hom T).firstMinimum := by
  -- Read a nonzero lattice vector `z` of `Hom (S, T)` as a matrix and apply it to a short basis `Y`
  -- of the lattice of `S`. Some image is a nonzero lattice vector of `T`, so it has length at least
  -- `T.firstMinimum`; and its length is at most `card n' * card n * ‖z‖` times that of the basis
  -- vector.
  refine le_firstMinimum_iff.2 ⟨?_, fun z hz z_ne ↦ ?_⟩
  · -- both minima are at most `1` and the denominator is a natural number
    grw [firstMinimum_le_one, firstMinimum_le_one]
    · simp [Nat.cast_inv_le_one, ← Nat.cast_mul]
    all_goals simp [firstMinimum_pos, le_of_lt]
  choose Y Y_mem Y_short using S.exists_short_basis hN_mem
  -- `k`, the matrix of `z` in adelic coordinates, takes the coordinates of `y` to those of `z y`
  let k : Matrix n' n (𝔸 E) := vecToMatrix ((S.hom T).vecAtPoint z)
  have vec_eq (y : n → E) : T.vecAtPoint (vecToMatrix z *ᵥ y) = k *ᵥ S.vecAtPoint y := by
    -- `z` is `matrixToVec (vecToMatrix z)` by definition.
    simp [k, show (S.hom T).vecAtPoint z = matrixToVec (T.ratMap S (vecToMatrix z)) from
      vecAtPoint_hom _ _ (vecToMatrix z), ratMap_mulVec_vecAtPoint]
  have norm_k (w : InfinitePlace E) :
      ‖k.map (·.1 w)‖ ≤ card n' * card n * ‖(S.hom T).archCoords z‖ :=
    l2_opNorm_le_of_apply fun i j ↦ ((S.hom T).archCoords z).norm_apply_le (w, i, j)
  have k_int (i : n') (j : n) : (k i j).2 ∈ Ô E := hz (i, j)
  -- As `Y` is invertible and `z ≠ 0`, some basis vector has a nonzero image.
  obtain ⟨j, hj⟩ : ∃ j : n, vecToMatrix z *ᵥ Y.1.col j ≠ 0 := by
    by_contra! h_all
    have hzY : vecToMatrix z * Y.1 = 0 := Matrix.ext fun i j ↦ congrFun (h_all j) i
    exact z_ne (by simpa [Matrix.mul_assoc] using congrArg (fun M ↦ matrixToVec (M * Y⁻¹.1)) hzY :)
  -- That image lies in the lattice of `T`, and its length is bounded by means of `norm_k`.
  obtain ⟨image_mem, norm_image⟩ :=
    T.mem_and_norm_le_of_vecAtPoint _ S (Y.1.col j) k 1 norm_k (by rw [one_smul, vec_eq])
  grw [firstMinimum_le (image_mem (by simpa using k_int) (Y_mem j)) hj, norm_image, Y_short]
  · have h_pos : 0 < S.firstMinimum := S.firstMinimum_pos
    simp [field]
  all_goals simp [firstMinimum_pos, le_of_lt]

variable [WeilData E]

/-- Let `S`, `T` be hermitian spaces over `E` with signs `s`, `s'` at the infinite places, and
`S.hom T = Hom (S, T)`. Let `t` be a matrix modulo the ideal `𝔪` and `Ψ_t(y) = ψ(tr(y t))` its
additive character (`traceChar t`), with `ψ` the chosen primitive character of the residue ring. Let
`v`, `w` be vectors of the Fock space in the variables `(τ, (i, k))`, `τ` an infinite place, with
signs `s' i * s k`, and `z` an adelic vector of `Hom (S, T)`. The datum `v ⊗ Ψ_t ⊗ vac` (`modDatum`)
is the function on adelic vectors made of `v` at the infinite places, `Ψ_t` at the places dividing
`𝔪` and the vacuum elsewhere; `dataInner` is the pairing `∫ c̄ c'` of such functions and `ϱ` the
Heisenberg action on them.

Then `⟨v ⊗ Ψ_t ⊗ vac, ϱ(z)(w ⊗ Ψ_t ⊗ vac)⟩` is a product of three factors. Write `z_f` for the
finite part of `z`, and `α`, `j` for the finite idele and the imaginary element of `E` fixed by
`WeilData E`. The first factor is `Ψ_t` read (by `liftFn`) at `finCoord z = α⁻¹ z_f`. The second is
the Fock coefficient `⟨v, ϱ(x) w⟩` at `x = realCoord z`, the components of `z` at the places `τ`
times `√(2π Im τ(j))`. The third is `vacuumFn` at `finVec (finCoord z) = (0, z_f)`: a complex number
of modulus `1` if `α⁻¹ z_f` is integral, and `0` otherwise. -/
lemma dataInner_traceChar {𝔪 : Modulus E} (t : Matrix n n' 𝔪.ResidueRing)
    (v w : fockSpace (realSigns E (homSigns s s'))) (z : n' × n → 𝔸 E) :
    (S.hom T).dataInner (modDatum S T 𝔪 (traceChar t) v)
        ((S.hom T).ϱ z (modDatum S T 𝔪 (traceChar t) w)) =
      𝔪.liftFn (traceChar t ∘ vecToMatrix) (finCoord z) *
        (fockInner v (realHeisenbergOp (realCoord z) w) * vacuumFn (finVec (finCoord z))) := by
  -- The finite part of the datum of `traceChar t` is the vacuum translated by a finite vector `y`.
  -- Moving `ϱ z_f` past `ϱ y` costs the phase `β(z_f, y) ^ 2`; if `α⁻¹ z_f` is integral, this is
  -- the lift of `traceChar t` at it.
  choose lift hlift using fun i j ↦ 𝔪.reduction_surjective (t i j)
  -- `tLift` is an integral lift of the transpose of `t`, so the trace of `x * t` is a dot product
  let tLift (p : n' × n) : Ô E := lift p.2 p.1
  have h_char :
      traceChar t ∘ vecToMatrix = fun x ↦ 𝔪.primAddChar (x ⬝ᵥ 𝔪.reduction ∘ tLift) := by
    simp [funext_iff, tLift, hlift, trace, Matrix.mul_apply, dotProduct, sum_prod_type, traceChar,
      vecToMatrix]
  let y : n' × n → 𝔸 E := finVec (star (idem 𝔪.places • 𝔪.generator⁻¹.1 • Subtype.val ∘ tLift))
  let zf : n' × n → 𝔸 E := fun i ↦ (0, (z i).2)
  have h_zf : finVec (finCoord z) = zf := funext fun i ↦ by simp [finVec, finCoord, zf]
  rw [h_zf]
  -- the pairing splits into a real and a finite part; `ϱ y` is unitary and cancels after `rho_swap`
  trans fockInner v (realHeisenbergOp (realCoord z) w) *
    ((adelicHeisenberg E (homSigns s s')).β zf y ^ 2 * vacuumFn zf)
  · rw [modDatum, modDatum, rho_integrated_realCoord, dataInner_integrated, h_char,
      𝔪.schrodingerOp_char_eq_translate_projOn, rho_swap, map_smul]
    -- ↓ rewrites operators on integrated vectors before their arguments are simplified.
    simp [y, zf, finVec, ↓← rho_integrated, vacuumFn]
  by_cases hz : ∀ i, finCoord z i ∈ Ô E
  · -- The phase of `ϱ zf` past `ϱ y` is the lift of `traceChar t` at `α⁻¹ z_f`.
    have h_beta : ((adelicHeisenberg E (homSigns s s')).β zf y : ℂ) ^ 2 =
      (ψf E (algebraMap E (𝔸f E) j * ∑ x, star α.val *
        (idem 𝔪.places * (𝔪.generator⁻¹.1 * (tLift x).1)) * (z x).2) : Circle) := by
      simp [y, zf, finVec, adelicHeisenberg, stdForm, stdAddChar, dotProduct, fst_sum, snd_sum,
        mulVec_diagonal, ← Circle.coe_pow, ← map_nsmul_eq_pow, two_mul, ← map_add, ← add_mul]
    rw [h_char, 𝔪.liftFn_apply, dite_eq_left fun i ↦ mul_mem (idem_mem_Ô _) (hz i), h_beta,
      mul_left_comm]
    simp [zf, finCoord, stdLattice.selfDualAddChar_apply, dotProduct, ← map_mul, ← map_sum, mul_sum,
      mul_assoc,
      mul_left_comm, mul_comm (tLift _).1]
  · -- Otherwise `z_f` lies outside the support of the vacuum.
    have h_vac : vacuumFn zf = 0 := by simpa [zf, vacuumFn, finCoord] using hz
    simp [h_vac]

omit [WeilData E] in
/-- Let `u` and `u'` be families of matrices `u τ` in `U(diag s)` and `u' τ` in `U(diag s')`, one
for each infinite place `τ` of `E` (`GInf`). The block diagonal matrix `pairHomInf (u, u')`, which
acts on `n' × n` matrices by `x ↦ (u' τ) x (u τ)⁻¹` at `τ`, has ℓ² operator norm at most
`maxOpNorm u * maxOpNorm u'`, where `maxOpNorm u` is the largest of the norms `‖u τ‖`. -/
lemma norm_pairHomInf_le_mul (u : GInf E s) (u' : GInf E s') :
    ‖(pairHomInf (u, u') :
        Matrix (InfinitePlace E × n' × n) (InfinitePlace E × n' × n) ℂ)‖ ≤
      maxOpNorm u * maxOpNorm u' := by
  -- The block diagonal map is a star homomorphism, so it does not increase norms, and each block
  -- is a Kronecker product.
  let B : (InfinitePlace E → Matrix (n' × n) (n' × n) ℂ) →⋆ₙₐ[ℂ]
      Matrix (InfinitePlace E × n' × n) (InfinitePlace E × n' × n) ℂ :=
    { blockMatrix with map_smul' := by simp [submatrix_smul], map_star' := by simp [star] }
  refine (NonUnitalStarAlgHom.norm_apply_le B _).trans ((pi_norm_le_iff_of_nonempty _).2 fun τ ↦ ?_)
  refine (norm_pairHom_le ..).trans ?_
  change ‖(u τ : Matrix n n ℂ)‖ * ‖(u' τ : Matrix n' n' ℂ)‖ ≤ maxOpNorm u * maxOpNorm u'
  gcongr
  exacts [norm_le_pi_norm (fun w ↦ (u w : Matrix n n ℂ)) τ,
    norm_le_pi_norm (fun w ↦ (u' w : Matrix n' n' ℂ)) τ]

/-- Let `V` be a hermitian space over `E` with adelic point `x` (`Space`). Its lattice
`V.baseLattice` consists of the rational vectors `y` whose adelic vector `V.vecAtPoint y = x⁻¹ y`
has integral finite part, and `λ = V.firstMinimum` is the minimum of `1` and the length of a
shortest nonzero lattice vector. Let `Φ w` be the chosen complex embedding at the infinite place `w`
and `j` the element of `E` with `Im (Φ w j) > 0` fixed by `WeilData E`. Let `c ≠ 0` and `m > 0`
satisfy `m |Φ w c| ≤ √(2π Im (Φ w j)) λ` for all `w`. If `y ≠ 0` and `c y` lies in the lattice, then
the Fock coordinates of `x⁻¹ y` have Euclidean norm at least `m`. -/
lemma le_norm_realCoord {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ} (V : Space E ι ε)
    {c : E} (hc_ne : c ≠ 0) {m : ℝ} (hm_pos : 0 < m)
    (hm : ∀ w : InfinitePlace E, m * ‖Φ w c‖ ≤ √(2 * Real.pi * (Φ w j).im) * V.firstMinimum)
    {y : ι → E} (hy_mem : c • y ∈ V.baseLattice) (hy_ne : y ≠ 0) :
    m ≤ ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖ := by
  -- The vector `c • y` is a nonzero lattice vector, so its length is at least the first minimum.
  refine le_of_mul_le_mul_right ?_ V.firstMinimum_pos
  calc m * V.firstMinimum ≤ ‖m • V.archCoords (c • y)‖ := by
        grw [norm_smul_of_nonneg hm_pos.le, firstMinimum_le hy_mem (smul_ne_zero hc_ne hy_ne)]
    _ ≤ ‖V.firstMinimum • WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖ := by
      -- Compare coordinate by coordinate, using `hm`.
      simp only [norm_eq]
      gcongr with ⟨w, i⟩
      calc _ = m * ‖Φ w c‖ * ‖(V.vecAtPoint y i).1 w‖ := by
            simp [abs_of_nonneg, hm_pos.le, archCoords, mul_assoc]
        _ ≤ √(2 * Real.pi * (Φ w j).im) * V.firstMinimum * ‖(V.vecAtPoint y i).1 w‖ := by grw [hm]
        _ = _ := by simp [abs_of_nonneg, realCoord, V.firstMinimum_pos.le, val_scaleIdele_fst,
          field]
    _ = _ := by simp [norm_smul, V.firstMinimum_pos.le, mul_comm]

/-- Let `c ≠ 0` and `m > 0` satisfy `m ‖Φ w c‖ ≤ √(2π Im (Φ w j)) · V.firstMinimum` at every
infinite place `w`. If `y ≠ z` and both `c • y` and `c • z` lie in `V.baseLattice`, then the Fock
coordinates `realCoord (V.vecAtPoint y)` and `realCoord (V.vecAtPoint z)` are at distance at least
`m`. -/
lemma le_norm_realCoord_sub {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ} (V : Space E ι ε)
    {c : E} (hc_ne : c ≠ 0) {m : ℝ} (hm_pos : 0 < m)
    (hm : ∀ w : InfinitePlace E, m * ‖Φ w c‖ ≤ √(2 * Real.pi * (Φ w j).im) * V.firstMinimum)
    {y z : ι → E} (hy_mem : c • y ∈ V.baseLattice) (hz_mem : c • z ∈ V.baseLattice) (hyz : y ≠ z) :
    m ≤ ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y)) -
      WithLp.toLp 2 (realCoord (V.vecAtPoint z))‖ := by
  have diff_far : m ≤ ‖WithLp.toLp 2 (realCoord (V.vecAtPoint (y - z)))‖ :=
    le_norm_realCoord V hc_ne hm_pos hm (by simpa [smul_sub] using sub_mem hy_mem hz_mem)
      (sub_ne_zero.2 hyz)
  -- The Fock coordinates of `y - z` are the differences of those of `y` and `z`.
  simpa [← sub_div, realCoord, norm_eq] using diff_far

/-- Let `V` be a hermitian space over `E` with adelic point `x` (`Space`). Its lattice
`V.baseLattice` consists of the rational vectors `y` whose adelic vector `V.vecAtPoint y = x⁻¹ y`
has integral finite part, and `λ = V.firstMinimum` is the minimum of `1` and the length of a
shortest nonzero lattice vector. Let `Φ w` be the chosen complex embedding at the infinite place `w`
and `j` the element of `E` with `Im (Φ w j) > 0` fixed by `WeilData E`. Let `c ≠ 0` and `m > 0`
satisfy `m |Φ w c| ≤ √(2π Im (Φ w j)) λ` for all `w`. Let `y` run over the nonzero vectors with
`c y` in the lattice, and let `|y|` be the Euclidean norm of the Fock coordinates of `x⁻¹ y`. If `q`
exceeds the number of these coordinates, then `m ≤ |y|` for all such `y`, and `∑ |y| ^ (-2q)`
converges and is at most `(5 / m) ^ (2q)`. -/
lemma tsum_inv_norm_realCoord_pow_le {ι : Type} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}
    (V : Space E ι ε) {c : E} (hc_ne : c ≠ 0) {m : ℝ} (hm_pos : 0 < m)
    (hm : ∀ w : InfinitePlace E, m * ‖Φ w c‖ ≤ √(2 * Real.pi * (Φ w j).im) * V.firstMinimum)
    {q : ℕ} (hq : Fintype.card (InfinitePlace E × ι) < q) :
    (∀ y : {y : ι → E | c • y ∈ V.baseLattice ∧ y ≠ 0},
      m ≤ ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖) ∧
    Summable (fun y : {y : ι → E | c • y ∈ V.baseLattice ∧ y ≠ 0} ↦
      ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖⁻¹ ^ (2 * q)) ∧
    ∑' y : {y : ι → E | c • y ∈ V.baseLattice ∧ y ≠ 0},
      ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖⁻¹ ^ (2 * q) ≤ (5 / m) ^ (2 * q) := by
  -- The points are `m`-separated and at distance at least `m` from `0`, so the packing bound
  -- applies; by `hq`, the exponent `2 * q` exceeds the real dimension by at least `2`.
  let L : Set (ι → E) := {y | c • y ∈ V.baseLattice ∧ y ≠ 0}
  let f (y : L) : EuclideanSpace ℂ (InfinitePlace E × ι) :=
    WithLp.toLp 2 (realCoord (V.vecAtPoint y))
  have h_far : ∀ y : L, m ≤ ‖f y‖ := fun ⟨_, hy, hy_ne⟩ ↦
    le_norm_realCoord V hc_ne hm_pos hm hy hy_ne
  have h_sep : Pairwise fun y z : L ↦ m ≤ ‖f y - f z‖ := fun ⟨_, hy, _⟩ ⟨_, hz, _⟩ hyz ↦
    le_norm_realCoord_sub V hc_ne hm_pos hm hy hz (Subtype.coe_ne_coe.2 hyz)
  have h_dim : Module.finrank ℝ (EuclideanSpace ℂ (InfinitePlace E × ι)) + 2 ≤ 2 * q := by
    simpa [finrank_real_of_complex, ← mul_add_one, le_of_lt] using hq
  exact ⟨h_far, tsum_inv_pow_le_of_separated hm_pos h_sep h_far h_dim⟩

open scoped Classical in
/-- Let `S`, `T` be hermitian spaces with signs `s`, `s'`, let `p` be an adelic point of the unitary
group of `S.hom T = Hom (S, T)`, whose signs are `homSigns s s' (i, k) = s' i * s k`, let `v`, `w`
be Fock vectors and let `y` be a rational vector. For a matrix `t` modulo the modulus `𝔪` with
additive character `Ψ_t = traceChar t`, the datum `v ⊗ Ψ_t ⊗ vac` (`modDatum`) is made of `v` at the
infinite places, `Ψ_t` at the places dividing `𝔪` and the vacuum vector elsewhere. Average over `t`
the pairing (`dataInner`) of `ω(p)(v ⊗ Ψ_t ⊗ vac)` with the Heisenberg translate `ϱ`, by the adelic
vector of `y` (`vecAtPoint`), of `ω(p)(w ⊗ Ψ_t ⊗ vac)`, where `ω` is the Weil action.

Let `x` be the adelic vector of `y` at the point of `Hom (S, T)` moved by `p`, with finite parts
`(x i).2`, and let `finCoord x` be these finite parts divided by the finite idele `α`. If
`finCoord x` is integral and vanishes modulo `𝔪`, the average is `fockInner v (realHeisenbergOp ξ
w) * ψf (traceOne * j / 2 * ∑ i, conj (x i).2 * (x i).2)`; otherwise it is `0`. Here
`realHeisenbergOp` is the Heisenberg action on the Fock space, `ξ = realCoord x` lists the
components of `x` at the infinite places `τ` times `√(2π Im τ(j))`, and `ψf` is the finite part of
the standard additive character. The idele `α` and the imaginary `j` in `E` are fixed by
`WeilData E`, and `traceOne = (1 - j⁻¹) / 2`. -/
lemma sum_dataInner_traceChar_div_card {𝔪 : Modulus E} (p : G E (homSigns s s'))
    (v w : fockSpace (realSigns E (homSigns s s'))) (y : n' × n → E) :
    let x : n' × n → 𝔸 E := ((S.hom T).move p).vecAtPoint y
    (∑ t : Matrix n n' 𝔪.ResidueRing,
        (S.hom T).dataInner ((S.hom T).ω p (modDatum S T 𝔪 (traceChar t) v))
          ((S.hom T).ϱ ((S.hom T).vecAtPoint y)
            ((S.hom T).ω p (modDatum S T 𝔪 (traceChar t) w)))) /
        Fintype.card (Matrix n n' 𝔪.ResidueRing) =
      if ∃ hx : ∀ i : n' × n, finCoord x i ∈ Ô E,
          ∀ i : n' × n, 𝔪.reduction ⟨finCoord x i, hx i⟩ = 0 then
        fockInner v (realHeisenbergOp (realCoord x) w) *
          ψf E ((traceOne * j / 2 : E) * ∑ i : n' × n, star (x i).2 * (x i).2)
      else 0 := by
  intro x
  -- Move `ω p` across the inner product, unfold the data and sum the characters over `t`. The
  -- idempotent of the places dividing `𝔪` does not change the class of an integral vector.
  have h_red (r : 𝔸f E) (hr : r ∈ Ô E) (hr' : idem 𝔪.places * r ∈ Ô E) :
      𝔪.reduction ⟨idem 𝔪.places * r, hr'⟩ = 𝔪.reduction ⟨r, hr⟩ := 𝔪.reduction_idem_mul ⟨r, hr⟩
  have h_term (t : Matrix n n' 𝔪.ResidueRing) :
      (S.hom T).dataInner ((S.hom T).ω p (modDatum S T 𝔪 (traceChar t) v))
          ((S.hom T).ϱ ((S.hom T).vecAtPoint y)
            ((S.hom T).ω p (modDatum S T 𝔪 (traceChar t) w))) =
        𝔪.liftFn (traceChar t ∘ vecToMatrix) (finCoord x) *
          (fockInner v (realHeisenbergOp (realCoord x) w) * vacuumFn (finVec (finCoord x))) := by
    simp [x, dataInner_omega_left, omega_rho, rep_apply_apply, dataInner_traceChar, vecAtPoint_move]
  simp only [h_term, ← sum_mul]
  by_cases hx : ∀ (i : n') (k : n), α⁻¹.val * (x (i, k)).2 ∈ Ô E
  · -- The sum of the characters `traceChar t` at a matrix vanishes unless the matrix is `0`.
    simp [finCoord, sum_addChar_trace_mul, isPrimitive_primAddChar, ← ext_iff, div_eq_inv_mul,
      liftFn_apply, traceChar, vecToMatrix, vacuumFn, finVec, hx, h_red, mul_mem, idem_mem_Ô]
  · -- Off the integral vectors the vacuum vanishes.
    simp [finCoord, vacuumFn, finVec, hx]

/-- Let the characters `a`, `b` of the unitary adeles of `E` (`AutChar`) have weights `γ`, `γ'` at
the infinite places and tame parts `ψ`, `ψ'` at the finite ones, and let `Ψ` be the average of the
characters `Ψ_t = traceChar t`, weighted by the conjugates of their theta kernels at `(g, h)`. Then
the kernel of `Ψ` at `(g u, h u')`, for real points `u`, `u'`, is the average over `t` of
`θ(ω(p)(w ⊗ Ψ_t ⊗ vac)) conj θ(ω(p)(v ⊗ Ψ_t ⊗ vac))`. Here `p = onHom (g, h)` is the point of
`Hom (S, T)` given by `(g, h)`, `ω` the untwisted adelic Weil action, `θ` the theta functional, `v`
the Fock vector of `Q` and `w = Ω(u, u') v`, with `Ω = realPairWeil γ γ'` the real Weil
representation of the pair twisted by powers of the determinants with exponents from `γ`, `γ'`. -/
lemma modKernel_expect_traceChar {a b : AutChar E} {γ γ' : InfinitePlace E → ℤ}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} {𝔪 : Modulus E}
    (ha : a.HasWeight γ ψ) (hb : b.HasWeight γ' ψ') (g : G E s) (h : G E s')
    (Q : MvPolynomial (InfinitePlace E × n' × n) ℂ) {v : fockSpace (realSigns E (homSigns s s'))}
    (hv : v = polyVector (realSigns E (homSigns s s')) Q) (u : GInf E s) (u' : GInf E s') :
    modKernel S T a b 𝔪 (𝔼 t : Matrix n n' 𝔪.ResidueRing,
        conj (modKernel S T a b 𝔪 (traceChar t) Q g h) • traceChar t) Q
        (g * (u, 1)) (h * (u', 1)) =
      (∑ t : Matrix n n' 𝔪.ResidueRing, (S.hom T).θ ((S.hom T).ω (G.onHom (g, h))
          (modDatum S T 𝔪 (traceChar t) (realPairWeil γ γ' (u, u') v))) *
        conj ((S.hom T).θ ((S.hom T).ω (G.onHom (g, h)) (modDatum S T 𝔪 (traceChar t) v)))) /
        Fintype.card (Matrix n n' 𝔪.ResidueRing) := by
  classical
  -- The unit scalar that `a`, `b` contribute at `(g, h)` cancels against its conjugate.
  have phase_cancel (f f' : 𝒮 (S.hom T)) :
      pairWeil S T a b (g, h) f 0 * conj (pairWeil S T a b (g, h) f' 0) =
        (S.hom T).ω (G.onHom (g, h)) f 0 * conj ((S.hom T).ω (G.onHom (g, h)) f' 0) := by
    calc _ = (pairChar a b (g, h) : ℂ) * conj (pairChar a b (g, h) : ℂ) *
          ((S.hom T).ω (G.onHom (g, h)) f 0 * conj ((S.hom T).ω (G.onHom (g, h)) f' 0)) := by
          simp [pairWeil]
          ring
      _ = _ := by rw [Complex.mul_conj', show ‖pairChar a b (g, h)‖ = 1 from norm_coe _, ofReal_one,
          one_pow, one_mul]
  -- By `pairWeil_integrated`, which uses the weights `ha` and `hb`, the real points act on `v` by
  -- `realPairWeil γ γ'`.
  have h_real (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) :
      pairWeil S T a b (g * (u, 1), h * (u', 1)) (modDatum S T 𝔪 Ψ v) =
        pairWeil S T a b (g, h) (modDatum S T 𝔪 Ψ (realPairWeil γ γ' (u, u') v)) := by
    simp [← Prod.mk_mul_mk, modDatum, pairWeil_integrated (γ := γ) (γ' := γ')]
  rw [← modKernelBilin_apply]
  -- By linearity the kernel of the average is the average of the kernels.
  simp [modKernel, pairTheta, mul_comm (conj _), h_real, expect, NNRat.smul_def, ← hv,
    div_eq_inv_mul, phase_cancel]

/-- Let `S`, `T` be hermitian spaces over `E` with signs `s`, `s'`, let `g`, `h` be points of their
adelic unitary groups, and let `a`, `b` be characters of the unitary adeles of `E` with weights `γ`,
`γ'` and tame parts `ψ`, `ψ'` (`HasWeight`). The class `WeilData E` fixes an imaginary element `j`
of `E` and a finite idele `α` that makes `Ô E` self-dual for the pairing `ψ_f(j α ᾱ z z')`. Let
`c ≠ 0` be such that `c α z` is integral for every `z` in `Ô E` that vanishes modulo `𝔪`. Let `λ` be
the first minimum of `Hom (S, T)` with the points moved by `g` and `h`, let `m > 0` satisfy
`m |Φ w c| ≤ √(2π Im (Φ w j)) λ` at all infinite places `w`, and let `q` exceed the number of
complex variables. Let `Q` be homogeneous of degree `d` under real scalings, with Fock vector `v`.

For a function `Ψ` on matrices modulo `𝔪`, the theta kernel `modKernel S T a b 𝔪 Ψ Q` sends a pair
of points `p` to `θ(ω_{a,b}(p)(v ⊗ Ψ ⊗ vac))`: the theta functional of the datum made of `v` at the
infinite places, `Ψ` at the places dividing `𝔪` and the vacuum elsewhere, moved by the Weil action
twisted by `a` and `b`. Then some `Ψ` has the property that, for all real points `u`, `u'`, this
kernel at `(g u, h u')` is within `(100 (d + 2q) / m²) ^ q (‖u‖ ‖u'‖) ^ (3q) |⟨v, v⟩|` of
`⟨v, Ω(u, u') v⟩`. Here `Ω` is the real Weil representation `realPairWeil γ γ'`, on the Fock space
for the signs `(τ, (i, k)) ↦ s' i * s k`, and `‖u‖ = maxOpNorm u` is the largest operator norm of
`u` at a place. -/
theorem exists_norm_modKernel_sub_fockInner_le [Nonempty n] [Nonempty n']
    {a b : AutChar E} {γ γ' : InfinitePlace E → ℤ}
    {ψ ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ} {𝔪 : Modulus E} {g : G E s}
    (ha : a.HasWeight γ ψ) (hb : b.HasWeight γ' ψ') {c : E} (hc_ne : c ≠ 0)
    (hc : ∀ z : Ô E, 𝔪.reduction z = 0 → (c : 𝔸f E) * (α.val * z.val) ∈ Ô E) (h : G E s') (m : ℝ)
    (q : ℕ) (hm_pos : 0 < m)
    (hm : ∀ w : InfinitePlace E, m * ‖Φ w c‖ ≤
      √(2 * Real.pi * (Φ w j).im) * ((S.move g).hom (T.move h)).firstMinimum)
    (hq : Fintype.card (InfinitePlace E × n' × n) < q)
    (Q : MvPolynomial (InfinitePlace E × n' × n) ℂ) {v : fockSpace (realSigns E (homSigns s s'))}
    (hv : v = polyVector (realSigns E (homSigns s s')) Q) (d : ℕ)
    (hQ : ∀ (r : ℝ) (x : InfinitePlace E × n' × n → ℂ), Q.eval (r • x) = r ^ d * Q.eval x) :
    ∃ Ψ : Matrix n' n 𝔪.ResidueRing → ℂ, ∀ (u : GInf E s) (u' : GInf E s'),
      ‖modKernel S T a b 𝔪 Ψ Q (g * (u, 1)) (h * (u', 1)) -
          fockInner v (realPairWeil γ γ' (u, u') v)‖ ≤
        maxOpNorm u' ^ (3 * q) * (100 * (d + 2 * q) / m ^ 2) ^ q * ‖fockInner v v‖ *
          maxOpNorm u ^ (3 * q) := by
  classical
  -- Take for `Ψ` the mean of the characters `traceChar t`, weighted by the conjugates of their
  -- kernels at `(g, h)`. Its kernel is a mean of products of thetas, hence a sum of terms `term y`
  -- over rational `y`. The term `y = 0` is the Fock coefficient; the others live on an
  -- `m`-separated set and decay fast.
  refine ⟨𝔼 t, conj (modKernel S T a b 𝔪 (traceChar t) Q g h) • traceChar t, fun u u' ↦ ?_⟩
  let p : G E (homSigns s s') := G.onHom (g, h)
  let V : Space E (n' × n) (homSigns s s') := (S.hom T).move p
  rw [show (S.move g).hom (T.move h) = V by
    simp [V, p, move, Space.hom, Units.ext_iff, mul_kronecker_mul, G.onHom]] at hm
  let L : Set (n' × n → E) := {y | c • y ∈ V.baseLattice ∧ y ≠ 0}
  let len (y : n' × n → E) : ℝ := ‖WithLp.toLp 2 (realCoord (V.vecAtPoint y))‖
  obtain ⟨h_far, h_summable, h_tsum⟩ : (∀ y : L, m ≤ len y) ∧
      Summable (fun y : L ↦ (len y)⁻¹ ^ (2 * q)) ∧
      ∑' y : L, (len y)⁻¹ ^ (2 * q) ≤ (5 / m) ^ (2 * q) :=
    tsum_inv_norm_realCoord_pow_le V hc_ne hm_pos hm hq
  -- The mean over `t` of the products of thetas is a sum over rational vectors.
  let w : fockSpace (realSigns E (homSigns s s')) := realPairWeil γ γ' (u, u') v
  let φ (t : Matrix n n' 𝔪.ResidueRing) (f : fockSpace (realSigns E (homSigns s s'))) :
    𝒮 (S.hom T) :=
    (S.hom T).ω p (modDatum S T 𝔪 (traceChar t) f)
  let mean : ℂ := (∑ t, (S.hom T).θ (φ t w) * conj ((S.hom T).θ (φ t v))) /
    card (Matrix n n' 𝔪.ResidueRing)
  let term (y : n' × n → E) : ℂ :=
    (∑ t, (S.hom T).dataInner (φ t v) ((S.hom T).ϱ ((S.hom T).vecAtPoint y) (φ t w))) /
      card (Matrix n n' 𝔪.ResidueRing)
  have h_sum : HasSum term mean :=
    (hasSum_sum fun t _ ↦ hasSum_dataInner _ (φ t w) (φ t v)).div_const _
  let x (y : n' × n → E) : n' × n → 𝔸 E := V.vecAtPoint y
  let χ (y : n' × n → E) : Circle :=
    ψf E ((traceOne * j / 2 : E) * ∑ i, star (x y i).2 * (x y i).2)
  have term_eq (y : n' × n → E) : term y =
      if ∃ hx : ∀ i, finCoord (x y) i ∈ Ô E, ∀ i, 𝔪.reduction ⟨finCoord (x y) i, hx i⟩ = 0 then
        fockInner v (realHeisenbergOp (realCoord (x y)) w) * χ y
      else 0 :=
    sum_dataInner_traceChar_div_card T p v w y
  -- By `hc`, the condition in `term_eq` puts `c • y` in the lattice.
  have h_supp : Function.support (fun y ↦ if y = 0 then 0 else term y) ⊆ L := by
    intro y hy
    obtain ⟨y_ne, term_ne⟩ := ite_ne_left_iff.1 hy
    obtain ⟨⟨hz, hz_zero⟩, -⟩ := ite_ne_right_iff.1 ((term_eq y).symm.trans_ne term_ne.symm)
    exact ⟨fun i ↦ by simpa [x, finCoord] using hc _ (hz_zero i), y_ne⟩
  -- Removing the term `y = 0` leaves the difference to be bounded, as a sum over `L`.
  have h_rest : HasSum (fun y : L ↦ if y.1 = 0 then 0 else term y) (mean - term 0) :=
    (hasSum_subtype_iff_of_support_subset h_supp).2 (hasSum_ite_sub_hasSum h_sum 0)
  -- Each term decays like a Heisenberg matrix coefficient of the Fock vector `v`.
  set dim : ℕ := card (InfinitePlace E × n' × n)
  let σ : USign (realSigns E (homSigns s s')) := pairHomInf (u, u')
  let normσ : ℝ := ‖(σ : Matrix (InfinitePlace E × n' × n) (InfinitePlace E × n' × n) ℂ)‖
  have term_le (y : L) :
      ‖if y.1 = 0 then 0 else term y‖ ≤
        normσ ^ (dim + 2 * q) * (fockInner v v).re * (4 * ((d + dim : ℕ) + q)) ^ q *
          (len y)⁻¹ ^ (2 * q) := by
    calc _ ≤ ‖fockInner v (realHeisenbergOp (realCoord (x y)) (realWeil σ v))‖ := by
          rw [term_eq]
          split_ifs <;> simp [w, σ, χ, realPairWeil, prod_mul_distrib, norm_coe]
      _ ≤ _ := norm_fockInner_realHeisenbergOp_le σ hv hQ le_rfl (hm_pos.trans_le (h_far y))
  have h_zero : term 0 = fockInner v w := by
    simp [term_eq, x, χ, finCoord, ← ZeroMemClass.zero_def, realCoord.eq_unfold, ← Pi.zero_def]
  rw [modKernel_expect_traceChar T ha hb g h Q hv u u', ← h_zero]
  -- Sum the bounds of the terms, use `dim ≤ q`, and collect the constants: `100 = 4 * 5 ^ 2`.
  calc ‖mean - term 0‖
      ≤ normσ ^ (dim + 2 * q) * (fockInner v v).re * (4 * ((d + dim : ℕ) + q)) ^ q *
          ∑' y : L, (len y)⁻¹ ^ (2 * q) :=
        h_rest.norm_le_of_bounded (h_summable.hasSum.mul_left _) term_le
    _ ≤ (maxOpNorm u * maxOpNorm u') ^ (q + 2 * q) * ‖fockInner v v‖ * (4 * ((d + q : ℕ) + q)) ^ q *
        (5 / m) ^ (2 * q) := by
      have one_le : 1 ≤ normσ := U.one_le_norm σ
      have normσ_le : normσ ≤ maxOpNorm u * maxOpNorm u' := norm_pairHomInf_le_mul u u'
      grw [re_le_norm, h_tsum, hq, hq, normσ_le]
    _ = _ := by
      rw [mul_assoc _ _ ((5 / m) ^ _), pow_mul (5 / m), ← mul_pow]
      push_cast
      ring

end New.Rows

/-!
## Integrals of holomorphic discrete series coefficients and isolation

Archimedean estimates on `New.GInf E s`, the product of the groups `U(diag s)` over the `f`
infinite places. `New.holMinorsPi s k` is the basic function `Min^hol` of weight `k`, a product of
quotients of principal minors, written `m_k`. For dominant `k` (`New.IsKDominant`) with a large gap
between the two sign blocks (`New.HasHolGap`) it is a matrix coefficient of a holomorphic discrete
series. Below, `u`, `u'` are two such weights, the entries of `u` at most `5 b` in modulus, and
`b = D.b`, `n_* = New.Data.nStar D` for admissible data `D`.

* `New.Data.integral_norm_holMinorsPi_mul_pow_le`: `∫ |m_u|²` is positive, and
  `∫ |m_u'(h)| |h| ^ (6 n_*) dh ≤ b ^ n_* ∫ |m_u|²`.
* `New.Data.integrable_mul_holMinorsPi`: a continuous function of growth at most
  `C |h| ^ (6 n_*)` is integrable against `m_u'`, with integral at most `C b ^ n_* ∫ |m_u|²`.
* `New.Data.integrable_holMinorsPi`: `m_u` is integrable; the bound on its entries is not needed.
-/

section Isolation

open MeasureTheory Matrix Norms.L2Operator Finset Fintype AddCircle NumberField

namespace New.Rows

/-- A point of the archimedean unitary group has operator norm at least `1` at every place, so the
largest of these norms is at least `1`. -/
@[bound] theorem one_le_maxOpNorm {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n]
    [DecidableEq n] [Nonempty n] {s : n → ℤˣ} (h : GInf E s) : 1 ≤ maxOpNorm h := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact (U.one_le_norm (h w)).trans (norm_le_pi_norm (fun w ↦ (h w : Matrix n n ℂ)) w)

end New.Rows

namespace New.Data

open Rows DiscreteSeries

/-- Let `D` be admissible data, with weight `b = D.b` and rank step `t = D.t`; in such data `b` is
very large against `t`. For natural numbers `n ≤ t` and `L ≤ 10 b + t`, the constant
`8 (2000 (n + L + 1)⁶) ^ (2 n²) 2 ^ (10 n³)` of `New.integral_tail_le` is at most
`2 ^ (13 t³) b ^ (14 t²)`. -/
lemma eight_mul_pow_mul_two_pow_le {P : Parameters} (D : Data P) {n L : ℕ} (hn : n ≤ D.t)
    (hL : (L : ℝ) ≤ 2 * (5 * D.b) + D.t) :
    (8 * (2000 * (n + L + 1) ^ 6) ^ (2 * n ^ 2) * 2 ^ (10 * n ^ 3) : ℝ) ≤
      2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2) := by
  -- `le_of_hasLogBound` compares the logarithms of both sides: `b` is huge against `t`.
  have hbase : (2000 * (n + L + 1) ^ 6 : ℝ) ≤ D.b ^ 7 := by
    grw [hL, hn]
    exact D.le_of_hasLogBound
  have hb : 1 ≤ D.b ^ 7 := D.le_of_hasLogBound
  calc _ ≤ 2 ^ (3 * 1) * (D.b ^ 7) ^ (2 * n ^ 2) * 2 ^ (10 * n ^ 3) := by grw [hbase]; norm_num
    _ ≤ 2 ^ (3 * D.t ^ 3) * (D.b ^ 7) ^ (2 * D.t ^ 2) * 2 ^ (10 * D.t ^ 3) := by
        gcongr
        exacts [one_le_two, Nat.one_le_pow _ _ D.t_odd.pos, one_le_two]
    _ = _ := by ring

/-- Let `D` be admissible data, with weight `b = D.b`, rank step `t = D.t`, number `f = D.f` of
infinite places and `n_* = nStar D = 2 f t³`. Then the tail bound `B = 2 ^ (13 t³) b ^ (14 t²)` of
`integrable_tail_and_integral_le` satisfies `2 ^ (6 n_*) B ^ f ≤ b ^ n_*`. -/
lemma two_pow_mul_pow_f_le_b_pow_nStar {P : Parameters} (D : Data P) :
    2 ^ (6 * nStar D) * (2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2)) ^ D.f ≤ D.b ^ nStar D := by
  have hb : 1 ≤ D.b := D.le_of_hasLogBound
  have hb_large : 2 ^ 25 ≤ D.b := D.le_of_hasLogBound
  have ht : 14 ≤ D.t := D.nat_le_of_hasLogBound
  calc _ = (2 ^ 25) ^ (D.f * D.t ^ 3) * D.b ^ (D.f * (14 * D.t ^ 2)) := by
        rw [← pow_mul]
        ring
    _ ≤ D.b ^ (D.f * D.t ^ 3) * D.b ^ (D.f * (D.t * D.t ^ 2)) := by gcongr
    _ = _ := by ring

variable {P : Parameters} {D : Data P} {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
  {s : n → ℤˣ} {o : n → ℤ} {u u' : D.Φ → n → ℤ}

attribute [fun_prop] IsHolOfWeight IsHolOfWeight.continuous

omit [DecidableEq n] [Nonempty n] in
/-- For admissible data `D` and rank `n ≤ t = D.t` we have `2 n³ ≤ n_*`,
where `n_* = nStar D = 2 f t³`, since there are `f ≥ 1` infinite places. -/
lemma two_mul_card_pow_three_le_nStar (h_rank : card n ≤ D.t) : 2 * card n ^ 3 ≤ nStar D :=
  (by gcongr : 2 * card n ^ 3 ≤ 2 * D.t ^ 3).trans (Nat.le_mul_of_pos_left _ card_pos)

omit [DecidableEq n] in
/-- In rank `n ≥ 1` the order of decay `10 n³` exceeds `8 n²`, the threshold for integrability on
`U(diag s)`. -/
lemma eight_mul_card_sq_lt : 8 * card n ^ 2 < 10 * card n ^ 3 := by
  linarith [Nat.pow_le_pow_right (card_pos (α := n)) (Nat.le_succ 2),
    Nat.pow_pos (n := 2) (card_pos (α := n))]

/-- In rank `1 ≤ n ≤ t = D.t` let the order `o` put the signs `+1` first, and let the weight `v` be
dominant within each sign block, with gap `300 n_*` between the blocks, `n_* = nStar D`. Let
`2 ρ = twoRho (-o) ⊤`, with entries `#{j | o i < o j} - #{j | o j < o i}`. Then `l = 2 v + 2 ρ` is a
doubled Harish-Chandra parameter of gap `500 n³ + 8 n_*`, and its discrete series coefficient
`dsCoeff` is `holMinors s v`: the quotient `m_{v+c} / m_c` of products of principal minors, where
`c i = 2 ∑ |v j|` at a sign `+1` and `c i = 0` otherwise. -/
lemma hasLargeGap_and_dsCoeff_eq_holMinors (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    {v : n → ℤ} (hv_dom : IsKDominant s o v) (hv_gap : HasHolGap s v (300 * nStar D)) :
    let l : HCParam s := 2 * v + twoRho (-o) ⊤
    l.HasLargeGap (8 * nStar D) ∧ ∀ g : USign s, l.dsCoeff g = holMinors s v g := by
  have hgap : 500 * card n ^ 3 + 8 * nStar D + card n + 1 < 300 * nStar D := by
    linarith [two_mul_card_pow_three_le_nStar h_rank, Nat.le_self_pow three_ne_zero (card n),
      Fintype.card_pos (α := n)]
  exact dsCoeff_eq_holMinors ho (8 * nStar D) (300 * nStar D) v hv_dom hv_gap hgap

/-- Let `D` be admissible data, `b = D.b`, `t = D.t`, and let the rank satisfy `1 ≤ n ≤ t`. For an
integer function `o` on the indices let `2 ρ = twoRho (-o) ⊤`, with entries
`#{j | o i < o j} - #{j | o j < o i}`. Let `l = 2 v + 2 ρ` be a doubled Harish-Chandra parameter of
gap `500 n³ + gap`, with `|v i| ≤ 5 b` for all `i`. Then the tail `deg(l) (2 / ‖g‖) ^ (10 n³)`, with
`deg` the formal degree, is integrable on `U(diag s)`, with integral at most
`2 ^ (13 t³) b ^ (14 t²)`. -/
lemma integrable_tail_and_integral_le (h_rank : card n ≤ D.t) {v : n → ℤ} {l : HCParam s}
    {gap : ℕ} (hl : l = 2 * v + twoRho (-o) ⊤) (hl_gap : l.HasLargeGap gap)
    (hv_le : ∀ i : n, |(v i : ℝ)| ≤ 5 * D.b) :
    let tail (g : USign s) : ℝ := l.formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ (10 * card n ^ 3)
    Integrable tail ∧ ∫ g : USign s, tail g ≤ 2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2) := by
  intro tail
  let L : ℕ := 2 * ⌊5 * D.b⌋₊ + card n
  have hl_le (i : n) : |l i| ≤ L := by
    have hv_floor : (v i).natAbs ≤ ⌊5 * D.b⌋₊ := Nat.le_floor (by simpa using hv_le i)
    have hρ : |twoRho (-o) ⊤ i| ≤ card n := abs_twoRho_le ⊤ i (-o)
    calc |l i| = |2 * v i + twoRho (-o) ⊤ i| := by simp [hl]
      _ ≤ 2 * (v i).natAbs + |twoRho (-o) ⊤ i| := (abs_add_le _ _).trans_eq (by simp)
      _ ≤ L := by lia
  have hL : (L : ℝ) ≤ 2 * (5 * D.b) + D.t := by
    push_cast [L]
    grw [Nat.floor_le (by positivity), h_rank]
  obtain ⟨hint, hle⟩ : Integrable tail ∧ ∫ g : USign s, tail g ≤
      8 * (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * 2 ^ (10 * card n ^ 3) :=
    integral_tail_le (hg := hl_gap) hl_le (10 * card n ^ 3) eight_mul_card_sq_lt
  exact ⟨hint, hle.trans (D.eight_mul_pow_mul_two_pow_le h_rank hL)⟩

/-- In rank `1 ≤ n ≤ t = D.t` let the order `o` put the signs `+1` first, and let the weights `u' τ`
be dominant within each sign block, with gap `300 n_*` between the blocks, `n_* = nStar D`. Then
`|m_u'(h)| |h| ^ (6 n_*) ≤ 2 ^ (6 n_*) ∏_τ (2 / ‖h τ‖) ^ (10 n³)` for `h` in the archimedean group
`GInf D.E s`. Here `τ` runs over the infinite places, `m_u' = holMinorsPi s u'` is the product
over `τ` of the quotients of minors `holMinors s (u' τ)`, and `|h| = maxOpNorm h` is the largest
of the operator norms `‖h τ‖`. -/
lemma norm_holMinorsPi_mul_pow_le (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D)) (h : GInf D.E s) :
    ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D) ≤
      2 ^ (6 * nStar D) * ∏ τ : D.Φ, (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3) := by
  -- Use `6 n_*` more powers of decay at a place `a` of largest norm.
  obtain ⟨a, ha⟩ : ∃ a : D.Φ, ‖(h a : Matrix n n ℂ)‖ = maxOpNorm h := (IsGreatest.pi_norm _).1
  have ha_ne : ‖(h a : Matrix n n ℂ)‖ ≠ 0 := (one_pos.trans_le (U.one_le_norm (h a))).ne'
  have hdecay (τ : D.Φ) : ‖holMinors s (u' τ) (h τ)‖ ≤
      (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3 + if τ = a then 6 * nStar D else 0) := by
    let l : HCParam s := 2 * u' τ + twoRho (-o) ⊤
    obtain ⟨hgap, hcoeff⟩ : l.HasLargeGap (8 * nStar D) ∧
        ∀ g : USign s, l.dsCoeff g = holMinors s (u' τ) g :=
      hasLargeGap_and_dsCoeff_eq_holMinors h_rank ho (hu'_dom τ) (hu'_gap τ)
    rw [← hcoeff]
    exact norm_dsCoeff_le_pow hgap (by lia) (h τ)
  calc ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)
      ≤ (∏ τ, (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3 + if τ = a then 6 * nStar D else 0)) *
          ‖(h a : Matrix n n ℂ)‖ ^ (6 * nStar D) := by
        grw [holMinorsPi, norm_prod, hdecay, ha]
    _ = (∏ τ, (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3)) *
          (2 / ‖(h a : Matrix n n ℂ)‖ * ‖(h a : Matrix n n ℂ)‖) ^ (6 * nStar D) := by
        simp only [pow_add, prod_mul_distrib, pow_ite, pow_zero, Fintype.prod_ite_eq', mul_pow,
          mul_assoc]
    _ = _ := by rw [div_mul_cancel₀ _ ha_ne, mul_comm]

/-- In rank `1 ≤ n ≤ t = D.t` let the order `o` put the signs `+1` first, and let the weights `u τ`
be dominant within each sign block, with gap `300 n_*` between the blocks, `n_* = nStar D`. Then
`|m_u(h)| |h| ^ (6 n_*)` is integrable on `GInf D.E s`, the product of the groups `U(diag s)` over
the infinite places `τ` of `D.E`. Here `m_u = holMinorsPi s u` is the product over `τ` of the
quotients of minors `holMinors s (u τ)` of weight `u τ`, and `|h| = maxOpNorm h` is the largest of
the operator norms `‖h τ‖`. -/
lemma integrable_norm_holMinorsPi_mul_pow (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D)) :
    Integrable fun h : GInf D.E s ↦ ‖holMinorsPi s u h‖ * maxOpNorm h ^ (6 * nStar D) := by
  have hcont : Continuous (holMinorsPi s u) := (isHolOfWeight_holMinorsPi ho hu_dom).continuous
  have hdom_int : Integrable fun h : GInf D.E s ↦
      2 ^ (6 * nStar D) * ∏ τ : D.Φ, (2 / ‖(h τ : Matrix n n ℂ)‖) ^ (10 * card n ^ 3) :=
    (Integrable.fintype_prod fun _ ↦ integrable_two_div_norm_pow eight_mul_card_sq_lt).const_mul _
  exact hdom_int.mono' (by fun_prop) (.of_forall fun h ↦ by
    simpa [abs_of_nonneg] using norm_holMinorsPi_mul_pow_le h_rank ho hu_dom hu_gap h)

omit [Nonempty n] in
/-- If the factor `holMinors s (u τ)` of `m_u = holMinorsPi s u` is the discrete series coefficient
of parameter `l τ` at every infinite place `τ`, then `∫ |m_u|²` is the inverse of the product of
the formal degrees of the `l τ`. -/
lemma integral_norm_holMinorsPi_sq_eq_inv_prod {l : D.Φ → HCParam s}
    (hl_coeff : ∀ (τ : D.Φ) (g : USign s), (l τ).dsCoeff g = holMinors s (u τ) g) :
    ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 = (∏ τ : D.Φ, (l τ).formalDegree)⁻¹ := by
  simp [holMinorsPi, HCParam.formalDegree, prod_pow, ← integral_fintype_prod_volume_eq_prod,
    hl_coeff]

/-- In rank `1 ≤ n ≤ t = D.t` let the order `o` put the signs `+1` first, and let the weights `u τ`
be dominant within each sign block, with gap `300 n_*` between the blocks, `n_* = nStar D`. Then
`∫ |m_u|² > 0`, with the integral over `GInf D.E s`, the product of the groups `U(diag s)` over
the infinite places `τ` of `D.E`. Here `m_u = holMinorsPi s u` is the product over `τ` of the
quotients of minors `holMinors s (u τ)` of weight `u τ`. -/
lemma integral_norm_holMinorsPi_sq_pos (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D)) :
    0 < ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 := by
  let l (τ : D.Φ) : HCParam s := 2 * u τ + twoRho (-o) ⊤
  obtain ⟨hl_gap, hl_coeff⟩ : (∀ τ : D.Φ, (l τ).HasLargeGap (8 * nStar D)) ∧
      ∀ (τ : D.Φ) (g : USign s), (l τ).dsCoeff g = holMinors s (u τ) g :=
    forall_and.1 fun τ ↦ hasLargeGap_and_dsCoeff_eq_holMinors h_rank ho (hu_dom τ) (hu_gap τ)
  rw [integral_norm_holMinorsPi_sq_eq_inv_prod hl_coeff]
  exact inv_pos.2 (prod_pos fun τ _ ↦ formalDegree_pos (hl_gap τ))

/-- Let `D` be admissible data, `b = D.b`, `t = D.t`, `n_* = nStar D`, and let the rank satisfy
`1 ≤ n ≤ t`. Let the order `o` put the signs `+1` first. Let the weights `u τ`, `u' τ` at the
infinite places `τ` be dominant within each sign block, with gap `300 n_*` between the blocks, and
let `u` have entries of modulus at most `5 b`. Write `m_u = holMinorsPi s u` for the product of
quotients of minors of weight `u`, and `|h| = maxOpNorm h` for the largest operator norm of `h` at
a place. Then `∫ |m_u|² > 0`, and `|m_u'(h)| |h| ^ (6 n_*)` is integrable with integral at most
`b ^ n_* ∫ |m_u|²`. -/
theorem integral_norm_holMinorsPi_mul_pow_le (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D))
    (hu_le : ∀ (τ : D.Φ) (i : n), |(u τ i : ℝ)| ≤ 5 * D.b) :
    0 < ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 ∧
    Integrable (fun h : GInf D.E s ↦ ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)) ∧
    ∫ h : GInf D.E s, ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D) ≤
      D.b ^ nStar D * ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 := by
  refine ⟨integral_norm_holMinorsPi_sq_pos h_rank ho hu_dom hu_gap,
    integrable_norm_holMinorsPi_mul_pow h_rank ho hu'_dom hu'_gap, ?_⟩
  -- At each place the factors of `m_u` and `m_u'` are discrete series coefficients. So the
  -- integrand is at most `2 ^ (6 n_*) ∫ |m_u|²` times a product of tails
  -- `deg * (2 / ‖g‖) ^ (10 n³)`; the formal degrees are those of `u`, with product `(∫ |m_u|²)⁻¹`.
  let l (τ : D.Φ) : HCParam s := 2 * u τ + twoRho (-o) ⊤
  obtain ⟨hl_gap, hl_coeff⟩ : (∀ τ, (l τ).HasLargeGap (8 * nStar D)) ∧
      ∀ (τ : D.Φ) (g : USign s), (l τ).dsCoeff g = holMinors s (u τ) g :=
    forall_and.1 fun τ ↦ hasLargeGap_and_dsCoeff_eq_holMinors h_rank ho (hu_dom τ) (hu_gap τ)
  let tail (τ : D.Φ) (g : USign s) : ℝ :=
    (l τ).formalDegree * (2 / ‖(g : Matrix n n ℂ)‖) ^ (10 * card n ^ 3)
  obtain ⟨htail_int, htail_le⟩ : (∀ τ : D.Φ, Integrable (tail τ)) ∧
      ∀ τ : D.Φ, ∫ g, tail τ g ≤ 2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2) :=
    forall_and.1 fun τ ↦ integrable_tail_and_integral_le h_rank rfl (hl_gap τ) (hu_le τ)
  set I : ℝ := ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2
  have hI : I = (∏ τ, (l τ).formalDegree)⁻¹ := integral_norm_holMinorsPi_sq_eq_inv_prod hl_coeff
  have hdeg_pos (τ : D.Φ) : 0 < (l τ).formalDegree := formalDegree_pos (hl_gap τ)
  have hbound (h : GInf D.E s) : ‖‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)‖ ≤
      2 ^ (6 * nStar D) * I * ∏ τ, tail τ (h τ) := by
    rw [Real.norm_of_nonneg (by positivity), hI, prod_mul_distrib, mul_assoc,
      inv_mul_cancel_left₀ (prod_pos fun τ _ ↦ hdeg_pos τ).ne']
    exact norm_holMinorsPi_mul_pow_le h_rank ho hu'_dom hu'_gap h
  have hI_pos : 0 < I := integral_norm_holMinorsPi_sq_pos h_rank ho hu_dom hu_gap
  calc _ ≤ ∫ h : GInf D.E s, 2 ^ (6 * nStar D) * I * ∏ τ, tail τ (h τ) :=
        (le_abs_self _).trans (norm_integral_le_of_norm_le
          ((Integrable.fintype_prod htail_int).const_mul _) (.of_forall hbound))
    _ = 2 ^ (6 * nStar D) * (∏ τ, ∫ g, tail τ g) * I := by
        rw [integral_const_mul, integral_fintype_prod_volume_eq_prod, mul_right_comm]
    _ ≤ 2 ^ (6 * nStar D) * (∏ _τ : D.Φ, 2 ^ (13 * D.t ^ 3) * D.b ^ (14 * D.t ^ 2)) * I := by
        gcongr with τ
        exacts [fun τ _ ↦ integral_nonneg fun g ↦ mul_nonneg (hdeg_pos τ).le (by positivity),
          htail_le τ]
    _ ≤ D.b ^ nStar D * I := by grw [prod_const, card_univ, D.two_pow_mul_pow_f_le_b_pow_nStar]

/-- Let `D` be admissible data (`Data P`), `b = D.b`, `t = D.t`, `n_* = nStar D`, and let the index
type `n` be nonempty with `card n ≤ t`. Let `s` be signs and let the order `o` put the indices of
sign `+1` first. Let the weights `u`, `u'` be K-dominant for `o` within each sign block, with gap
`300 n_*` between the blocks, and let the entries of `u` be at most `5 b` in modulus. Write
`m_u = holMinorsPi s u` and `|h| = maxOpNorm h` for `h` in `GInf D.E s`. If `A` is continuous on
`GInf D.E s` and `|A h| ≤ C |h| ^ (6 n_*)`, then `A m_u'` is integrable and
`|∫ A m_u'| ≤ C b ^ n_* ∫ |m_u|²`. -/
theorem integrable_mul_holMinorsPi (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D))
    (hu_le : ∀ (τ : D.Φ) (i : n), |(u τ i : ℝ)| ≤ 5 * D.b)
    {A : GInf D.E s → ℂ} {C : ℝ} (hA : Continuous A)
    (hA_le : ∀ h : GInf D.E s, ‖A h‖ ≤ C * maxOpNorm h ^ (6 * nStar D)) :
    Integrable (A * holMinorsPi s u') ∧
    ‖∫ h : GInf D.E s, A h * holMinorsPi s u' h‖ ≤
      C * D.b ^ nStar D * ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 := by
  obtain ⟨-, hint, hle⟩ : 0 < ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 ∧
      Integrable (fun h : GInf D.E s ↦ ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)) ∧
      ∫ h : GInf D.E s, ‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D) ≤
        D.b ^ nStar D * ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 :=
    integral_norm_holMinorsPi_mul_pow_le h_rank ho hu_dom hu'_dom hu_gap hu'_gap hu_le
  have hC : 0 ≤ C := by simpa [maxOpNorm] using (norm_nonneg _).trans (hA_le 1)
  have hcont : Continuous (holMinorsPi s u') := (isHolOfWeight_holMinorsPi ho hu'_dom).continuous
  have hbound (h : GInf D.E s) : ‖A h * holMinorsPi s u' h‖ ≤
      C * (‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)) := by
    grw [norm_mul, hA_le, mul_assoc, mul_comm (maxOpNorm h ^ _)]
  refine ⟨(hint.const_mul C).mono' (by fun_prop) (.of_forall hbound), ?_⟩
  calc _ ≤ ∫ h : GInf D.E s, C * (‖holMinorsPi s u' h‖ * maxOpNorm h ^ (6 * nStar D)) :=
        norm_integral_le_of_norm_le (hint.const_mul C) (.of_forall hbound)
    _ ≤ _ := by grw [integral_const_mul, hle, mul_assoc]

/-- Let `D : Data P`, `t = D.t`, `n_* = nStar D`, and let the rank satisfy `1 ≤ n ≤ t`. Let the
order `o` put the signs `+1` first, and let the weights `u τ` be dominant within each sign block,
with gap `300 n_*` between the blocks. Then `holMinorsPi s u`, the product of quotients of minors of
weight `u`, is integrable. -/
theorem integrable_holMinorsPi (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D)) :
    Integrable (holMinorsPi s u) := by
  have hbound (h : GInf D.E s) :
      ‖holMinorsPi s u h‖ ≤ ‖holMinorsPi s u h‖ * maxOpNorm h ^ (6 * nStar D) :=
    le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (one_le_maxOpNorm h))
  exact (integrable_norm_holMinorsPi_mul_pow h_rank ho hu_dom hu_gap).mono'
    (isHolOfWeight_holMinorsPi ho hu_dom).continuous.aestronglyMeasurable (.of_forall hbound)

/-- Let `D` be admissible data, `b = D.b`, `t = D.t`, `n_* = nStar D`, and let the rank satisfy
`1 ≤ n ≤ t`. Let the order `o` put the signs `+1` first, let the weights `u`, `u'` be dominant
within each sign block with gap `300 n_*` between the blocks, the entries of `u` at most `5 b` in
modulus. Write `m_u = holMinorsPi s u` and `|h| = maxOpNorm h`. Let `W`, `K`, `K'` be continuous,
`|W| ≤ M`, and `K`, `K'` both within `δ |h| ^ (6 n_*)` of a function `K₀`. If `∫ W K' m_u' = 0` and
`K m_u' W` is integrable, then `|∫ K m_u' W| ≤ 2 δ M b ^ n_* ∫ |m_u|²`. -/
lemma norm_integral_mul_holMinorsPi_mul_le (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D))
    (hu_le : ∀ (τ : D.Φ) (i : n), |(u τ i : ℝ)| ≤ 5 * D.b)
    {W K K' K₀ : GInf D.E s → ℂ} {M δ : ℝ} (hW : Continuous W) (hK : Continuous K)
    (hK' : Continuous K') (hW_le : ∀ h : GInf D.E s, ‖W h‖ ≤ M)
    (hK_close : ∀ h : GInf D.E s, ‖K h - K₀ h‖ ≤ δ * maxOpNorm h ^ (6 * nStar D))
    (hK'_close : ∀ h : GInf D.E s, ‖K' h - K₀ h‖ ≤ δ * maxOpNorm h ^ (6 * nStar D))
    (h_orth : ∫ h : GInf D.E s, W h * K' h * holMinorsPi s u' h = 0)
    (h_int : Integrable fun h : GInf D.E s ↦ (K * holMinorsPi s u') h * W h) :
    ‖∫ h : GInf D.E s, (K * holMinorsPi s u') h * W h‖ ≤
      2 * δ * M * D.b ^ nStar D * ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 := by
  -- Orthogonality lets us replace `K` by the small function `K - K'`.
  have hM : 0 ≤ M := (norm_nonneg _).trans (hW_le 1)
  have hdiff_le (h : GInf D.E s) :
      ‖(W * (K - K')) h‖ ≤ 2 * δ * M * maxOpNorm h ^ (6 * nStar D) :=
    calc ‖W h * (K h - K' h)‖ ≤ M * (‖K h - K₀ h‖ + ‖K' h - K₀ h‖) := by
          grw [norm_mul, hW_le, norm_sub_le_norm_sub_add_norm_sub _ (K₀ h), norm_sub_rev (K₀ h)]
      _ ≤ M * (δ * maxOpNorm h ^ (6 * nStar D) + δ * maxOpNorm h ^ (6 * nStar D)) := by
          grw [hK_close, hK'_close]
      _ = _ := by ring
  obtain ⟨hdiff_int, hdiff⟩ : Integrable (W * (K - K') * holMinorsPi s u') ∧
      ‖∫ h, (W * (K - K')) h * holMinorsPi s u' h‖ ≤
        2 * δ * M * D.b ^ nStar D * ∫ h, ‖holMinorsPi s u h‖ ^ 2 :=
    integrable_mul_holMinorsPi h_rank ho hu_dom hu'_dom hu_gap hu'_gap hu_le
      (hW.mul (hK.sub hK')) hdiff_le
  have hsub : ∫ h, (K * holMinorsPi s u') h * W h - (W * (K - K') * holMinorsPi s u') h = 0 :=
    (integral_congr_ae (.of_forall fun h ↦ by simp; ring)).trans h_orth
  rw [integral_sub h_int hdiff_int, sub_eq_zero] at hsub
  rwa [hsub]

omit [Nonempty n] in
/-- Let the order `o` put the signs `+1` first, let `u` be dominant within each sign block, write
`m_u = holMinorsPi s u`, and let `f` be holomorphic of weight `u`: it extends analytically to
products with `o`-triangular matrices, on which it transforms by the character `u`. Let `W θ` be a
family of functions on the group whose mean over the circle is the conjugate of `c m_u`, with
`c ≠ 0`. If `f(h) W θ h` is jointly integrable and `|∫ f W θ| ≤ B` whenever this integral converges,
then `(∫ |m_u|²) |f 1| |c| ≤ B`. -/
lemma integral_mul_norm_apply_one_mul_le (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) {f : GInf D.E s → ℂ} (hf : IsHolOfWeight s o u f)
    {W : UnitAddCircle → GInf D.E s → ℂ} {c : ℂ} {B : ℝ} (hc : c ≠ 0)
    (hW_mean : ∀ h : GInf D.E s,
      ∫ θ : UnitAddCircle, W θ h = starRingEnd ℂ (holMinorsPi s u h * c))
    (h_int : Integrable (Function.uncurry fun (θ : UnitAddCircle) (h : GInf D.E s) ↦ f h * W θ h)
      (volume.prod volume))
    (h_le : ∀ θ : UnitAddCircle, Integrable (fun h : GInf D.E s ↦ f h * W θ h) →
      ‖∫ h : GInf D.E s, f h * W θ h‖ ≤ B) :
    (∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2) * ‖f 1‖ * ‖c‖ ≤ B := by
  -- Exchange the integrals over `θ` and `h`, then use the reproducing formula for `f`.
  set I : ℝ := ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2 with hI
  have hI_nonneg : 0 ≤ I := integral_nonneg fun h ↦ sq_nonneg _
  let A (h : GInf D.E s) : ℂ := f h * starRingEnd ℂ (holMinorsPi s u h)
  have hA (h : GInf D.E s) : ∫ θ, f h * W θ h = A h * starRingEnd ℂ c := by
    rw [integral_const_mul, hW_mean, map_mul, ← mul_assoc]
  have hA_int : Integrable A := by
    simpa [hA, integrable_mul_const_iff, hc] using h_int.integral_prod_right
  have hrepr : ∫ h, A h = I * f 1 := by
    simpa [A, ← hI] using hf.integral_mul_conj_holMinorsPi ho hu_dom hA_int
  calc _ = ‖∫ h, ∫ θ, f h * W θ h‖ := by
        simp [hA, integral_mul_const, hrepr, abs_of_nonneg hI_nonneg]
    _ = ‖∫ θ, ∫ h, f h * W θ h‖ := by rw [integral_integral_swap h_int]
    _ ≤ B * (volume : Measure UnitAddCircle).real .univ :=
        norm_integral_le_of_norm_le_const (h_int.prod_right_ae.mono h_le)
    _ = B := by simp [Measure.real]

/-- Let `D` be admissible data (`Data`), of which only these are used: the CM field `E = D.E`, the
set `D.Φ` of its `f` infinite places `τ`, the number `t = D.t`, the weight `b = D.b`, which is very
large against `t`, and `n_* = nStar D = 2 f t³`. For signs `s` on `n` indices, `1 ≤ n ≤ t`, the
group `GInf D.E s` is the product of the groups `U(diag s)` over `τ`, with its Haar measure `dh`,
and `G D.E s` is its product with the finite adelic unitary group. Let the order `o` put the signs
`+1` first. Let the weights `u τ`, `u' τ` be dominant within each sign block, with entries at the
sign `-1` larger by at least `300 n_*` than those at the sign `+1` (`HasHolGap`), and let `u` have
entries of modulus at most `5 b`. Write `m_u' = holMinorsPi s u'` for the product over `τ` of the
quotients of principal minors `holMinors s (u' τ)`, and `|h| = maxOpNorm h` for the largest operator
norm of `h` at a place.

Let `F` on `G D.E s` be continuous and holomorphic of weight `u` in the archimedean variable, with a
peak `z` (`F` is bounded and `|F z|` exceeds half of `sup |F|`), and let `K₀` be bounded. Suppose
that at every peak `x` we have `∫ conj F(x h) K(h) m_u'(h) dh = 0` for some `K` that is holomorphic
of weight `u - u'` and has `|K h - K₀ h| ≤ δ |h| ^ (6 n_*)`. Then `|K₀ 1| ≤ (4 b ^ n_* + 1) δ`. -/
theorem norm_apply_one_le_of_forall_isPeak (h_rank : card n ≤ D.t) (ho : IsPosFirstOrder s o)
    (hu_dom : ∀ τ : D.Φ, IsKDominant s o (u τ)) (hu'_dom : ∀ τ : D.Φ, IsKDominant s o (u' τ))
    (hu_gap : ∀ τ : D.Φ, HasHolGap s (u τ) (300 * nStar D))
    (hu'_gap : ∀ τ : D.Φ, HasHolGap s (u' τ) (300 * nStar D))
    (hu_le : ∀ (τ : D.Φ) (i : n), |(u τ i : ℝ)| ≤ 5 * D.b)
    {F : New.G D.E s → ℂ} {z : New.G D.E s} {K₀ : GInf D.E s → ℂ} {C δ : ℝ}
    (hF : Continuous F) (hF_hol : IsAdelicHol o u F) (hz : IsPeak F z)
    (hK₀_le : ∀ h : GInf D.E s, ‖K₀ h‖ ≤ C)
    (h_orth : ∀ x : New.G D.E s, IsPeak F x → ∃ K : GInf D.E s → ℂ,
      IsHolOfWeight s o (u - u') K ∧
      (∀ h : GInf D.E s, ‖K h - K₀ h‖ ≤ δ * maxOpNorm h ^ (6 * nStar D)) ∧
      ∫ h : GInf D.E s, star (F (x * (h, 1))) * K h * holMinorsPi s u' h = 0) :
    ‖K₀ 1‖ ≤ (4 * D.b ^ nStar D + 1) * δ := by
  -- Rotate `z` by a circle `rot θ`: all `z * rot θ` are peaks, so `h_orth` gives functions `K θ`.
  -- Replacing `K θ` by `K 0` has a small cost, the mean over `θ` turns the translate of `F` into
  -- `F z * m_u`, and the reproducing formula evaluates the integral.
  set I : ℝ := ∫ h : GInf D.E s, ‖holMinorsPi s u h‖ ^ 2
  have hI_pos : 0 < I := integral_norm_holMinorsPi_sq_pos h_rank ho hu_dom hu_gap
  let rot (θ : UnitAddCircle) : GInf D.E s := fun _ ↦ diagTorus s fun i ↦ θ.toCircle ^ o i
  have hpeak (θ : UnitAddCircle) : IsPeak F (z * (rot θ, 1)) := by
    have hF_rot : F (z * (rot θ, 1)) = (∏ τ, ∏ i, (↑(θ.toCircle ^ o i) : ℂ) ^ u τ i) * F z := by
      simpa [Prod.mk_one_one] using (hF_hol z).apply_mul_diagTorus 1 fun i ↦ θ.toCircle ^ o i
    exact hz.of_norm_le (by simp [hF_rot, Circle.norm_coe])
  have hK (θ : UnitAddCircle) : ∃ K : GInf D.E s → ℂ, IsHolOfWeight s o (u - u') K ∧
      (∀ h, ‖K h - K₀ h‖ ≤ δ * maxOpNorm h ^ (6 * nStar D)) ∧
      ∫ h, star (F (z * (rot θ, 1) * (h, 1))) * K h * holMinorsPi s u' h = 0 :=
    h_orth (z * (rot θ, 1)) (hpeak θ)
  choose K hK_hol hK_close hK_orth using hK
  -- `W θ` is the conjugate of the quotient of the rotated translate of `F` by the character.
  let W (θ : UnitAddCircle) (h : GInf D.E s) : ℂ :=
    starRingEnd ℂ (F (z * (rot θ * h, 1)) * ∏ τ, ∏ i, ↑((θ.toCircle ^ o i) ^ u τ i)⁻¹)
  have hW_orth (θ : UnitAddCircle) : ∫ h, W θ h * K θ h * holMinorsPi s u' h = 0 :=
    calc _ = ∫ h, star (F (z * (rot θ, 1) * (h, 1))) * K θ h * holMinorsPi s u' h *
          starRingEnd ℂ (∏ τ, ∏ i, ↑((θ.toCircle ^ o i) ^ u τ i)⁻¹) := by
          congr with h
          simp [W, mul_assoc z]
          ring
      _ = 0 := by rw [integral_mul_const, hK_orth, zero_mul]
  -- As `h ↦ F (z h)` is holomorphic of weight `u`, this quotient has circle mean `m_u * F z`.
  have hW_mean (h : GInf D.E s) : ∫ θ, W θ h = starRingEnd ℂ (holMinorsPi s u h * F z) := by
    rw [← mul_one z, ← Prod.mk_one_one, ← (hF_hol z).circle_mean_holMinorsPi ho hu_dom h,
      integral_conj]
  have hW_le (θ : UnitAddCircle) (h : GInf D.E s) : ‖W θ h‖ ≤ 2 * ‖F z‖ := by
    simpa [W, Circle.norm_coe] using hz.norm_le (z * (rot θ * h, 1))
  have hK_le (h : GInf D.E s) : ‖K 0 h‖ ≤ (C + δ) * maxOpNorm h ^ (6 * nStar D) := by
    grw [norm_le_insert' _ (K₀ h), hK_close, hK₀_le, add_mul,
      ← le_mul_of_one_le_right ((norm_nonneg _).trans (hK₀_le h))
        (one_le_pow₀ (one_le_maxOpNorm h))]
  have hK_int : Integrable (K 0 * holMinorsPi s u') :=
    (integrable_mul_holMinorsPi h_rank ho hu_dom hu'_dom hu_gap hu'_gap hu_le
      (hK_hol 0).continuous hK_le).1
  have hprod_int : Integrable
      (Function.uncurry fun θ h ↦ (K 0 * holMinorsPi s u') h * W θ h) (volume.prod volume) :=
    (hK_int.comp_snd volume).mul_bdd (g := W.uncurry) (by fun_prop)
      (.of_forall fun x ↦ hW_le x.1 x.2)
  have hslice (θ : UnitAddCircle) (hθ : Integrable fun h ↦ (K 0 * holMinorsPi s u') h * W θ h) :
      ‖∫ h, (K 0 * holMinorsPi s u') h * W θ h‖ ≤ 2 * δ * (2 * ‖F z‖) * D.b ^ nStar D * I :=
    norm_integral_mul_holMinorsPi_mul_le h_rank ho hu_dom hu'_dom hu_gap hu'_gap hu_le
      (by fun_prop) (hK_hol 0).continuous (hK_hol θ).continuous (hW_le θ) (hK_close 0) (hK_close θ)
      (hW_orth θ) hθ
  -- `K 0 * m_u'` is holomorphic of weight `u`, and its value at `1` is `K 0 1`.
  have hhol : IsHolOfWeight s o u (K 0 * holMinorsPi s u') := by
    simpa using (hK_hol 0).mul ho.1 (isHolOfWeight_holMinorsPi ho hu'_dom)
  have h_le : I * ‖K 0 1‖ * ‖F z‖ ≤ 2 * δ * (2 * ‖F z‖) * D.b ^ nStar D * I := by
    simpa using
      integral_mul_norm_apply_one_mul_le ho hu_dom hhol hz.ne_zero hW_mean hprod_int hslice
  have hK_one : ‖K 0 1‖ ≤ 4 * δ * D.b ^ nStar D :=
    le_of_mul_le_mul_right (by linarith) (mul_pos hI_pos (norm_pos_iff.2 hz.ne_zero))
  have hK_diff : ‖K 0 1 - K₀ 1‖ ≤ δ := by simpa [maxOpNorm] using hK_close 0 1
  linarith [norm_le_insert (K 0 1) (K₀ 1)]

end New.Data

end Isolation
