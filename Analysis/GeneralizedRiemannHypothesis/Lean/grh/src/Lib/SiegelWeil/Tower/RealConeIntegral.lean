import Lib.SiegelWeil.SingularForms.UnimodularCoefficients
import Lib.SiegelWeil.Tower.PrincipalIdeles
import Lib.Weil.MixedModel.Slices

/-!
# The real cone integral

The archimedean Tate integral of a Fock vector over the cone of real isotropic vectors of
`V' = V ⊕ H`, and its convergence in every moment for positive real exponents.

Throughout, `A` and `X` split a hyperbolic plane off `W'` and `V'`, with complements `W` and `V`.

* `PairFock E s t` is the Fock space of `Hom(W, V)` at the infinite places, the type
  `fockSpace (realSigns E (homSigns s t))` that `coneIntegrand` takes values in.
* `lineTermReal A X β a` maps the Fock space of `Hom(W', V')` to that of `Hom(W, V)`; it is the
  archimedean part of the term at `a` in Poisson's formula on the line, on the side that the Boolean
  `β` names.
* `fockMoment N v = ∫ (1 + ‖y‖) ^ N ‖v y‖ dy` is the `N`-th moment of `v`, and `IsSchwartzVector v`
  says that all moments of `v` are finite.

## Relation to the literature

Known; see `Lib.SiegelWeil.Tower.LargeSideConstantTerm` for sources.
-/

noncomputable section

namespace New.Exchange

open Matrix NumberField MeasureTheory Measure Fock Fintype Finset Real ENNReal Space
variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r r' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} {W : Space E n s} {W' : Space E n' s'}
  {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)
  [IsBaseAdapted A] [IsBaseAdapted X] (μ : InfinitePlace E → ℤ)

/-- The idele with archimedean component `a` and finite component `1`. -/
abbrev realIdele (a : (InfinitePlace E → ℂ)ˣ) : (𝔸 E)ˣ :=
  a.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E))

omit [WeilData E] in
/-- The idele norm of the idele with archimedean component `a` and finite component `1` is
`∏ w, ‖a w‖ ^ 2`. -/
lemma ideleAbs_realIdele_eq_prod (a : (InfinitePlace E → ℂ)ˣ) :
    ideleAbs (realIdele a) = ∏ w : InfinitePlace E, ‖a.val w‖ ^ 2 := by
  simp [ideleAbs]

omit [WeilData E] in
lemma continuous_ideleAbs_realIdele :
    Continuous fun a : (InfinitePlace E → ℂ)ˣ ↦ ideleAbs (realIdele a) :=
  continuous_ideleAbs.comp ((Continuous.prodMk_left (Y := 𝔸f E) 1).units_map _)

/-- The integrand of the cone integral at `p = (k, a)`, with `k` in the maximal compact subgroup of
`U(V')`: the line term `lineTermReal A X β a` of `k v`, times the character
`∏ w, (a w / |a w|) ^ (2 μ w)` and the power `z` of the idele norm of `a`. Here `k` acts through its
archimedean component, as the element `(1, k)` of `U(W') × U(V')` in the Weil representation with
weight `targetWeight n' μ` on `U(V')` and `0` on `U(W')`. The two values of `β` give the terms on
the two sides of Poisson's formula on the line (`tsum_lineTerm`). -/
def coneIntegrand (β : Bool) (z : ℝ) (v : PairFock E s' t')
    (p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) : fockSpace (realSigns E (homSigns s t)) :=
  ((∏ w : InfinitePlace E, (p.2.val w / ‖p.2.val w‖) ^ (2 * μ w)) *
      (ideleAbs (realIdele p.2) ^ z : ℝ)) •
    lineTermReal A X β p.2 (realPairWeil (targetWeight n' μ) 0 (1, (p.1 : G E t').1) v)

/-- The cone integral: the real Tate integral of `v`, with exponent `z`, over the cone of the
isotropic vectors `k⁻¹ x a`, where `x` spans the isotropic line `X.k` of `V'`, `k` runs over the
maximal compact subgroup of `U(V')` and `a` over the archimedean ideles `(E ⊗ ℝ)ˣ`. -/
def cone (z : ℝ) (v : PairFock E s' t') : PairFock E s t :=
  ∫ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ, coneIntegrand A X μ true z v p ∂haar.prod haar

/-- The cone integral formed with the terms on the other side of Poisson's formula on the line. -/
def dualCone (z : ℝ) (v : PairFock E s' t') : PairFock E s t :=
  ∫ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ, coneIntegrand A X μ false z v p ∂haar.prod haar

/-- For `z > 0` the function `y ^ (2 z) (1 + log² y)` of `y > 0` is at most a constant times a power
of `1 + y`. -/
lemma exists_sq_rpow_mul_one_add_log_sq_le {z : ℝ} (hz : 0 < z) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ y : ℝ, 0 < y →
      (y ^ 2) ^ z * (1 + Real.log y ^ 2) ≤ C * (1 + y) ^ M := by
  let k : ℕ := 2 * ⌈z⌉₊
  refine ⟨1 + z⁻¹ ^ 2, k + 2, by positivity, fun y hy ↦ ?_⟩
  have h_one : (1 : ℝ) ≤ 1 + y := by linarith
  have h_pow : (y ^ 2) ^ z ≤ (1 + y) ^ k := by
    grw [show y ≤ 1 + y by linarith, pow_mul, ← Real.rpow_natCast _ ⌈z⌉₊]
    exact rpow_le_rpow_of_exponent_le (one_le_pow₀ h_one) (Nat.le_ceil z)
  -- For `y ≤ 1` use `|log y * y ^ z| ≤ z⁻¹`, for `y ≥ 1` use `0 ≤ log y ≤ y`.
  have h_log : (y ^ 2) ^ z * Real.log y ^ 2 ≤ z⁻¹ ^ 2 + (1 + y) ^ k * y ^ 2 := by
    obtain h_le | h_ge := le_total y 1
    · have h_small : |Real.log y * y ^ z| ≤ z⁻¹ := by
        simpa using (abs_log_mul_self_rpow_lt y z hy h_le hz).le
      calc (y ^ 2) ^ z * Real.log y ^ 2 = |Real.log y * y ^ z| ^ 2 := by
            rw [sq_abs, mul_pow, mul_comm, ← rpow_pow_comm hy.le]
        _ ≤ z⁻¹ ^ 2 + (1 + y) ^ k * y ^ 2 := le_add_of_le_of_nonneg (by gcongr) (by positivity)
    · refine le_add_of_nonneg_of_le (by positivity) ?_
      gcongr
      exacts [log_nonneg h_ge, log_le_self hy.le]
  calc (y ^ 2) ^ z * (1 + Real.log y ^ 2) ≤ z⁻¹ ^ 2 * 1 + (1 + y) ^ k * (1 + y ^ 2) := by
        linarith [h_pow, h_log]
    _ ≤ z⁻¹ ^ 2 * (1 + y) ^ (k + 2) + (1 + y) ^ k * (1 + y) ^ 2 := by
        gcongr
        exacts [one_le_pow₀ h_one, by nlinarith]
    _ = (1 + z⁻¹ ^ 2) * (1 + y) ^ (k + 2) := by ring

omit [WeilData E] in
/-- For `z > 0` the power `(∏ w, ‖a w‖ ^ 2) ^ z` is at most a power of `1 + ‖a‖` times a constant
multiple of `∏ w, (1 + log² ‖a w‖)⁻¹`, for `a` with nonzero coordinates. -/
lemma exists_prod_norm_sq_rpow_le {z : ℝ} (hz : 0 < z) :
    ∃ (c : ℝ) (M : ℕ), 0 ≤ c ∧ ∀ a : (InfinitePlace E → ℂ)ˣ,
      (∏ w : InfinitePlace E, ‖a.val w‖ ^ 2) ^ z ≤
        (1 + ‖a.val‖) ^ M * (c * ∏ w : InfinitePlace E, (1 + Real.log ‖a.val w‖ ^ 2)⁻¹) := by
  obtain ⟨c, m, hc, h_log⟩ := exists_sq_rpow_mul_one_add_log_sq_le hz
  let d : ℕ := Fintype.card (InfinitePlace E)
  refine ⟨c ^ d, m * d, by positivity, fun a ↦ ?_⟩
  have h_place (w : InfinitePlace E) :
      (‖a.val w‖ ^ 2) ^ z ≤ (1 + ‖a.val‖) ^ m * c * (1 + log ‖a.val w‖ ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    grw [h_log _ (norm_pos_iff.2 (piUnits_val_apply_ne_zero a w)), norm_le_pi_norm, mul_comm]
  rw [← finsetProd_rpow _ _ (by simp) z]
  calc ∏ w, (‖a.val w‖ ^ 2) ^ z ≤ ∏ w, (1 + ‖a.val‖) ^ m * c * (1 + log ‖a.val w‖ ^ 2)⁻¹ := by
        gcongr with w
        exact h_place w
    _ = (1 + ‖a.val‖) ^ (m * d) * (c ^ d * ∏ w, (1 + log ‖a.val w‖ ^ 2)⁻¹) := by
        rw [prod_mul_distrib, prod_const, card_univ, mul_pow, ← pow_mul, mul_assoc]

/-- The line term `lineTermReal A X β a v`, the slice of the Fock vector `v` at the point `a` of the
isotropic line, decays rapidly in `a`, in every moment: `(1 + ‖a‖) ^ M` times its `N`-th moment
`fockMoment N` is at most a finite constant, independent of `a` and `v`, times the `(N + M)`-th
moment of `v`. -/
lemma exists_fockMoment_lineTermReal_le (β : Bool) (N M : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (a : InfinitePlace E → ℂ) (v : PairFock E s' t'),
      (1 + ‖a‖ₑ) ^ M * fockMoment N (lineTermReal A X β a v) ≤ C * fockMoment (N + M) v := by
  -- The bound holds in the mixed model through which `lineTermReal` is defined, at the point `y`
  -- with coordinate `a w` at `(w, .inr _)` and `0` elsewhere.
  obtain ⟨C, hC, h_slice⟩ : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (y : InfinitePlace E × LineIndex n r → ℂ) (v : PairFock E s' t'),
        (1 + ‖y‖ₑ) ^ M * fockMoment N ((isAdapted_lineTermSplitting A X β).mixedModel.slice y v) ≤
          C * fockMoment (N + M) v :=
    (isAdapted_lineTermSplitting A X β).mixedModel.exists_fockMoment_slice_le N M
  refine ⟨C, hC, fun a v ↦ ?_⟩
  let y : InfinitePlace E × LineIndex n r → ℂ := fun p ↦ a p.1 * p.2.isRight.toNat
  have h_norm : ‖a‖ₑ ≤ ‖y‖ₑ :=
    enorm_le_iff_norm_le.2 <| (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun w ↦ by
      simpa [y] using norm_le_pi_norm y (w, .inr 0)
  calc (1 + ‖a‖ₑ) ^ M * fockMoment N (lineTermReal A X β a v)
      ≤ (1 + ‖y‖ₑ) ^ M * fockMoment N (lineTermReal A X β a v) := by grw [h_norm]
    _ ≤ C * fockMoment (N + M) v := by
        rw [lineTermReal]
        exact h_slice y v

/-- The `N`-th moment of the cone integrand at `(k, a)` is `(∏ w, ‖a w‖ ^ 2) ^ z` times the moment
of the line term at `a` of `k v`: the phases and determinants have modulus `1`. On the right the
archimedean component `(k : G E t').1` of `k`, paired with `1 : GInf E s'` on the `W'` side, acts on
`Hom(W', V')` by composition (`pairHomInf`), and on the Fock space by the Weil representation
`realWeil`. -/
lemma fockMoment_coneIntegrand (β : Bool) (z : ℝ) (v : PairFock E s' t') (N : ℕ)
    (k : maxCompact E t') (a : (InfinitePlace E → ℂ)ˣ) :
    fockMoment N (coneIntegrand A X μ β z v (k, a)) =
      ‖(∏ w : InfinitePlace E, ‖a.val w‖ ^ 2) ^ z‖ₑ * fockMoment N
        (lineTermReal A X β a (realWeil (pairHomInf ((1 : GInf E s'), (k : G E t').1)) v)) := by
  simp only [coneIntegrand, realPairWeil_apply_apply, map_smul, smul_smul, fockMoment_smul,
    ideleAbs_realIdele_eq_prod]
  congr 1
  exact enorm_eq_iff_norm_eq.2 (by simp)

/-- Let `A` and `X` be base-adapted splittings, by one hyperbolic plane, of `W'` over `W` and of
`V'` over `V`. For `p = (k, a)`, with `k` in the maximal compact subgroup of `U(V')` and
`a ∈ (InfinitePlace E → ℂ)ˣ`, `coneIntegrand A X μ β z v p` is the line term `lineTermReal A X β a`
of `k v` (`k` acting through the Weil representation), times `∏ w, (a w / |a w|) ^ (2 μ w)` and the
`z`-th power of the idele norm of `a`. For `z > 0` and a Schwartz Fock vector `v` (all moments
`fockMoment N v` finite), there is a function `φ` of `p`, integrable for the product Haar measure,
such that the `N`-th moment of `coneIntegrand A X μ β z v p` is at most `‖φ p‖ₑ` for every `p`. -/
lemma exists_integrable_fockMoment_coneIntegrand_le (β : Bool) {z : ℝ} (hz : 0 < z)
    {v : PairFock E s' t'} (hv : IsSchwartzVector v) (N : ℕ) :
    ∃ φ : maxCompact E t' × (InfinitePlace E → ℂ)ˣ → ℝ, Integrable φ (haar.prod haar) ∧
      ∀ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
        fockMoment N (coneIntegrand A X μ β z v p) ≤ ‖φ p‖ₑ := by
  -- The moment at `(k, a)` is at most a continuous function of `k`, which runs over a compact
  -- group, times `∏ w, (1 + log² ‖a w‖)⁻¹`: the scalar factor grows polynomially in `a` and the
  -- vector decays rapidly.
  obtain ⟨c, M, hc, h_scalar⟩ := exists_prod_norm_sq_rpow_le (E := E) hz
  obtain ⟨C, hC, h_decay⟩ := exists_fockMoment_lineTermReal_le A X β N M
  let L (a : (InfinitePlace E → ℂ)ˣ) : ℝ := c * ∏ w, (1 + log ‖a.val w‖ ^ 2)⁻¹
  have hL : Integrable L haar := integrable_prod_inv_one_add_log_sq.const_mul c
  -- `K k` is `C` times the bound of `fockMoment_realWeil_le` for the moment of `k v`.
  let u (k : maxCompact E t') : USign (realSigns E (homSigns s' t')) :=
    pairHomInf ((1 : GInf E s'), (k : G E t').1)
  let m₀ : ℝ≥0∞ := fockMoment (N + M) (Fock.vacVector : PairFock E s' t')
  open Norms.Operator in
  let K (k : maxCompact E t') : ℝ≥0∞ := C * (‖realMultiplier (u k)‖ₑ *
    ((1 + ‖(u k).val.val‖ₑ) ^ (N + M) * m₀ * fockMoment (N + M) v))
  have hK (k : maxCompact E t') : K k ≠ ⊤ := by
    simp [K, m₀, mul_eq_top, hC, hv (N + M), isSchwartzVector_vacVector (N + M)]
  have hK_cont : Continuous fun k : maxCompact E t' ↦ (K k).toReal := by
    -- In terms of the matrix entries of `k`, the multiplier is a product of minors.
    simp [K, u, toReal_add, pairHomInf, realMultiplier]
    fun_prop [kroneckerMap]
  refine ⟨fun p ↦ (K p.1).toReal * L p.2,
    .mul_prod (DiscreteSeries.integrable_of_compactSpace hK_cont) hL, fun ⟨k, a⟩ ↦ ?_⟩
  have h_enorm : ‖(∏ w, ‖a.val w‖ ^ 2) ^ z‖ₑ ≤ (1 + ‖a.val‖ₑ) ^ M * ‖L a‖ₑ := by
    have h_abs : |(∏ w, ‖a.val w‖ ^ 2) ^ z| ≤ (1 + ‖a.val‖) ^ M * |L a| := by
      simpa (disch := positivity) only [abs_of_nonneg, L] using h_scalar a
    simpa [← toReal_le_toReal, mul_eq_top, toReal_add] using h_abs
  calc fockMoment N (coneIntegrand A X μ β z v (k, a))
      = ‖(∏ w, ‖a.val w‖ ^ 2) ^ z‖ₑ * fockMoment N (lineTermReal A X β a (realWeil (u k) v)) :=
        fockMoment_coneIntegrand A X μ β z v N k a
    _ ≤ (1 + ‖a.val‖ₑ) ^ M * fockMoment N (lineTermReal A X β a (realWeil (u k) v)) *
        ‖L a‖ₑ := by grw [h_enorm, mul_right_comm]
    _ ≤ C * fockMoment (N + M) (realWeil (u k) v) * ‖L a‖ₑ := by grw [h_decay]
    _ ≤ K k * ‖L a‖ₑ := by grw [fockMoment_realWeil_le]
    _ = ‖(K k).toReal * L a‖ₑ := by rw [enorm_mul (K k).toReal, enorm_toReal (hK k)]

/-- For `z > 0` the cone integrand is continuous in `p = (k, a)`. -/
lemma continuous_coneIntegrand (β : Bool) {z : ℝ} (hz : 0 < z) (v : PairFock E s' t') :
    Continuous (coneIntegrand A X μ β z v) := by
  have h_coord (w : InfinitePlace E) :
      Continuous fun p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ ↦ p.2.val w :=
    (continuous_apply w).comp Units.continuous_val.snd'
  -- Unfolded, the line term is a continuous linear map applied to a Heisenberg translate of `k v`.
  unfold coneIntegrand lineTermReal Splitting.IsAdapted.mixedModel
  dsimp
  simp only [ideleAbs_realIdele_eq_prod]
  fun_prop (disch := simp)

/-- Convergence of the cone integral. Let `A` and `X` be base-adapted splittings, by one hyperbolic
plane, of `W'` over `W` and of `V'` over `V`. For `p = (k, a)`, with `k` in the maximal compact
subgroup of `U(V')` and `a ∈ (InfinitePlace E → ℂ)ˣ`, `coneIntegrand A X μ β z v p` is the line term
`lineTermReal A X β a` of `k v` (`k` acting through the Weil representation), times
`∏ w, (a w / |a w|) ^ (2 μ w)` and the `z`-th power of the idele norm of `a`. For `z > 0` and a
vector `v` all of whose moments are finite (`IsSchwartzVector v`), this integrand is integrable for
the product Haar measure, and its integral over all `p` again has all moments finite. -/
lemma integrable_coneIntegrand (β : Bool) {z : ℝ} (hz : 0 < z) {v : PairFock E s' t'}
    (hv : IsSchwartzVector v) :
    Integrable (coneIntegrand A X μ β z v) (haar.prod haar) ∧
      IsSchwartzVector (∫ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
        coneIntegrand A X μ β z v p ∂haar.prod haar) := by
  have h_moment (N : ℕ) : ∫⁻ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
      fockMoment N (coneIntegrand A X μ β z v p) ∂haar.prod haar ≠ ⊤ := by
    obtain ⟨φ, hφ, h_le⟩ := exists_integrable_fockMoment_coneIntegrand_le A X μ β hz hv N
    exact ((lintegral_mono h_le).trans_lt hφ.hasFiniteIntegral).ne
  exact isSchwartzVector_integral (continuous_coneIntegrand A X μ β hz v).aestronglyMeasurable
    h_moment

/-- For `z > 0` and a vector `v` all of whose moments are finite, all moments of the integral of the
cone integrand are finite. -/
lemma isSchwartzVector_integral_coneIntegrand (β : Bool) {z : ℝ} (hz : 0 < z) {v : PairFock E s' t'}
    (hv : IsSchwartzVector v) :
    IsSchwartzVector (∫ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
      coneIntegrand A X μ β z v p ∂haar.prod haar) :=
  (integrable_coneIntegrand A X μ β hz hv).right

end New.Exchange

end
