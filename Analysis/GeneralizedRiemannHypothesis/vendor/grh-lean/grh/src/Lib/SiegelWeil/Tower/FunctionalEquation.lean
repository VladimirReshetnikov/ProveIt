import Lib.SiegelWeil.Tower.LargeSideConstantTerm
import Lib.SiegelWeil.Tower.TestVector

/-!
# The functional equation of the `L`-function of a tamely ramified character

Tate's argument for the base change of a character of `[U(1)]` of positive weight `μ` that is tamely
ramified at split places. The zeta integral `𝒵` of `exists_zetaIntegral`, whose values `𝒵(x)` and
`𝒵(1 - x)` are for `x ≥ 1` the same expression in `x` up to a constant factor, is evaluated at the
test function `∏ conj (a w) ^ (2 μ w) exp (-|a w|²)` (see `Lib.SiegelWeil.Tower.TestVector`). It
continues `L` to real `x > -min μ` and compares the absolute values at `z` and `1 - z` for
`1 ≤ z < min μ + 1`. As `L` has no zero at real `x ≥ 1`, the extension has no zero at the integers
`j > -min μ` (`exists_analytic_extension_ne_zero`). The file also computes the theta kernels of
pairs in which one space is `0`.

Notions from other files:
* `Space E n s`: a hermitian space over the field `E` with basis indexed by `n` and signs `s`;
  `stdSpace E Empty` is the space `0`, `W.θ` the theta functional and `W.vacElem` the vacuum.
* `pairTheta W V α β f`: the theta kernel of `(W, V)` twisted by the characters `α` and `β`;
  `localDatum W V v Φ 𝔠.readsAt` is the datum with archimedean part `v`, the function `Φ` at the
  ramified places of `𝔠` and the vacuum elsewhere; `thetaLarge W V 𝔠 v Φ` integrates the kernel at
  this datum over `[U(V)]`.
* `SplitTameChar E μ`: a character `ν` of `[U(1)]` of positive weight `μ`, tamely ramified exactly
  at a non-empty set `S` of split places; `ν.L S` is its `L`-function without `S ∪ S̄`.

## Relation to the literature

Known result: analytic continuation and functional equation of Hecke `L`-functions. Only real
arguments `x > -min μ` and absolute values are treated. Source: J. Tate, Fourier analysis in number
fields and Hecke's zeta-functions (thesis, 1950), §2.5 and Main Theorem 4.4.1.
-/

noncomputable section

namespace New.Exchange

open MeasureTheory Measure Real Finset Fintype Fock Space Set

open NumberField (InfinitePlace)

/-- For `c > 0`, the function `exp (-y²) y ^ (2 c) (1 + log² y)` is bounded above on `y > 0`. -/
lemma exists_exp_neg_sq_mul_rpow_mul_one_add_log_sq_le {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, ∀ y > (0 : ℝ), rexp (-y ^ 2) * (y ^ 2) ^ c * (1 + log y ^ 2) ≤ B := by
  obtain ⟨C, M, hC, h_poly⟩ : ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
      ∀ y : ℝ, 0 < y → (y ^ 2) ^ c * (1 + log y ^ 2) ≤ C * (1 + y) ^ M :=
    exists_sq_rpow_mul_one_add_log_sq_le hc
  refine ⟨C * rexp (M + M ^ 2), fun y hy ↦ ?_⟩
  have h_exp : (1 + y) ^ M ≤ rexp (M * y) := by
    grw [exp_nat_mul, add_comm, add_one_le_exp]
  have h_exponent : -y ^ 2 + M * y ≤ M + M ^ 2 := by
    nlinarith [sq_nonneg (y - M), sq_nonneg y, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  calc rexp (-y ^ 2) * (y ^ 2) ^ c * (1 + log y ^ 2)
      ≤ rexp (-y ^ 2) * (C * rexp (M * y)) := by grw [mul_assoc, h_poly y hy, h_exp]
    _ = C * rexp (-y ^ 2 + M * y) := by rw [exp_add, mul_left_comm]
    _ ≤ C * rexp (M + M ^ 2) := by gcongr

/-- For exponents `c x > 0`, the function `a ↦ ∏ x, exp (-|a x|²) |a x| ^ (2 c x)` is integrable for
the Haar measure of the group `(ι → ℂ)ˣ`: the integrals that define the `Γ`-factors converge. -/
lemma integrable_prod_exp_neg_sq_mul_rpow {ι : Type} [Fintype ι] {c : ι → ℝ}
    (hc : ∀ x : ι, 0 < c x) :
    Integrable (fun a : (ι → ℂ)ˣ ↦ ∏ x : ι, rexp (-‖a.val x‖ ^ 2) * (‖a.val x‖ ^ 2) ^ c x)
      haar := by
  -- Each factor is at most a constant times `(1 + log² |a x|)⁻¹`.
  choose B hB using fun x : ι ↦ exists_exp_neg_sq_mul_rpow_mul_one_add_log_sq_le (hc x)
  have h_sq (x : ι) : Continuous fun a : (ι → ℂ)ˣ ↦ ‖a.val x‖ ^ 2 :=
    ((continuous_apply x).comp Units.continuous_val).norm.pow 2
  have h_cont : Continuous fun a : (ι → ℂ)ˣ ↦
      ∏ x : ι, rexp (-‖a.val x‖ ^ 2) * (‖a.val x‖ ^ 2) ^ c x :=
    continuous_finsetProd _ fun x _ ↦
      (h_sq x).neg.rexp.mul ((h_sq x).rpow_const fun _ ↦ .inr (hc x).le)
  have h_le (a : (ι → ℂ)ˣ) :
      ‖∏ x : ι, rexp (-‖a.val x‖ ^ 2) * (‖a.val x‖ ^ 2) ^ c x‖ ≤
        (∏ x : ι, B x) * ∏ x : ι, (1 + log ‖a.val x‖ ^ 2)⁻¹ := by
    rw [norm_of_nonneg (by positivity), ← prod_mul_distrib]
    refine prod_le_prod₀ (fun x _ ↦ by positivity) fun x _ ↦ ?_
    rw [le_mul_inv_iff₀ (by positivity)]
    exact hB x ‖a.val x‖ (norm_pos_iff.2 (piUnits_val_apply_ne_zero a x))
  exact (integrable_prod_inv_one_add_log_sq.const_mul (∏ x : ι, B x)).mono'
    h_cont.aestronglyMeasurable (.of_forall h_le)

section Archimedean

variable {E : Type} [Field E] [CMType E]

variable (E) in
/-- The test function times the archimedean component of a character of weight `m`: the integrand
of the archimedean zeta integral without the factor `|a| ^ x`, where `|a| = ∏ w, |a w|²`. -/
def gammaWeight (m : InfinitePlace E → ℕ) (a : (InfinitePlace E → ℂ)ˣ) : ℝ :=
  rexp (-∑ w : InfinitePlace E, ‖a.val w‖ ^ 2) *
    ∏ w : InfinitePlace E, Complex.normSq (a.val w) ^ m w

variable (E) in
/-- The archimedean zeta integral `∫ gammaWeight E m a * |a| ^ x` of the test function at real `x`,
where `ideleAbs (realIdele a) = |a| = ∏ w, |a w|²`. Classically (not proved here), for `x > -min m`,
it is a constant times `∏ Γ(x + m w)`; only its positivity and analyticity are proved and used. -/
def gammaIntegral (m : InfinitePlace E → ℕ) (x : ℝ) : ℝ :=
  ∫ a : (InfinitePlace E → ℂ)ˣ, gammaWeight E m a * ideleAbs (realIdele a) ^ x ∂haar

variable {m : InfinitePlace E → ℕ} {k : ℕ}

/-- The integrand `gammaWeight E m a * |a| ^ x` of the archimedean zeta integral is integrable for
`x > -k`, where `k ≤ m w` for every infinite place `w` and `|a| = ∏ w, |a w|²`. -/
lemma integrable_gammaWeight_mul_rpow (hk : ∀ w : InfinitePlace E, k ≤ m w) {x : ℝ}
    (hx : -(k : ℝ) < x) :
    Integrable (fun a : (InfinitePlace E → ℂ)ˣ ↦ gammaWeight E m a * ideleAbs (realIdele a) ^ x)
      haar := by
  have h_pos (w : InfinitePlace E) : 0 < m w + x := by
    linarith [(Nat.cast_le (α := ℝ)).2 (hk w)]
  refine (integrable_prod_exp_neg_sq_mul_rpow h_pos).congr (.of_forall fun a ↦ ?_)
  have h_sq (w : InfinitePlace E) : 0 < ‖a.val w‖ ^ 2 := by
    simp [piUnits_val_apply_ne_zero a w]
  have h_abs : ideleAbs (realIdele a) = ∏ w : InfinitePlace E, ‖a.val w‖ ^ 2 := by
    simp [ideleAbs, finAdele_one_apply]
  change ∏ w : InfinitePlace E, rexp (-‖a.val w‖ ^ 2) * (‖a.val w‖ ^ 2) ^ (m w + x) =
    gammaWeight E m a * ideleAbs (realIdele a) ^ x
  simp only [gammaWeight, h_abs, ← finsetProd_rpow _ _ (fun w _ ↦ (h_sq w).le),
    rpow_add (h_sq _), rpow_natCast, prod_mul_distrib, ← exp_sum, sum_neg_distrib,
    Complex.normSq_eq_norm_sq, mul_assoc]

lemma gammaWeight_pos (a : (InfinitePlace E → ℂ)ˣ) : 0 < gammaWeight E m a :=
  mul_pos (exp_pos _) <| prod_pos fun w _ ↦
    pow_pos (Complex.normSq_pos.2 (piUnits_val_apply_ne_zero a w)) (m w)

/-- The archimedean zeta integral `gammaIntegral E m x` is positive for `x > -k`, where `k ≤ m w`
for every infinite place `w`. -/
lemma gammaIntegral_pos (hk : ∀ w : InfinitePlace E, k ≤ m w) {x : ℝ} (hx : -(k : ℝ) < x) :
    0 < gammaIntegral E m x := by
  have h_pos (a : (InfinitePlace E → ℂ)ˣ) : 0 < gammaWeight E m a * ideleAbs (realIdele a) ^ x :=
    mul_pos (gammaWeight_pos a) (rpow_pos_of_pos ideleAbs_pos x)
  rw [gammaIntegral, integral_pos_iff_support_of_nonneg (fun a ↦ (h_pos a).le)
    (integrable_gammaWeight_mul_rpow hk hx), Function.support_eq_univ fun a ↦ (h_pos a).ne']
  simp [pos_iff_ne_zero, NeZero.ne]

/-- The archimedean zeta integral `gammaIntegral E m x` is analytic in the real variable `x > -k`,
where `k ≤ m w` for every infinite place `w`. -/
lemma analyticOnNhd_gammaIntegral (hk : ∀ w : InfinitePlace E, k ≤ m w) :
    AnalyticOnNhd ℝ (fun x : ℝ ↦ (gammaIntegral E m x : ℂ)) (Ioi (-(k : ℝ))) := by
  intro x hx
  obtain ⟨x₀, hx₀, h_lt⟩ := exists_between (mem_Ioi.1 hx)
  have h_int {y : ℝ} (hy : -(k : ℝ) < y) : Integrable (fun a : (InfinitePlace E → ℂ)ˣ ↦
      (gammaWeight E m a : ℂ) * (ideleAbs (realIdele a) ^ y : ℝ)) haar :=
    ((integrable_gammaWeight_mul_rpow hk hy).ofReal (𝕜 := ℂ)).congr
      (.of_forall fun a ↦ Complex.ofReal_mul _ _)
  -- The integral is a Mellin transform, hence analytic between `x₀` and `x + 1`.
  have h_strip : AnalyticOnNhd ℝ (fun y : ℝ ↦ ∫ a : (InfinitePlace E → ℂ)ˣ,
      (gammaWeight E m a : ℂ) * (ideleAbs (realIdele a) ^ y : ℝ) ∂haar) (Ioo x₀ (x + 1)) := by
    obtain ⟨-, -, h_analytic⟩ := analyticOnNhd_integral_mul_rpow (fun _ ↦ ideleAbs_pos)
      continuous_ideleAbs_realIdele.measurable (h_int hx₀).hasFiniteIntegral
      (h_int (y := x + 1) (by linarith))
    exact h_analytic
  simp only [gammaIntegral, ← integral_complex_ofReal, Complex.ofReal_mul]
  exact h_strip x ⟨h_lt, lt_add_one x⟩

end Archimedean

variable {E : Type} [Field E] [CMType E]
/-- For the tame part `χ` of a split tame character `𝔠`, the standard datum
`stdColDatum 𝔠.semilocalChar 1`, which sends an integral matrix `y` with unit determinant to
`χ⁻¹ (det y)` and all other matrices to zero, has the value `1` at the identity matrix. -/
lemma stdColDatum_one_one {n : Type} [Fintype n] [DecidableEq n] {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) :
    stdColDatum 𝔠.semilocalChar 1 (1 : Matrix n n (LocProd 𝔠.ramifiedPlaces)) = 1 := by
  simp [stdColDatum, IsIntMatrix.one, invOnUnits, IsIntegralUnit]

variable [WeilData E]

/-- For a space `W` of rank zero, the operator `W.schrodingerOp 𝔠.ramifiedPlaces Φ` (a combination
of Heisenberg operators at the ramified places `𝔠.ramifiedPlaces` that represents the function `Φ`
of finite adelic vectors) sends the vacuum `W.vacElem` to `Φ 0` times the vacuum. -/
lemma schrodingerOp_vacElem_of_isEmpty {n : Type} [Fintype n] [DecidableEq n] [IsEmpty n]
    {s : n → ℤˣ} (W : Space E n s) {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ)
    (Φ : (n → 𝔸f E) → ℂ) :
    W.schrodingerOp 𝔠.ramifiedPlaces Φ W.vacElem = Φ 0 • W.vacElem := by
  -- In rank zero `Φ` is a constant, so it is a multiple of the indicator function `boxIndicator`.
  have hΦ : Φ = Φ 0 • boxIndicator n 𝔠.ramifiedPlaces := by
    funext x
    simp [Subsingleton.eq_zero x, boxIndicator_apply]
  conv_lhs => rw [hΦ, map_smul, _root_.smul_apply,
    schrodingerOp_boxIndicator 𝔠.readsAt.disjoint_star, projOn_vacElem]

/-- The theta integral `thetaLarge W V 𝔠 v Φ g` is homogeneous in the archimedean part `v` of the
datum. -/
lemma thetaLarge_smul {n r : Type} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    {s : n → ℤˣ} {t : r → ℤˣ} (W : Space E n s) (V : Space E r t) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (c : ℂ) (v : PairFock E s t)
    (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ) (g : G E s) :
    thetaLarge W V 𝔠 (c • v) Φ g = c * thetaLarge W V 𝔠 v Φ g := by
  simp only [thetaIntegral, pairTheta, localDatum, map_smul, _root_.smul_apply, smul_eq_mul,
    integral_const_mul]

/-- Let `A` be an adapted splitting (orthonormal at the infinite places, integral at the finite
ones) of `W'` into a hyperbolic plane and a space `W` of rank zero, and let the signs `s'` of `W'`
take each of the values `1` and `-1` once. On either side `β` of Poisson's formula, the integral
over the maximal compact subgroup and the archimedean ideles of the cone integrand with exponent
`x`, at the test vector `tateVector s' m` (the product of the `m w`-th powers of the diagonal Fock
variables), is the vacuum `vacVector` of the archimedean Fock space times `gammaIntegral E m x`
times the volume of the compact subgroup. -/
lemma integral_coneIntegrand_tateVector {n n' : Type} [Fintype n] [DecidableEq n] [IsEmpty n]
    [Fintype n'] [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} {W : Space E n s}
    {W' : Space E n' s'} (A : W'.Splitting W Unit) [IsBaseAdapted A] (hs : Function.Bijective s')
    (m : InfinitePlace E → ℕ) (β : Bool) (x : ℝ) :
    ∫ p : maxCompact E s' × (InfinitePlace E → ℂ)ˣ,
        coneIntegrand A A (fun w : InfinitePlace E ↦ m w) β x (tateVector s' m) p ∂haar.prod haar =
      ((gammaIntegral E m x * (haar : Measure (maxCompact E s')).real univ : ℝ) : ℂ) •
        vacVector := by
  let f (a : (InfinitePlace E → ℂ)ˣ) : ℝ := gammaWeight E m a * ideleAbs (realIdele a) ^ x
  -- The integrand does not depend on the compact variable, whose integral gives the volume.
  have h_integrand (p : maxCompact E s' × (InfinitePlace E → ℂ)ˣ) :
      coneIntegrand A A (fun w : InfinitePlace E ↦ m w) β x (tateVector s' m) p =
        f p.2 • vacVector := by
    rw [coneIntegrand_tateVector A hs, mul_right_comm]
    rfl
  simp only [h_integrand, integral_smul_const, integral_fun_snd f, smul_eq_mul, f,
    gammaIntegral, mul_comm, Complex.coe_smul]

section RankZero

variable {n : Type} [Fintype n] [DecidableEq n] {s : n → ℤˣ}

/-- For a hermitian space `W` of rank zero (`n` empty) over a CM field `E` with Weil data, the theta
functional `W.θ` takes the value `1` on the vacuum `W.vacElem` (the Gaussian times twisted lattice
indicator, as an element of 𝒮(W)). -/
lemma theta_vacElem_of_isEmpty (W : Space E n s) [IsEmpty n] : W.θ W.vacElem = 1 := by
  rw [theta_apply, vacElem_apply_eq_prod_lineTheta (fun _ ↦ Subsingleton.elim _ _), univ_eq_empty,
    Finset.prod_empty]

/-- Take the datum with the Fock vector `x` as archimedean part and the function `Φ` at the ramified
places of `𝔠`. The theta kernel of the pair `(W, 0)`, twisted by characters `α`, `β` of `[U(1)]`,
at this datum and at adelic unitary elements `(g, h)` is `β (det g)⁻¹ * Φ 0` times the theta
functional of the space `Hom(W, 0)` at the image of the vacuum under the integrated operator of
`x`. -/
lemma pairTheta_target_zero (W : Space E n s) (α β : AutChar E) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (x : PairFock E s (1 : Empty → ℤˣ))
    (Φ : Matrix Empty n (LocProd 𝔠.ramifiedPlaces) → ℂ) (g : G E s) (h : G E (1 : Empty → ℤˣ)) :
    pairTheta W (stdSpace E Empty) α β (localDatum W (stdSpace E Empty) x Φ 𝔠.readsAt) (g, h) =
      (β.val g.det : ℂ)⁻¹ * Φ 0 * (W.hom (stdSpace E Empty)).θ
        ((W.hom (stdSpace E Empty)).integrated x (W.hom (stdSpace E Empty)).vacElem) := by
  -- The space `H` of homomorphisms is `0`: the group acts trivially and `Φ` is read at `0`.
  set H : Space E (Empty × n) (homSigns s 1) := W.hom (stdSpace E Empty)
  have h_datum : localDatum W (stdSpace E Empty) x Φ 𝔠.readsAt =
      H.integrated x (Φ 0 • H.vacElem) := by
    rw [localDatum, schrodingerOp_vacElem_of_isEmpty, congrArg Φ (Subsingleton.eq_zero _)]
  rw [pairTheta, pairWeil_apply, Subsingleton.eq_one (G.onHom (g, h)), h_datum,
    Subsingleton.eq_one h]
  simp [H, mul_assoc]

/-- The theta kernel of the pair `(0, W)` twisted by `α` and `β`, at the datum with the vacuum as
archimedean part and the function `Ψ` at the ramified places of `𝔠`, is `α (det g) * Ψ 0`. -/
lemma pairTheta_source_zero (W : Space E n s) (α β : AutChar E) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (Ψ : Matrix n Empty (LocProd 𝔠.ramifiedPlaces) → ℂ)
    (h : G E (1 : Empty → ℤˣ)) (g : G E s) :
    pairTheta (stdSpace E Empty) W α β
        (localDatum (stdSpace E Empty) W vacVector Ψ 𝔠.readsAt) (h, g) =
      α.val g.det * Ψ 0 := by
  -- The space `H` of homomorphisms is `0`: the group acts trivially and `Ψ` is read at `0`.
  let H : Space E (n × Empty) (homSigns 1 s) := (stdSpace E Empty).hom W
  have h_datum : localDatum (stdSpace E Empty) W vacVector Ψ 𝔠.readsAt = Ψ 0 • H.vacElem := by
    rw [localDatum, schrodingerOp_vacElem_of_isEmpty, congrArg Ψ (Subsingleton.eq_zero _)]
    simp only [H, map_smul, projReal_eq_self_of_mem_finitePart, vacElem_mem_finitePart]
  rw [pairTheta, pairWeil_apply, Subsingleton.eq_one (G.onHom (h, g)), h_datum,
    Subsingleton.eq_one h, map_one, one_apply_eq_self, map_smul, map_smul,
    theta_vacElem_of_isEmpty H]
  simp

/-- For the pair `(W, 0)`, the theta integral at `1` of the datum with the vacuum as archimedean
part and the function `Φ` at the ramified places of `𝔠` is the volume of `[U(0)]`, the domain of
integration, times `Φ 0`. -/
lemma thetaLarge_stdSpace_empty_vacVector_one (W : Space E n s) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (Φ : Matrix Empty n (LocProd 𝔠.ramifiedPlaces) → ℂ) :
    thetaLarge W (stdSpace E Empty) 𝔠 vacVector Φ 1 =
      (stdSpace E Empty).quotMeasure.real univ * Φ 0 := by
  have h_kernel (h : G E (1 : Empty → ℤˣ)) :
      pairTheta W (stdSpace E Empty) (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n)
        (localDatum W (stdSpace E Empty) vacVector Φ 𝔠.readsAt) (1, h) = Φ 0 := by
    simp only [pairTheta_target_zero, map_one, Circle.coe_one, inv_one, one_mul,
      projReal_eq_self_of_mem_finitePart, vacElem_mem_finitePart, theta_vacElem_of_isEmpty, mul_one]
  simp only [thetaLarge, thetaIntegral, h_kernel, integral_const, Complex.real_smul]

end RankZero

/-- For each weight `m` there are positive reals `a`, `a'` with the following property for every
split tame character `𝔠 = (ν, S)` of weight `m` (weight positive everywhere, tame part nontrivial
exactly on a nonempty finite set `S` of places disjoint from its conjugate). There exist `κ ≠ 0`,
`ε` with `‖ε‖ = a`, `ε'` with `‖ε'‖ = a'`, and a function `𝒵` analytic on all of ℝ (in the proof,
the zeta integral of the test function) such that for `x ≥ 1` both `𝒵(x)/ε` and `𝒵(1 - x)/ε'` equal
`|α₀| ^ x ∏_{w ∈ S} q_w ^ (x - 1/2) L^S(x, ν) · gammaIntegral E m x · κ`. Here `α₀ = scaleIdele E`
is the idele of the Weil data that fixes the measures, `q_w` is the order of the residue field at
`w`, and `gammaIntegral E m x` is the archimedean zeta integral; classically, though not proved or
used here, it is a constant times `∏_w Γ(x + m w)`. -/
lemma exists_analyticOnNhd_eq_L_mul_gammaIntegral (m : InfinitePlace E → ℕ) :
    ∃ a a' : ℝ, 0 < a ∧ 0 < a' ∧
      ∀ 𝔠 : SplitTameChar E fun w : InfinitePlace E ↦ m w,
      ∃ (κ ε ε' : ℂ) (𝒵 : ℝ → ℂ), κ ≠ 0 ∧ ‖ε‖ = a ∧ ‖ε'‖ = a' ∧
        AnalyticOnNhd ℝ 𝒵 univ ∧
        ∀ x ≥ (1 : ℝ),
          𝒵 x = ε *
            (ideleAbs (WeilData.scaleIdele E) ^ x * ∏ w : 𝔠.ramifiedPlaces,
              (w.val.q : ℝ) ^ (x - 1 / 2) : ℝ) *
              𝔠.character.L 𝔠.ramifiedPlaces x * (gammaIntegral E m x * κ) ∧
          𝒵 (1 - x) = ε' *
            (ideleAbs (WeilData.scaleIdele E) ^ x * ∏ w : 𝔠.ramifiedPlaces,
              (w.val.q : ℝ) ^ (x - 1 / 2) : ℝ) *
              𝔠.character.L 𝔠.ramifiedPlaces x * (gammaIntegral E m x * κ) := by
  -- Remove a plane from both spaces of the pair `(H, H)`, where `H` is the hyperbolic plane; what
  -- remains is the space `Z = 0`, and the cone integral of the test vector is the vacuum
  -- `vacVector` of the archimedean Fock space times `gammaIntegral E m x` times a volume.
  let Z : Space E Empty 1 := stdSpace E Empty
  let A : (hyperbolicSum Unit Z).Splitting Z Unit := removePlanes Unit Z
  let s : (Unit ⊕ Unit) ⊕ Empty → ℤˣ := Sum.elim (hyperbolicSigns Unit) 1
  have h_signs : Function.Bijective s := by decide
  obtain ⟨a, ha, h_zeta⟩ := exists_zetaIntegral A A (Equiv.emptySum Empty _)
    (Equiv.emptySum Empty Empty) (by simp) fun w : InfinitePlace E ↦ m w
  -- The side `true` of Poisson's formula gives `𝒵(x)`, the side `false` gives `𝒵(1 - x)`.
  refine ⟨a true, a false, ha true, ha false, fun 𝔠 ↦ ?_⟩
  obtain ⟨ε, hε, h_continuation⟩ := h_zeta 𝔠
  -- Take the test vector, the empty matrix, the idele `1` and the identity of the group.
  obtain ⟨𝒵, h_analytic, -, h_value⟩ :=
    h_continuation (tateVector s m) (isSchwartzVector_tateVector s m) 0 nofun 1 1 (.inl rfl)

  let Φ : Matrix Empty Empty (LocProd 𝔠.ramifiedPlaces) → ℂ := stdColDatum 𝔠.semilocalChar 1
  -- There is only one empty matrix.
  have h_datum : stdRowDatum (Equiv.emptySum Empty Empty) 𝔠.semilocalChar 0 = Φ :=
    funext fun _ ↦ congrArg Φ (Subsingleton.elim _ _)
  have h_zero : Φ 0 = 1 := (congrArg Φ (Subsingleton.elim 0 1)).trans (stdColDatum_one_one 𝔠)
  have h_theta : thetaLarge Z Z 𝔠 vacVector Φ 1 ≠ 0 := by
    rw [thetaLarge_stdSpace_empty_vacVector_one, h_zero, mul_one]
    have : SecondCountableTopology (G E (1 : Empty → ℤˣ)) := inferInstance
    exact Complex.ofReal_ne_zero.2 measureReal_univ_ne_zero
  have : R1Space (maxCompact E s) := inferInstance
  let κ : ℂ := (haar : Measure (maxCompact E s)).real univ * thetaLarge Z Z 𝔠 vacVector Φ 1
  have h_cone (β : Bool) (x : ℝ) :
      thetaLarge Z Z 𝔠 (∫ p : maxCompact E s × (InfinitePlace E → ℂ)ˣ,
        coneIntegrand A A (fun w ↦ m w) β x (tateVector s m) p ∂haar.prod haar) Φ 1 =
        gammaIntegral E m x * κ := by
    rw [integral_coneIntegrand_tateVector A h_signs, thetaLarge_smul, Complex.ofReal_mul, mul_assoc]
  have h_side (β : Bool) {x : ℝ} (hx : 1 ≤ x) : 𝒵 (cond β x (1 - x)) = ε β *
      (ideleAbs (WeilData.scaleIdele E) ^ x * ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ) ^ (x - 1 / 2) :
        ℝ) *
        𝔠.character.L 𝔠.ramifiedPlaces x * (gammaIntegral E m x * κ) := by
    rw [h_value β x hx, h_datum, h_cone]
  exact ⟨κ, ε true, ε false, 𝒵,
    mul_ne_zero (Complex.ofReal_ne_zero.2 measureReal_univ_ne_zero) h_theta, hε true, hε false,
    h_analytic, fun x hx ↦ ⟨h_side true hx, h_side false hx⟩⟩

/-- The factor `|α₀| ^ x ∏ q_w ^ (x - 1/2)` of the zeta integral is analytic in `x`. Here `α₀` is
`WeilData.scaleIdele E` and `q_w` is the order of the residue field at the ramified place `w` of
`𝔠`. -/
lemma analyticAt_ideleAbs_rpow_mul_prod_rpow {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ)
    (x : ℝ) :
    AnalyticAt ℝ (fun y : ℝ ↦ ((ideleAbs (WeilData.scaleIdele E) ^ y *
      ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ) ^ (y - 1 / 2) : ℝ) : ℂ)) x := by
  have h_scale : AnalyticAt ℝ (fun y : ℝ ↦ ideleAbs (WeilData.scaleIdele E) ^ y) x := by
    simp only [rpow_def_of_pos ideleAbs_pos]
    fun_prop
  have h_place (w : 𝔠.ramifiedPlaces) : AnalyticAt ℝ (fun y : ℝ ↦ (w.val.q : ℝ) ^ (y - 1 / 2))
    x := by
    simp only [rpow_def_of_pos (show (0 : ℝ) < w.val.q by simp [FinPlace.q_bounds])]
    fun_prop
  exact (Complex.ofRealCLM.analyticAt _).comp
    (h_scale.mul (Finset.analyticAt_fun_prod _ fun w _ ↦ h_place w))

/-- Functional equation in absolute values, on a real interval (a special case of the main theorem
of Tate's thesis). Let `k ≤ μ w` for every infinite place `w`. For a split tame character
`𝔠 = (ν, S)` of weight `μ` the function `L^S(x, ν)` of `x ≥ 1` extends to an analytic function `Λ`
of real `x > -k`, and `L♯(1 - z) = C z * L♯(z)` for real `1 ≤ z < k + 1`. Here
`L♯(z) = ‖L^S(z, ν)‖ ∏_{w ∈ S} q_w ^ (z - 1/2)` is `lSharp 𝔠 z`, `L♯(1 - z)` is formed with `Λ`,
and `C z > 0` does not depend on the character. -/
theorem exists_analytic_extension_functional_equation {μ : InfinitePlace E → ℤ} {k : ℕ}
    (hk : ∀ w : InfinitePlace E, k ≤ μ w) :
    ∃ C : ℝ → ℝ, (∀ z ∈ Ico (1 : ℝ) (k + 1), 0 < C z) ∧
      ∀ 𝔠 : SplitTameChar E μ, ∃ Λ : ℝ → ℂ,
        AnalyticOnNhd ℝ Λ (Ioi (-(k : ℝ))) ∧
        (∀ x ≥ (1 : ℝ), Λ x = 𝔠.character.L 𝔠.ramifiedPlaces x) ∧
        ∀ z ∈ Ico (1 : ℝ) (k + 1),
          ‖Λ (1 - z)‖ * ∏ w : 𝔠.ramifiedPlaces,
            (w.val.q : ℝ) ^ (1 - z - 1 / 2) = C z * lSharp 𝔠 z := by
  obtain ⟨m, rfl⟩ : ∃ m : InfinitePlace E → ℕ, μ = fun w : InfinitePlace E ↦ (m w : ℤ) :=
    ⟨fun w ↦ (μ w).toNat, funext fun w ↦
      (Int.toNat_of_nonneg ((Nat.cast_nonneg k).trans (hk w))).symm⟩
  replace hk (w : InfinitePlace E) : k ≤ m w := Nat.cast_le.1 (hk w)
  -- `a` and `a'` are the absolute values of the factors in the formulas for `𝒵(x)`, `𝒵(1 - x)`.
  obtain ⟨a, a', ha, ha', h_zeta⟩ := exists_analyticOnNhd_eq_L_mul_gammaIntegral m
  let α : ℝ := ideleAbs (WeilData.scaleIdele E)
  have hα (x : ℝ) : 0 < α ^ x := rpow_pos_of_pos ideleAbs_pos x
  have h_left {z : ℝ} (hz : z ∈ Ico (1 : ℝ) (k + 1)) : -(k : ℝ) < 1 - z := by linarith [hz.2]
  have h_right {x : ℝ} (hx : 1 ≤ x) : -(k : ℝ) < x := by linarith [Nat.cast_nonneg (α := ℝ) k]
  let C (z : ℝ) : ℝ := a' * α ^ z * gammaIntegral E m z /
    (a * α ^ (1 - z) * gammaIntegral E m (1 - z))
  have h_pos {c x : ℝ} (hc : 0 < c) (hx : -(k : ℝ) < x) : 0 < c * α ^ x * gammaIntegral E m x :=
    mul_pos (mul_pos hc (hα x)) (gammaIntegral_pos hk hx)
  refine ⟨C, fun z hz ↦ div_pos (h_pos ha' (h_right hz.1)) (h_pos ha (h_left hz)), fun 𝔠 ↦ ?_⟩
  obtain ⟨κ, ε, ε', 𝒵, hκ, hε, hε', h_analytic, h_value⟩ := h_zeta 𝔠
  let Q (x : ℝ) : ℝ := ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ) ^ (x - 1 / 2)
  have hQ (x : ℝ) : 0 < Q x := prod_pos fun w _ ↦ rpow_pos_of_pos (by simp [FinPlace.q_bounds]) _
  -- Divide `𝒵` by the product `F` of its factors other than `L`, which is analytic without zeros.
  let F (x : ℝ) : ℂ := ε * (α ^ x * Q x : ℝ) * (gammaIntegral E m x * κ)
  have hF_norm {x : ℝ} (hx : -(k : ℝ) < x) :
      ‖F x‖ = a * (α ^ x * Q x) * (gammaIntegral E m x * ‖κ‖) := by
    simp [F, hε, abs_of_pos, hα, hQ, gammaIntegral_pos hk hx]
  have hF_ne {x : ℝ} (hx : -(k : ℝ) < x) : F x ≠ 0 := by
    simp [F, (hα x).ne', (hQ x).ne', (gammaIntegral_pos hk hx).ne',
      hκ, norm_ne_zero_iff.1 (hε.trans_ne ha.ne')]
  have hF_analytic : AnalyticOnNhd ℝ F (Ioi (-(k : ℝ))) :=
    fun x hx ↦ (analyticAt_const.mul (analyticAt_ideleAbs_rpow_mul_prod_rpow 𝔠 x)).mul
      ((analyticOnNhd_gammaIntegral hk x hx).mul analyticAt_const)
  refine ⟨fun x ↦ 𝒵 x / F x, (h_analytic.mono (subset_univ _)).div hF_analytic fun x ↦ hF_ne,
    fun x hx ↦ ?_, fun z hz ↦ ?_⟩
  · change 𝒵 x / F x = 𝔠.character.L 𝔠.ramifiedPlaces x
    rw [div_eq_iff (hF_ne (h_right hx)), (h_value x hx).1]
    ring
  · have h_dual : ‖𝒵 (1 - z)‖ =
        a' * (α ^ z * Q z) * ‖𝔠.character.L 𝔠.ramifiedPlaces z‖ * (gammaIntegral E m z * ‖κ‖) := by
      have h_eq : 𝒵 (1 - z) = ε' * (α ^ z * Q z : ℝ) * 𝔠.character.L 𝔠.ramifiedPlaces z *
          (gammaIntegral E m z * κ) := (h_value z hz.1).2
      simp [h_eq, hε', abs_of_pos, hα, hQ, gammaIntegral_pos hk (h_right hz.1)]
    -- Both products over the ramified places are values of `Q`.
    change ‖𝒵 (1 - z) / F (1 - z)‖ * Q (1 - z) = C z * (‖𝔠.character.L 𝔠.ramifiedPlaces z‖ * Q z)
    simp only [norm_div, h_dual, hF_norm (h_left hz), C]
    field_simp [(hQ _).ne']

/-- Let `k ≤ μ w` for every infinite place `w`, and let `𝔠 = (ν, S)` be a split tame character of
weight `μ`. The `L`-function `L^S(x, ν)` of `x ≥ 1`, written `𝔠.character.L 𝔠.ramifiedPlaces x`,
extends to an analytic function `Λ` of real `x > -k` that has no zero at the integers `j > -k`. -/
theorem exists_analytic_extension_ne_zero {μ : InfinitePlace E → ℤ} {k : ℕ}
    (hk : ∀ w : InfinitePlace E, k ≤ μ w) (𝔠 : SplitTameChar E μ) :
    ∃ Λ : ℝ → ℂ, AnalyticOnNhd ℝ Λ (Ioi (-(k : ℝ))) ∧
      (∀ x ≥ (1 : ℝ), Λ x = 𝔠.character.L 𝔠.ramifiedPlaces x) ∧
      ∀ j : ℤ, -(k : ℤ) < j → Λ j ≠ 0 := by
  obtain ⟨C, hC, h_extension⟩ := exists_analytic_extension_functional_equation hk
  obtain ⟨Λ, h_analytic, h_eq, h_equation⟩ := h_extension 𝔠
  refine ⟨Λ, h_analytic, h_eq, fun j hj h_zero ↦ ?_⟩
  obtain h_pos | h_nonpos := lt_or_ge 0 j
  · have h_one : (1 : ℝ) ≤ j := by exact_mod_cast h_pos
    exact 𝔠.L_ne_zero h_one ((h_eq j h_one).symm.trans h_zero)
  · -- The functional equation carries `j ≤ 0` to `1 - j ≥ 1`.
    have h_mem : (1 - j : ℝ) ∈ Ico (1 : ℝ) (k + 1) :=
      ⟨by simpa using h_nonpos, by
        linarith [show -(k : ℝ) < j by exact_mod_cast hj]⟩
    have h_value : C (1 - j) * lSharp 𝔠 (1 - j) = 0 := by simp [← h_equation _ h_mem, h_zero]
    exact (mul_pos (hC _ h_mem) (lSharp_pos 𝔠 h_mem.1)).ne' h_value

end New.Exchange

end
