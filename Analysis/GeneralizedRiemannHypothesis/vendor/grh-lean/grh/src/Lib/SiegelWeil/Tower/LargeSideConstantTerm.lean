import Lib.SiegelWeil.Tower.ConstantTerm
import Lib.SiegelWeil.Tower.FiniteTateIntegral
import Lib.SiegelWeil.Tower.LineGaussSums

/-!
# Removing a plane: the constant term on the side of the large space

Let `W' = W ⊕ H` and `V' = V ⊕ H` be hermitian spaces over the CM field `E`, with `H` a hyperbolic
plane and `W` of even rank. On standard data, the constant term of the theta integral of `(W', V')`
along the new isotropic line of `W'` unfolds to Tate's integral `𝒵(e + 1)`, `e = rk V - rk W / 2`,
for the base change of the character.

Neither side of Poisson's formula on the line has a term at `0`, so `𝒵` is analytic on the real
line. For `x ≥ 1` its value is, up to an explicit factor, `L(x)` times the theta integral of
`(W, V)` at a cone integral (`New.Exchange.exists_zetaIntegral`). This gives the constant term for
`e ≥ 0` (`New.Exchange.exists_planeConstantTerm_eq_thetaLarge_cone`) and, through the other side of
Poisson's formula, for `e < 0` (`New.Exchange.exists_planeConstantTerm_eq_thetaLarge_dualCone`).

## Main definitions and results

* `New.Exchange.exists_planeConstantTerm_eq_thetaLarge_cone`: for `z = rk V - rk W / 2 ≥ 0`, with
  `rk W = card n` even, a Schwartz vector `v'` and integral `y`, the constant term along `A` of the
  theta integral of `(W', V')` is `γ` times the theta integral of `(W, V)` on
  `cone A X μ (z + 1) v'` and `stdRowDatum σ 𝔠.semilocalChar y`.
* `New.Exchange.exists_planeConstantTerm_eq_thetaLarge_dualCone`: the same for
  `rk V - rk W / 2 = -z - 1 < 0`, at `u = 1`, with `dualCone A X μ (z + 1) v'` in place of the cone.

Notions from other files:
* `𝔠 : SplitTameChar E μ` is a character `𝔠.character` of `[U(1)]` of positive weight `μ`, tamely
  ramified exactly on a finite set `𝔠.ramifiedPlaces` of places disjoint from its conjugate;
  `𝔠.semilocalChar` is `t ↦ ν(t / t̄)`, for `ν = 𝔠.character`, on the product
  `LocProd 𝔠.ramifiedPlaces` of the completions at `𝔠.ramifiedPlaces`.
* `A : W'.Splitting W Unit` is a decomposition `W' = W ⊕ H`; it is `IsBaseAdapted` if its frames are
  orthonormal at the infinite places and integral at the finite places.
* `localDatum W V v Φ 𝔠.readsAt` is the datum on `Hom(W, V)` with real part `v`, the function `Φ` at
  the places of `𝔠.ramifiedPlaces` and the vacuum elsewhere; `thetaLarge W V 𝔠 v Φ` is its theta
  integral over `[U(V)]`.
* `stdRowDatum σ χ y` sends `x` to `χ⁻¹` of the determinant of the matrix with the rows of `y` and
  `x` if that matrix is integral with integral inverse, and to `0` otherwise.
* `New.Exchange.lSharp` (from `Lib.SiegelWeil.Tower.FiniteTateIntegral`) is
  `L♯(z) = |L^S(z, ν)| ∏_{w ∈ S} q_w ^ (z - 1/2)` for `ν = 𝔠.character`, `S = 𝔠.ramifiedPlaces`.

## Relation to the literature

Known result: the tower property for the constant term of a theta lift along an isotropic line. In
the literature the lifted form is cuspidal, whereas here it is a character, the data are ramified,
and the isotropic orbit survives as a Tate integral. The constant term is therefore the smaller lift
times a factor whose size is given by a Hecke L-value. Source: S. Rallis, On the Howe duality
conjecture, Compositio Math. 51 (1984), Thm I.1.1; for the unitary case, C. Wu, Irreducibility of
theta lifting for unitary groups, J. Number Theory 133 (2013), Prop. 3.1.
-/

noncomputable section

namespace New.Exchange

open MeasureTheory Measure WeilData SemilocalField Space Fintype Real Complex Set

open NumberField (InfinitePlace)

/-! ### The standard data of a pair with one more plane -/

section

variable {E : Type} [Field E] [CMType E] {μ : InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ}
  [WeilData E] {n n' r r' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r'] {s : n → ℤˣ} {s' : n' → ℤˣ}
variable {t : r → ℤˣ} {t' : r' → ℤˣ} {W : Space E n s} {W' : Space E n' s'} {V : Space E r t}
  {V' : Space E r' t'} {b : Type} {ν : AutChar E}
  (A : W'.Splitting W Unit) (X : V'.Splitting V Unit) [IsBaseAdapted A]

/-- Adding `card b` hyperbolic planes to `W` multiplies the twisted character
`rankTwist ν n = ν * upsilonU1 ^ (card n / 2)` by `upsilonU1 ^ card b`. -/
theorem rankTwist_eq_mul_of_splitting [Fintype b] [DecidableEq b] (A : W'.Splitting W b) :
    rankTwist ν n' = rankTwist ν n * upsilonU1 ^ card b := by
  rw [rankTwist, rankTwist, A.card_eq, Nat.add_mul_div_left _ _ two_pos, pow_add, mul_assoc]

/-- The datum on `Hom(W, V)` with real part the Fock vector `v` and with the function `Φ` at the
ramified places of the split tame character `𝔠` is homogeneous in `Φ`. -/
theorem smul_localDatum (c : ℂ) (v : PairFock E s t)
    (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ) :
    c • localDatum W V v Φ 𝔠.readsAt = localDatum W V v (c • Φ) 𝔠.readsAt := by
  rw [← map_smul, smul_schrodingerOp]
  rfl

/-- Let `f` be the datum of the pair `(W, V)` with real part `v` and, at the ramified places of the
split tame character `𝔠`, the standard function `stdRowDatum σ 𝔠.semilocalChar z` of a matrix `z`
with entries in the ring `O` of local integers. Then `f` is fixed by the integral finite points `k`
of `U(V)` in the Weil representation twisted by `rankTwist 𝔠.character⁻¹ n` and any character
`c`. -/
theorem pairWeil_stdRowDatum_eq_self [Fintype b] [DecidableEq b]
    {c : AutChar E} {v : PairFock E s t}
    {z : Matrix b n (LocProd 𝔠.ramifiedPlaces)} {k : Gf E r} {f : 𝒮 (W.hom V)} (σ : b ⊕ r ≃ n)
    (hz : IsIntMatrix O z) (hk : k ∈ stdLevel E r)
    (hf : localDatum W V v (stdRowDatum σ 𝔠.semilocalChar z) 𝔠.readsAt = f) :
    pairWeil W V (rankTwist 𝔠.character⁻¹ n) c (1, (k : G E t)) f = f := by
  -- The point `k` translates the standard function by `atPlaces _ k⁻¹` and multiplies it by a
  -- character value. The translation multiplies the function by the inverse of that value.
  subst hf
  obtain ⟨hk_int, hk_inv⟩ := mem_intGL.1 hk
  have h_translate (x : Matrix r n (LocProd 𝔠.ramifiedPlaces)) :
      𝔠.semilocalChar (atPlaces 𝔠.ramifiedPlaces k⁻¹).val.det * stdRowDatum σ 𝔠.semilocalChar z
        ((atPlaces 𝔠.ramifiedPlaces k⁻¹).val * x) =
        stdRowDatum σ 𝔠.semilocalChar z x :=
    (areMatched_stdRowDatum_stdColDatum σ hz).left_mul <| mem_intGL.2
      ⟨fun i j ↦ evalPlaces_mem_O _ (hk_inv i j), fun i j ↦ evalPlaces_mem_O _ (hk_int i j)⟩
  have h_char : ((rankTwist 𝔠.character⁻¹ n).val (detFin t k) * (c.val (detFin s 1))⁻¹).val =
      𝔠.semilocalChar (atPlaces 𝔠.ramifiedPlaces k⁻¹).val.det := by
    rw [← 𝔠.character_detFin_eq_of_mem_stdLevel (s := t) (inv_mem hk)]
    simp [detFin, ← map_inv, rankTwist, circleChar_inv_apply,
      upsilonU1_detFin_eq_one_of_mem_stdLevel hk, Prod.mk_one_one]
  refine (𝔠.readsAt.pairWeil_localDatum_of_mem_stdLevel (stdRowDatum_mem σ 𝔠.semilocalChar)
    (one_mem _)
    hk).trans ?_
  rw [h_char, smul_localDatum]
  congr with x
  simpa [atPlaces, Gf.subtype_eq_val, Gf.coe_inv, ← map_inv] using h_translate x

variable (𝔠) in
/-- The datum of the pair `(W', V')` with `v` at the real places and, at the places
`𝔠.ramifiedPlaces`, the standard datum of `y` composed with the projection to `W`. -/
abbrev planeDatum (σ' : b ⊕ r' ≃ n') (v : PairFock E s' t')
    (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)) :
    𝒮 (W'.hom V') :=
  localDatum W' V' v (stdRowDatum σ' 𝔠.semilocalChar (y * (adaptedFrame 𝔠.readsAt A).dualI))
    𝔠.readsAt

variable (𝔠 V') in
/-- The constant term along `A`, at the point `(u, g)` of the Levi subgroup, of the theta integral
of `(W', V')` on `planeDatum 𝔠 A σ' v y`. -/
abbrev planeConstantTerm (σ' : b ⊕ r' ≃ n') (v : PairFock E s' t')
    (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)) (u : (𝔸 E)ˣ) (g : G E s) : ℂ :=
  ∫ q : Matrix n Unit (𝔸 E) × Matrix Unit Unit (𝔸 E),
    thetaLarge W' V' 𝔠 v (stdRowDatum σ' 𝔠.semilocalChar (y * (adaptedFrame 𝔠.readsAt A).dualI))
    (lineRadical A q * A.levi (Matrix.GeneralLinearGroup.scalar Unit u, g)) ∂radicalMeasure

/-- For every matrix `y` the datum `planeDatum 𝔠 A σ' v y` (`v` at the real places, the standard
datum of `y` composed with the projection to `W` at the places `𝔠.ramifiedPlaces`) has zero source
term at `0` along the splitting `A` of the plane of `W'`. -/
theorem homSlice_zero_planeDatum (σ' : b ⊕ r' ≃ n') (v : PairFock E s' t')
    (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)) : A.homSlice V' 0 (planeDatum 𝔠 A σ' v y) = 0 := by
  set N : IntegralFrame (LocProd 𝔠.ramifiedPlaces) n' n Unit := adaptedFrame 𝔠.readsAt A
  -- The function is 0 at every `w` with `w * N.K = 0`: on its support the rows of `y * N.dualI` and
  -- `w` form a left invertible matrix, which cannot kill `N.K`.
  have h_zero (w : Matrix r' n' (LocProd 𝔠.ramifiedPlaces)) (hw : w * N.K = 0) :
      stdRowDatum σ' 𝔠.semilocalChar (y * N.dualI) w = 0 := by
    by_contra h_ne
    obtain ⟨-, L, -, hL⟩ : IsPrimitiveMatrix O (((y * N.dualI).fromRows w).submatrix σ'.symm id) :=
      isPrimitiveMatrix_of_stdColDatum_ne_zero .one _ h_ne
    have hK : N.K = 0 := by
      rw [← Matrix.one_mul N.K, ← hL, Matrix.mul_assoc]
      simp [submatrix_id_mul, Matrix.mul_assoc, hw, N.blockRelations.dualI_mul_K]
    simpa [hK] using N.blockRelations.dualK_mul_K
  -- So the function agrees there with the one attached to the zero function on `Hom(W, V')`.
  have h_std (w : Matrix r' n' (LocProd 𝔠.ramifiedPlaces)) (hw : w * N.K = 0) :
      stdRowDatum σ' 𝔠.semilocalChar (y * N.dualI) w = N.stdDatum 0 w := by
    simp [h_zero w hw, IntegralFrame.stdDatum]
  simpa [localDatum, ← Pi.zero_def] using 𝔠.readsAt.homSlice_localDatum A V' (G := 0)
    (stdRowDatum_mem σ' 𝔠.semilocalChar) 0 v fun w hw ↦ h_std w (by simpa using hw)

/-- A shortcut for instance search, for the Haar measures on `maxCompact E t` below. -/
local instance : LocallyCompactSpace (maxCompact E t) := inferInstance

/-- Let `A` and `X` be base-adapted splittings of a plane off `W'` and `V'`, let `v` be a Schwartz
vector (all Fock moments finite), let `y` be a matrix over the completions at the places
`𝔠.ramifiedPlaces`, and let `g ∈ U(W)` and `σ : b ⊕ r ≃ n`. Then for every character `ψ`, every side
`β` and every `x > 0`, the map that sends `(h, k, a)` to the theta kernel `pairTheta W V ψ ψ` at
`(g, h)` of the datum with real part `coneIntegrand A X μ β x v (k, a)` (the real line term of side
`β` at `a` of `k v`, times `|a| ^ x` and `∏_w (a_w / |a_w|) ^ (2 μ w)`), part
`stdRowDatum σ 𝔠.semilocalChar y` at `𝔠.ramifiedPlaces` and the vacuum elsewhere is integrable. The
measure is the quotient measure on `[U(V)]` times Haar measure on the cone (the maximal compact
subgroup of `U(V')` times the real ideles). -/
theorem integrable_theta_cone [IsBaseAdapted X]
    (σ : b ⊕ r ≃ n) (ψ : AutChar E) (β : Bool) {x : ℝ} (hx : 0 < x)
    {v : PairFock E s' t'} (hv : IsSchwartzVector v) (y : Matrix b n (LocProd 𝔠.ramifiedPlaces))
      (g : G E s) :
    Integrable (fun p : G E t × maxCompact E t' × (InfinitePlace E → ℂ)ˣ ↦ pairTheta W V ψ ψ
        (localDatum W V (coneIntegrand A X μ β x v p.2) (stdRowDatum σ 𝔠.semilocalChar y) 𝔠.readsAt)
          (g, p.1))
      (V.quotMeasure.prod (haar.prod haar)) := by
  -- The kernel is bounded on `[U(V)]` by a moment of the real datum.
  let kernel (h : G E t) (w : PairFock E s t) : ℂ :=
    pairTheta W V ψ ψ (localDatum W V w (stdRowDatum σ 𝔠.semilocalChar y) 𝔠.readsAt) (g, h)
  obtain ⟨Q, D, hD, h_decay⟩ : ∃ (Q : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ (h : G E t) (w : PairFock E s t),
      Fock.fockMoment Q w ≠ ⊤ → ‖kernel h w‖ ≤ D * (Fock.fockMoment Q w).toReal := by
    have h_std : stdRowDatum σ 𝔠.semilocalChar y ∈ schwartzBruhat fun x ↦ HasLeftInv x.transpose :=
      stdRowDatum_mem σ 𝔠.semilocalChar (s := y)
    have ⟨_, _, h_support⟩ := h_std
    obtain ⟨B, Q, C, h_decay⟩ := pairTheta_decay_of_onto W V ψ ψ _ 𝔠.readsAt.disjoint_star
      (𝔠.readsAt.isSchwartzBruhat h_std) (fun _ h ↦ h_support h) 0
    refine ⟨Q, |C * W.height g ^ B|, abs_nonneg _, fun h w hw ↦ ?_⟩
    calc _ ≤ C * (Fock.fockMoment Q w).toReal * W.height g ^ B := by simpa using h_decay w g h hw
      _ ≤ _ := by grw [mul_right_comm, le_abs_self (C * _)]
  obtain ⟨φ, hφ_int, hφ⟩ : ∃ φ : maxCompact E t' × (InfinitePlace E → ℂ)ˣ → ℝ,
      Integrable φ (haar.prod haar) ∧
      ∀ q, Fock.fockMoment Q (coneIntegrand A X μ β x v q) ≤ ‖φ q‖ₑ :=
    exists_integrable_fockMoment_coneIntegrand_le A X μ β hx hv Q
  have h_bound (h : G E t) (q : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) :
      ‖kernel h (coneIntegrand A X μ β x v q)‖ ≤ D * ‖φ q‖ :=
    calc _ ≤ D * (Fock.fockMoment Q (coneIntegrand A X μ β x v q)).toReal :=
        h_decay _ _ ((hφ q).trans_lt enorm_lt_top).ne
      _ ≤ _ := by grw [ENNReal.toReal_mono enorm_ne_top (hφ q), toReal_enorm]
  have h_cont : Continuous (Function.uncurry kernel) := by
    simp only [kernel, pairTheta]
    fun_prop
  -- The bound is integrable; the integrand is measurable as the kernel is continuous.
  refine ((hφ_int.comp_snd _).norm.const_mul D).mono' ?_ (.of_forall fun p ↦ h_bound p.1 p.2)
  exact h_cont.comp_aestronglyMeasurable₂ aestronglyMeasurable_id.comp_fst
    (integrable_coneIntegrand A X μ β hx hv).1.aestronglyMeasurable.comp_snd

/-! ### Tate's integral on the line -/

variable (ν) in
/-- The function on the line in Tate's integral: for an adele `α` and a point `k` of the maximal
compact subgroup of `U(V')`, the theta kernel of `(W, V)` at `(g, h)` on `lineTerm A X β α (k f)`,
the datum of `(W, V)` read off `k f` at the point `α` of the line, all characters being `ν⁻¹`
twisted as in `rankTwist`. For `β = false` it is the function on the other side of Poisson's
formula. -/
def lineValue (f : 𝒮 (W'.hom V')) (g : G E s) (β : Bool) (α : 𝔸 E) (h : G E t)
    (k : maxCompact E t') : ℂ :=
  pairTheta W V (rankTwist ν⁻¹ n) (rankTwist ν⁻¹ n)
    (lineTerm A X β α (pairWeil W' V' (rankTwist ν⁻¹ n') (rankTwist ν⁻¹ n') (1, k) f)) (g, h)

omit [IsBaseAdapted A] in
/-- Let `rk W = card n` be even, and `u = 1` or `rk V = card n`. The Levi points `(u, g)` of `U(W')`
and `(a, h)` of `U(V')` move the line by `a u`. Move `f` by these points and `k`, take its line term
at `ξ` (`lineTerm A X β ξ`, a datum of `(W, V)`) and multiply the theta value of this term by the
module `|a| ^ (rk V + 1)` of the parabolic subgroup. The result is `ν̃(a u) |a u| ^ (e + 1)` times
`lineValue` at `ξ * poissonVariable β (a u)`, where `lineValue` is the theta kernel at `(g, h)` of
the line term of `k f`. Here `e = rk V - card n / 2` and `ν̃` is the base change of `ν`. The Poisson
variable is `a u`, or its conjugate inverse on the other side of Poisson's formula (`β = false`),
where the exponent is `e`. -/
theorem theta_lineTerm_levi (hn : 2 ∣ card n) {u : (𝔸 E)ˣ} (hu : u = 1 ∨ card r = card n)
    (f : 𝒮 (W'.hom V')) (g : G E s) (β : Bool) (ξ : 𝔸 E) (a : (𝔸 E)ˣ) (h : G E t)
    (k : maxCompact E t') :
    (ideleAbs a ^ (card r + 1) : ℝ) * θ (W.hom V) (lineTerm A X β ξ
        (pairWeil W' V' (rankTwist ν⁻¹ n') (rankTwist ν⁻¹ n')
          (A.levi (Matrix.GeneralLinearGroup.scalar Unit u, g), lineLevi X (a, h) * k) f)) =
      ν.baseChange.val (a * u) * lineValue ν A X f g β (ξ * poissonVariable E β (a * u)) h k *
        (ideleAbs (a * u) ^ ((card r - card n / 2 : ℤ) + cond β 1 0 : ℝ) : ℝ) := by
  obtain ⟨d, hd⟩ := hn
  have h_point : (if β then ↑(a * u) else star ↑(a * u)⁻¹ : 𝔸 E) = poissonVariable E β (a * u) := by
    cases β <;> simp [poissonVariable_true, poissonVariable_false]
  -- The Levi points move the line term to `a u` and multiply its theta value by a factor `c`.
  let c : ℂ := √(ideleAbs u) ^ (2 * card r + 2) /
    ((ν⁻¹).baseChange.val (a * u) * √(ideleAbs (a * u)) ^ (card n + if β then 0 else 2))
  have h_move : θ (W.hom V) (lineTerm A X β ξ (pairWeil W' V' (rankTwist ν⁻¹ n') (rankTwist ν⁻¹ n')
        (A.levi (.scalar Unit u, g), lineLevi X (a, h) * k) f)) =
      c * lineValue ν A X f g β (ξ * poissonVariable E β (a * u)) h k := by
    have h_split : ((A.levi (.scalar Unit u, g), lineLevi X (a, h) * k) : G E s' × G E t') =
        (A.levi (.scalar Unit u, g), lineLevi X (a, h)) * (1, k.val) := by simp
    rw [h_split, ← rep_apply_apply, lineValue, rankTwist_eq_mul_of_splitting A, card_unit, pow_one,
      lineTerm_pairWeil_levi A X hu, spaceChar_rankTwist ⟨d, hd⟩, map_smul, smul_eq_mul, h_point,
      pairTheta]
  -- It remains to compare the factors.
  set e : ℝ := (card r - card n / 2 : ℤ) + cond β 1 0
  have h_module : ideleAbs a ^ (card r + 1) * √(ideleAbs u) ^ (2 * card r + 2) =
      ideleAbs (a * u) ^ e * √(ideleAbs (a * u)) ^ (card n + if β then 0 else 2) := by
    have h_exp : e + 1 / 2 * (card n + if β then 0 else 2 : ℕ) = (card r + 1 : ℕ) := by
      cases β <;> simp [e, hd] <;> ring
    calc _ = ideleAbs (a * u) ^ (card r + 1) := by
          rw [← mul_add_one 2 (card r), pow_mul, sq_sqrt ideleAbs_pos.le, map_mul, mul_pow]
      _ = _ := by
        rw [← rpow_natCast, ← h_exp, rpow_add ideleAbs_pos, sqrt_eq_rpow,
          rpow_mul_natCast ideleAbs_pos.le]
  have h_factor : (ideleAbs a ^ (card r + 1) : ℝ) * c =
      ν.baseChange.val (a * u) * (ideleAbs (a * u) ^ e : ℝ) := by
    have h_ne : (√(ideleAbs (a * u)) : ℂ) ≠ 0 := ofReal_ne_zero.2 (sqrt_pos.2 ideleAbs_pos).ne'
    rw [← mul_div_assoc, ← ofReal_pow, ← ofReal_mul, h_module]
    simp [circleChar_inv_apply, field]
  rw [h_move, ← mul_assoc, h_factor, mul_right_comm]

omit [IsBaseAdapted A] in
/-- Poisson's formula on the line. Let `E` be a CM field with Weil data, let `A` and `X` split a
hyperbolic plane off `W'` and `V'`, and let `rk W = card n` be even. Let
`lineValue ν A X f g β α h k` be the theta kernel of `(W, V)` at `(g, h)` on the line term at `α` of
`k f`, with characters `ν⁻¹` twisted as in `rankTwist`, in the model `β`. If `lineValue` vanishes at
`0` for both `β`, then for every idele `a` the sum over `ξ ∈ Eˣ` of the `β = true` value at `ξ a`,
times `|a|`, equals the sum over `ξ ∈ Eˣ` of the `β = false` value at `ξ ā⁻¹`. -/
theorem tsum_lineValue_poisson (hn : 2 ∣ card n) {f : 𝒮 (W'.hom V')} {g : G E s} {h : G E t}
    {k : maxCompact E t'} (h_zero : ∀ β : Bool, lineValue ν A X f g β 0 h k = 0) (a : (𝔸 E)ˣ) :
    (∑' ξ : Eˣ, lineValue ν A X f g true (toAdele ξ.val * a) h k) * ideleAbs a =
      ∑' ξ : Eˣ, lineValue ν A X f g false (toAdele ξ.val * poissonVariable E false a) h k := by
  let e : ℤ := card r - card n / 2
  -- The sums over `Eˣ` are sums over `E`.
  have h_units (β : Bool) :
      ∑' ξ : Eˣ, lineValue ν A X f g β (toAdele ξ.val * poissonVariable E β a) h k =
        ∑' ξ : E, lineValue ν A X f g β (toAdele ξ * poissonVariable E β a) h k :=
    Units.val_injective.tsum_eq
      (f := fun ξ : E ↦ lineValue ν A X f g β (toAdele ξ * poissonVariable E β a) h k)
      fun ξ hξ ↦ Ne.isUnit fun hξ_zero ↦ hξ (by simp [hξ_zero, h_zero])
  -- Apply `tsum_lineTerm` to the translate of `f` by the Levi point of `a`.
  have h_poisson :
      ν.baseChange.val a * (∑' ξ : E, lineValue ν A X f g true
          (toAdele ξ * poissonVariable E true a) h k) * (ideleAbs a ^ (e + 1 : ℝ) : ℝ) =
        ν.baseChange.val a * (∑' ξ : E, lineValue ν A X f g false
          (toAdele ξ * poissonVariable E false a) h k) * (ideleAbs a ^ (e + 0 : ℝ) : ℝ) := by
    let F : 𝒮 (W'.hom V') := pairWeil W' V' (rankTwist ν⁻¹ n') (rankTwist ν⁻¹ n')
      (A.levi (Matrix.GeneralLinearGroup.scalar Unit 1, g), lineLevi X (a, h) * k) f
    have h_levi (β : Bool) :
        (ideleAbs a ^ (card r + 1) : ℝ) * ∑' ξ : E, θ (W.hom V) (lineTerm A X β (toAdele ξ) F) =
          ν.baseChange.val a * (∑' ξ : E, lineValue ν A X f g β
            (toAdele ξ * poissonVariable E β a) h k) * (ideleAbs a ^ (e + cond β 1 0 : ℝ) : ℝ) := by
      simp only [← tsum_mul_left, ← tsum_mul_right]
      refine tsum_congr fun ξ ↦ ?_
      simpa only [mul_one] using theta_lineTerm_levi A X hn (.inl rfl) f g β (toAdele ξ) a h k
    -- `tsum_lineTerm` is Poisson's formula for the line terms of `F`.
    calc _ = (ideleAbs a ^ (card r + 1) : ℝ) *
          ∑' ξ : E, θ (W.hom V) (lineTerm A X true (toAdele ξ) F) := (h_levi true).symm
      _ = _ := by rw [tsum_lineTerm A X false]; exact h_levi false
  have h_ne : (ν.baseChange.val a : ℂ) * (ideleAbs a ^ (e : ℝ) : ℝ) ≠ 0 :=
    mul_ne_zero (Circle.coe_ne_zero _) (ofReal_ne_zero.2 (rpow_pos_of_pos ideleAbs_pos _).ne')
  rw [← h_units, ← h_units, rpow_add_one ideleAbs_pos.ne', add_zero, ofReal_mul,
    poissonVariable_true] at h_poisson
  -- Cancel the common factor `ν̃(a) |a| ^ e`.
  exact mul_left_cancel₀ h_ne (by linear_combination h_poisson)

variable (ν) in
/-- The integrand of Tate's integral `𝒵(x)` at `p = ((a, h), k)`, for an idele `a`, a point `h` of
`U(V)` and a point `k` of the maximal compact subgroup of `U(V')`: it is `ν̃(a u) |a u| ^ x` times
the sum of `lineValue` at `(h, k)` over `Eˣ a u`. -/
def zetaIntegrand (f : 𝒮 (W'.hom V')) (g : G E s) (u : (𝔸 E)ˣ) (x : ℝ)
    (p : ((𝔸 E)ˣ × G E t) × maxCompact E t') : ℂ :=
  ν.baseChange.val (p.1.1 * u) *
    (∑' ξ : Eˣ, lineValue ν A X f g true (toAdele ξ.val * (p.1.1 * u : (𝔸 E)ˣ)) p.1.2 p.2) *
    (ideleAbs (p.1.1 * u) ^ x : ℝ)

omit [IsBaseAdapted A] in
/-- Let `rk W` be even and suppose that `lineValue` vanishes at `0` on both sides. Then Tate's
integrand at `x` (for `β = true`) or `1 - x` (for `β = false`) is the sum over `ξ : Eˣ` of
`ν̃(z) |z| ^ x` times `lineValue` on the side `β` at `z`, where `z` is `ξ` times the value at
`a u` of `poissonVariable E β`. -/
theorem zetaIntegrand_eq_tsum (hn : 2 ∣ card n) {f : 𝒮 (W'.hom V')} {g : G E s} {h : G E t}
    {k : maxCompact E t'} (h_zero : ∀ β : Bool, lineValue ν A X f g β 0 h k = 0) (u a : (𝔸 E)ˣ)
    (β : Bool) (x : ℝ) :
    zetaIntegrand ν A X f g u (cond β x (1 - x)) ((a, h), k) = ∑' ξ : Eˣ,
      ν.baseChange.val (principalAdeleUnit ξ * poissonVariable E β (a * u)) *
        lineValue ν A X f g β (principalAdeleUnit ξ * poissonVariable E β (a * u) : (𝔸 E)ˣ) h k *
        (ideleAbs (principalAdeleUnit ξ * poissonVariable E β (a * u)) ^ x : ℝ) := by
  -- The character and the module are trivial on principal ideles. For `β = false` the sum is then
  -- turned to the other side by Poisson's formula.
  have h_char (ξ : Eˣ) : ν.baseChange.val (principalAdeleUnit ξ) = 1 := ν.baseChange.prop _ ⟨ξ, rfl⟩
  have h_abs (ξ : Eˣ) : ideleAbs (principalAdeleUnit ξ) = 1 := ideleAbs_toAdele ξ
  simp only [zetaIntegrand, map_mul ν.baseChange.val (principalAdeleUnit _),
    map_mul ideleAbs (principalAdeleUnit _), h_char, h_abs, one_mul, tsum_mul_left, tsum_mul_right,
    baseChange_poissonVariable]
  cases β
  · have h_poisson :
        (∑' ξ : Eˣ, lineValue ν A X f g true (toAdele ξ.val * (a * u : (𝔸 E)ˣ)) h k) *
            ideleAbs (a * u) =
          ∑' ξ : Eˣ, lineValue ν A X f g false
            (principalAdeleUnit ξ * poissonVariable E false (a * u) : (𝔸 E)ˣ) h k :=
      tsum_lineValue_poisson A X hn h_zero (a * u)
    rw [← h_poisson, ideleAbs_poissonVariable_false, Bool.cond_false, rpow_sub ideleAbs_pos,
      rpow_one, inv_rpow ideleAbs_pos.le]
    push_cast
    ring
  · simp [poissonVariable_true]

variable [IsBaseAdapted X]

variable (W V 𝔠) in
/-- The theta kernel of `(W, V)` at `(g, h)` on the standard datum of `y`, as a linear form in the
real vector. -/
def stdKernelForm (σ : b ⊕ r ≃ n) (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)) (g : G E s)
    (h : G E t) :
    PairFock E s t →L[ℂ] ℂ :=
  θ (W.hom V) ∘L pairWeil W V (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n) (g, h) ∘L
    (W.hom V).integrated.flip (namedVector W V (stdRowDatum σ 𝔠.semilocalChar y) 𝔠.readsAt)

lemma stdKernelForm_apply (σ : b ⊕ r ≃ n) (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)) (g : G E s)
    (h : G E t) (v : PairFock E s t) :
    stdKernelForm 𝔠 W V σ y g h v = pairTheta W V (rankTwist 𝔠.character⁻¹ n)
      (rankTwist 𝔠.character⁻¹ n)
      (localDatum W V v (stdRowDatum σ 𝔠.semilocalChar y) 𝔠.readsAt) (g, h) :=
  rfl

/-- The integral over `[U(V)]` of the kernel `stdKernelForm` on a real vector `v` is the theta
integral of `(W, V)` on `v` and the standard datum of `y`. -/
lemma integral_stdKernelForm (σ : b ⊕ r ≃ n) (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)) (g : G E s)
    (v : PairFock E s t) :
    ∫ h : G E t, stdKernelForm 𝔠 W V σ y g h v ∂V.quotMeasure =
      thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar y) g :=
  rfl

/-- The datum factors. For integral `y`, the function of Tate's integral of `planeDatum 𝔠 A σ' v y`
at `α α₀`, where `α₀ = scaleIdele E`, is `l β * γ` times the finite factor `lineFinFactor` shifted
by the uniformiser `ϖ` times the kernel of `(W, V)` on the real line term at `α∞` of `k v`. Here `l`
does not depend on the character, and `|γ| ^ 2 = (∏ q_w)⁻¹`. -/
theorem exists_lineValue_eq [Fintype b] [DecidableEq b]
    (σ' : b ⊕ r' ≃ n') (σ : b ⊕ r ≃ n) (μ : InfinitePlace E → ℤ) :
    ∃ l : Bool → ℂˣ, ∀ 𝔠 : SplitTameChar E μ, ∃ γ : ℂ,
      ‖γ‖ ^ 2 = (∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ))⁻¹ ∧
      ∀ (v : PairFock E s' t') (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)), IsIntMatrix O y →
        ∀ (g : G E s) (β : Bool) (α : 𝔸 E) (h : G E t) (k : maxCompact E t'),
          lineValue 𝔠.character A X (planeDatum 𝔠 A σ' v y) g β (α * scaleIdele E) h k =
            l β * γ * lineFinFactor 𝔠 ϖ.val α.2 *
              stdKernelForm 𝔠 W V σ y g h (lineTermReal A X β α.1
                (realPairWeil (targetWeight n' μ) 0 (1, k.val.1) v)) := by
  classical
  obtain ⟨l, h_terms⟩ := exists_lineTerm_localDatum A σ' σ X
  refine ⟨l, fun 𝔠 ↦ ?_⟩
  obtain ⟨γ, hγ, h_term⟩ := h_terms 𝔠.readsAt 𝔠.tameLocalChar
  refine ⟨γ, ?_, fun v y hy g β α h k ↦ ?_⟩
  · simp [hγ, TameLocalChar.ResidueRing, Nat.card_pi, card_ResField]
  -- The finite part of `k` fixes the datum, and its real part moves `v`; then the line term of the
  -- moved datum is read off from `exists_lineTerm_localDatum`.
  have h_int : IsIntMatrix O (y * (adaptedFrame 𝔠.readsAt A).dualI) :=
    hy.mul (adaptedFrame 𝔠.readsAt A).blockRelations.isIntMatrix_dualI
  have h_move : pairWeil W' V' (rankTwist 𝔠.character⁻¹ n') (rankTwist 𝔠.character⁻¹ n') (1, k.val)
      (planeDatum 𝔠 A σ' v y) =
      planeDatum 𝔠 A σ' (realPairWeil (targetWeight n' μ) 0 (1, k.val.1) v) y := by
    rw [show ((1, k.val) : G E s' × G E t') = (1, k.val.1, 1) * (1, 1, k.val.2) by simp,
      ← rep_apply_apply, pairWeil_stdRowDatum_eq_self σ' h_int k.prop.2 rfl]
    exact pairWeil_integrated_right _ _ k.val.1 v
  have h_line (v' : PairFock E s' t') :
      lineTerm A X β (α * scaleIdele E) (planeDatum 𝔠 A σ' v' y) =
        (l β * γ * lineFinFactor 𝔠 ϖ.val α.2) •
          localDatum W V (lineTermReal A X β α.1 v') (stdRowDatum σ 𝔠.semilocalChar y)
            𝔠.readsAt := by
    -- At `α α₀` the adele in the formula for the line term is `α α₀ α₀⁻¹ = α`.
    simpa only [Units.mul_inv_cancel_right, lineFinFactor, ite_isIntegralUnit_eq_ite_invOnUnits_div]
      using h_term y β v' (α * scaleIdele E)
  rw [lineValue, h_move, h_line, stdKernelForm_apply]
  simp only [pairTheta, map_smul, smul_eq_mul]

variable (𝔠) in
/-- The theta kernel of `(W, V)` at `(g, h)` on the cone integrand with exponent `x` at `(k, a)`,
for `p = (h, k, a)`. -/
def coneKernel (σ : b ⊕ r ≃ n) (v : PairFock E s' t') (y : Matrix b n (LocProd 𝔠.ramifiedPlaces))
    (g : G E s) (β : Bool) (x : ℝ) (p : G E t × maxCompact E t' × (InfinitePlace E → ℂ)ˣ) : ℂ :=
  stdKernelForm 𝔠 W V σ y g p.1 (coneIntegrand A X μ β x v p.2)

/-- The measure of the unfolded integral: idele classes, `[U(V)]` and the maximal compact subgroup
of `U(V')`. -/
abbrev zetaMeasure (V : Space E r t) (t' : r' → ℤˣ) :
    Measure (((𝔸 E)ˣ × G E t) × maxCompact E t') :=
  (((principalAdeleUnits E).quotMeasure haar).prod V.quotMeasure).prod haar

variable (𝔠) in
/-- For every side `β` of Poisson's formula on the line, the function of Tate's integral for `f` at
`α α₀`, where `α₀ = scaleIdele E`, is a constant `κ β` times the finite factor of `𝔠` shifted by
the uniformiser `ϖ` times the theta kernel of `(W, V)` on the standard datum of `y` and the real
line term `lineTermReal` at `α∞` of `k v` (the Weil action of the real component of `k` on `v`). -/
def LineValueFactors (σ : b ⊕ r ≃ n) (v : PairFock E s' t')
    (y : Matrix b n (LocProd 𝔠.ramifiedPlaces))
    (g : G E s) (f : 𝒮 (W'.hom V')) (κ : Bool → ℂ) : Prop :=
  ∀ (β : Bool) (α : 𝔸 E) (h : G E t) (k : maxCompact E t'),
    lineValue 𝔠.character A X f g β (α * scaleIdele E) h k =
      κ β * lineFinFactor 𝔠 ϖ.val α.2 * stdKernelForm 𝔠 W V σ y g h (lineTermReal A X β α.1
        (realPairWeil (targetWeight n' μ) 0 (1, k.val.1) v))

/-- The idele `c⁻¹ α₀`, `α₀ = scaleIdele E`, by which Tate's integral is translated; in use `c` is a
finite idele with `lineFinFactor 𝔠 ϖ a = lineFinFactor 𝔠 1 (a * c)`
(`exists_lineFinFactor_uniformizer_eq`). -/
abbrev shiftIdele (c : (𝔸f E)ˣ) : (𝔸 E)ˣ := finIdeleIncl c⁻¹ * scaleIdele E

/-! ### The cone kernel and the unfolded integral -/

section
variable {σ : b ⊕ r ≃ n} {v : PairFock E s' t'} (y : Matrix b n (LocProd 𝔠.ramifiedPlaces))
  (g : G E s) (β : Bool)

/-- The cone kernel at a triple `p = (h, k, a)` (so `h = p.1`, `k = p.2.1`, `a = p.2.2`) is
`ν̃(a) |a| ^ x` times the kernel on the real line term at `a` of `k v`, where `ν̃` is the base
change of `ν = 𝔠.character`. Only the real component `k.val.1` of `k` acts on `v`. -/
theorem coneKernel_eq (x : ℝ) (p : G E t × maxCompact E t' × (InfinitePlace E → ℂ)ˣ) :
    coneKernel 𝔠 A X σ v y g β x p =
      stdKernelForm 𝔠 W V σ y g p.1 (lineTermReal A X β p.2.2
          (realPairWeil (targetWeight n' μ) 0 (1, p.2.1.val.1) v)) *
        𝔠.character.baseChange.val (realIdele p.2.2) * (ideleAbs (realIdele p.2.2) ^ x : ℝ) := by
  have h_char : (𝔠.character.baseChange.val (realIdele p.2.2) : ℂ) =
      ∏ w : InfinitePlace E, (p.2.2.val w / ‖p.2.2.val w‖) ^ (2 * μ w) :=
    𝔠.hasWeight.baseChange_apply_inf p.2.2
  rw [coneKernel, coneIntegrand, map_smul, h_char, smul_eq_mul]
  ring

/-- For a Schwartz vector `v` and an exponent `x > 0` the cone kernel is integrable over `[U(V)]`
and the cone. -/
theorem integrable_coneKernel (hv : IsSchwartzVector v) {x : ℝ} (hx : 0 < x) :
    Integrable (coneKernel 𝔠 A X σ v y g β x) (V.quotMeasure.prod (haar.prod haar)) := by
  unfold coneKernel
  simp only [stdKernelForm_apply]
  exact integrable_theta_cone A X σ (rankTwist 𝔠.character⁻¹ n) β hx hv y g

/-- For a Schwartz vector and `x > 0` the integral of the cone kernel is the theta integral of
`(W, V)` at the cone integral, the integral of the cone integrand. -/
theorem integral_coneKernel (hv : IsSchwartzVector v) {x : ℝ} (hx : 0 < x) :
    ∫ p : G E t × maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
      coneKernel 𝔠 A X σ v y g β x p ∂V.quotMeasure.prod (haar.prod haar) =
      thetaLarge W V 𝔠 (∫ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
        coneIntegrand A X μ β x v p ∂haar.prod haar)
        (stdRowDatum σ 𝔠.semilocalChar y) g := by
  rw [integral_prod _ (integrable_coneKernel A X y g β hv hx), ← integral_stdKernelForm]
  exact integral_congr_ae (.of_forall fun h ↦ (stdKernelForm 𝔠 W V σ y g h).integral_comp_comm
    (integrable_coneIntegrand A X μ β hx hv).1)

/-- For a Schwartz vector the integral of the cone kernel is continuous in the exponent `x` on every
interval `[1, x₁]`. -/
theorem continuousOn_integral_coneKernel (hv : IsSchwartzVector v) {x₁ : ℝ} (hx₁ : 1 ≤ x₁) :
    ContinuousOn
      (fun x : ℝ ↦ ∫ p : G E t × maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
        coneKernel 𝔠 A X σ v y g β x p ∂V.quotMeasure.prod (haar.prod haar))
      (Icc 1 x₁) := by
  -- In `x` the integral is a Mellin transform that converges at both ends of the interval.
  have h_int {x : ℝ} (hx : 0 < x) :
      Integrable (coneKernel 𝔠 A X σ v y g β x) (V.quotMeasure.prod (haar.prod haar)) :=
    integrable_coneKernel A X y g β hv hx
  simp only [funext (coneKernel_eq A X y g β _)] at h_int ⊢
  obtain ⟨-, h_cont, -⟩ := analyticOnNhd_integral_mul_rpow (fun _ ↦ ideleAbs_pos)
    (continuous_ideleAbs_realIdele.measurable.comp measurable_snd.snd)
    (h_int one_pos).hasFiniteIntegral (h_int (one_pos.trans_le hx₁))
  exact h_cont

end
section
variable {σ : b ⊕ r ≃ n} {v : PairFock E s' t'} {y : Matrix b n (LocProd 𝔠.ramifiedPlaces)}
  {g : G E s} {f : 𝒮 (W'.hom V')} {κ : Bool → ℂ} {c : (𝔸f E)ˣ}

/-- If the datum `f` factors along the line (`LineValueFactors`) for the split tame character `𝔠`,
neither side of Poisson's formula on the line has a term at `0`. -/
theorem lineValue_zero_of_factor (h_factor : LineValueFactors 𝔠 A X σ v y g f κ) (β : Bool)
    (h : G E t) (k : maxCompact E t') : lineValue 𝔠.character A X f g β 0 h k = 0 := by
  simpa [lineFinFactor_zero] using h_factor β 0 h k

/-- Let the datum `f` factor along the line (`LineValueFactors`) for the split tame character `𝔠`,
and let the translation by `c` remove the uniformiser from the finite factor. Then one term of
Tate's integrand at the idele `α K`, with `K = c⁻¹ α₀` and `α₀ = scaleIdele E`, is the cone kernel
at the real part of `α` times a function of its finite part. -/
theorem baseChange_mul_lineValue_eq_coneKernel_mul (h_factor : LineValueFactors 𝔠 A X σ v y g f κ)
    (hc : ∀ a : 𝔸f E, lineFinFactor 𝔠 ϖ.val a = lineFinFactor 𝔠 1 (a * c))
    (β : Bool) (x : ℝ) (α : (𝔸 E)ˣ) (h : G E t) (k : maxCompact E t') :
    let K : (𝔸 E)ˣ := shiftIdele c
    𝔠.character.baseChange.val (α * K) * lineValue 𝔠.character A X f g β (α * K : (𝔸 E)ˣ) h k *
        (ideleAbs (α * K) ^ x : ℝ) =
      coneKernel 𝔠 A X σ v y g β x (h, k, (ideleParts E α).1) *
        (κ β * 𝔠.character.baseChange.val K * (ideleAbs K ^ x : ℝ) *
          finTateIntegrand 𝔠 x (ideleParts E α).2) := by
  intro K
  obtain ⟨⟨α₁, α₂⟩, rfl⟩ := (ideleParts E).symm.surjective α
  have h_parts : (ideleParts E).symm (α₁, α₂) = realIdele α₁ * finIdeleIncl α₂ := by
    simpa using (realIdele_mul_finIdeleIncl_ideleParts ((ideleParts E).symm (α₁, α₂))).symm
  have h_value :
      lineValue 𝔠.character A X f g β (realIdele α₁ * finIdeleIncl α₂ * K : (𝔸 E)ˣ) h k =
        κ β * lineFinFactor 𝔠 1 α₂ * stdKernelForm 𝔠 W V σ y g h (lineTermReal A X β α₁
          (realPairWeil (targetWeight n' μ) 0 (1, k.val.1) v)) := by
    simpa [K, hc, ← mul_assoc] using h_factor β (α₁, α₂ * c⁻¹) h k
  have h_char : (𝔠.character.baseChange.val (realIdele α₁ * finIdeleIncl α₂ * K) : ℂ) =
      𝔠.character.baseChange.val (realIdele α₁) * 𝔠.character.baseChange.finPart α₂ *
        𝔠.character.baseChange.val K := by
    simp [HeckeChar.finPart]
  have h_abs : ideleAbs (realIdele α₁ * finIdeleIncl α₂ * K) ^ x =
      ideleAbs (realIdele α₁) ^ x * finIdeleAbs α₂ ^ x * ideleAbs K ^ x := by
    rw [map_mul, mul_rpow ideleAbs_pos.le ideleAbs_pos.le, map_mul,
      mul_rpow ideleAbs_pos.le ideleAbs_pos.le]
    rfl
  rw [ContinuousMulEquiv.apply_symm_apply, h_parts, h_value, h_char, h_abs, coneKernel_eq,
    finTateIntegrand]
  push_cast
  ring

/-- Let `𝔠 : SplitTameChar E μ` be a split tame character and `v` a real datum. Let the datum `f`
factor along the line with constants `κ` (`LineValueFactors`), let the translation by `c` remove the
uniformiser from the finite factor, let `rk W` be even, let all Fock moments of `v` be finite and
let `ρ` be a Haar measure on the finite ideles such that Haar measure on the ideles, read in
`poissonVariable E β` (`a` or `ā⁻¹`) and split by `ideleParts`, is `haar.prod ρ`. Then for `x > 1`
Tate's integral at `x` (for `β = true`) or at `1 - x` (for `β = false`) converges, and it is the
integral of the cone kernel times `L^S(x, ν)` and explicit factors, for `ν = 𝔠.character` and
`S = 𝔠.ramifiedPlaces`. -/
theorem integral_zetaIntegrand_of_one_lt [Fintype b] [DecidableEq b]
    (h_factor : LineValueFactors 𝔠 A X σ v y g f κ)
    (hc : ∀ a : 𝔸f E, lineFinFactor 𝔠 ϖ.val a = lineFinFactor 𝔠 1 (a * c))
    (hn : 2 ∣ card n) (hv : IsSchwartzVector v) (u : (𝔸 E)ˣ)
    {β : Bool} {ρ : Measure (𝔸f E)ˣ} [IsHaarMeasure ρ]
    (hρ : MeasurePreserving ((poissonVariable E β).trans (ideleParts E)) haar (haar.prod ρ))
    {x : ℝ} (hx : 1 < x) :
    let K : (𝔸 E)ˣ := shiftIdele c
    Integrable (zetaIntegrand 𝔠.character A X f g u (cond β x (1 - x))) (zetaMeasure V t') ∧
      ∫ p : ((𝔸 E)ˣ × G E t) × maxCompact E t',
        zetaIntegrand 𝔠.character A X f g u (cond β x (1 - x)) p ∂zetaMeasure V t' =
        (∫ p : G E t × maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
          coneKernel 𝔠 A X σ v y g β x p ∂V.quotMeasure.prod (haar.prod haar)) *
          (κ β * 𝔠.character.baseChange.val K * (ideleAbs K ^ x : ℝ) *
            (𝔠.character.L 𝔠.ramifiedPlaces x * ρ.real (idelesUnitOff (K := E) ∅))) := by
  intro K
  obtain ⟨h_tate_int, h_tate⟩ : Integrable (finTateIntegrand 𝔠 x) ρ ∧
      ∫ a, finTateIntegrand 𝔠 x a ∂ρ = 𝔠.character.L 𝔠.ramifiedPlaces x * ρ.real
        (idelesUnitOff (K := E) ∅) :=
    integral_finTateIntegrand 𝔠 ρ hx
  rw [← h_tate, ← integral_const_mul]
  -- It remains to see that each term of the sum over `Eˣ` is a function of the archimedean part
  -- times a function of the finite part.
  refine integral_ideleClass_tsum hρ
    (integrable_coneKernel A X y g β hv (one_pos.trans hx)) (h_tate_int.const_mul _)
    (poissonVariable E β u * K⁻¹) fun a h k ↦ ?_
  rw [zetaIntegrand_eq_tsum A X hn fun β ↦ lineValue_zero_of_factor A X h_factor β h k]
  refine tsum_congr fun ξ ↦ ?_
  have h_idele : principalAdeleUnit ξ * poissonVariable E β (a * u) =
      principalAdeleUnit ξ * poissonVariable E β a * (poissonVariable E β u * K⁻¹) * K := by
    simp [mul_assoc]
  simpa only [h_idele] using baseChange_mul_lineValue_eq_coneKernel_mul A X h_factor hc β x _ h k

/-- The formula of `integral_zetaIntegrand_of_one_lt` for Tate's integral of the split tame
character `𝔠 : SplitTameChar E μ` in terms of the cone kernel holds for all `x ≥ 1`, under the same
hypotheses, if Tate's integral is continuous in its exponent: both sides are then continuous up to
`1`. -/
theorem integral_zetaIntegrand_of_one_le [Fintype b] [DecidableEq b]
    (h_factor : LineValueFactors 𝔠 A X σ v y g f κ)
    (hc : ∀ a : 𝔸f E, lineFinFactor 𝔠 ϖ.val a = lineFinFactor 𝔠 1 (a * c))
    (hn : 2 ∣ card n) (hv : IsSchwartzVector v) (u : (𝔸 E)ˣ)
    {β : Bool} {ρ : Measure (𝔸f E)ˣ} [IsHaarMeasure ρ]
    (hρ : MeasurePreserving ((poissonVariable E β).trans (ideleParts E)) haar (haar.prod ρ))
    (h_cont : Continuous fun x : ℝ ↦
      ∫ p : ((𝔸 E)ˣ × G E t) × maxCompact E t',
        zetaIntegrand 𝔠.character A X f g u x p ∂zetaMeasure V t')
    {x : ℝ} (hx : 1 ≤ x) :
    let K : (𝔸 E)ˣ := shiftIdele c
    ∫ p : ((𝔸 E)ˣ × G E t) × maxCompact E t',
      zetaIntegrand 𝔠.character A X f g u (cond β x (1 - x)) p ∂zetaMeasure V t' =
      (∫ p : G E t × maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
        coneKernel 𝔠 A X σ v y g β x p ∂V.quotMeasure.prod (haar.prod haar)) *
        (κ β * 𝔠.character.baseChange.val K * (ideleAbs K ^ x : ℝ) *
          (𝔠.character.L 𝔠.ramifiedPlaces x * ρ.real (idelesUnitOff (K := E) ∅))) := by
  intro K
  -- Both sides, `tate` and `rhs`, are continuous on `[1, x + 1]` and agree on `(1, x + 1]`.
  let tate : ℝ → ℂ := fun x ↦
    ∫ p, zetaIntegrand 𝔠.character A X f g u (cond β x (1 - x)) p ∂zetaMeasure V t'
  let rhs (x : ℝ) : ℂ :=
    (∫ p, coneKernel 𝔠 A X σ v y g β x p ∂V.quotMeasure.prod (haar.prod haar)) *
      (κ β * 𝔠.character.baseChange.val K * (ideleAbs K ^ x : ℝ) *
        (𝔠.character.L 𝔠.ramifiedPlaces x * ρ.real (idelesUnitOff (K := E) ∅)))
  have h_pow : Continuous fun x : ℝ ↦ ((ideleAbs K ^ x : ℝ) : ℂ) :=
    continuous_ofReal.comp (continuous_const_rpow ideleAbs_pos.ne')
  have h_L : ContinuousOn (𝔠.character.L 𝔠.ramifiedPlaces) (Icc 1 (x + 1)) :=
    (continuousOn_L 𝔠).mono Icc_subset_Ici_self
  have h_right : ContinuousOn rhs (Icc 1 (x + 1)) :=
    (continuousOn_integral_coneKernel A X y g β hv (by linarith)).mul
      ((continuous_const.mul h_pow).continuousOn.mul (h_L.mul_const _))
  have h_left : Continuous tate :=
    h_cont.comp (by cases β <;> simp only [Bool.cond_false, Bool.cond_true] <;> fun_prop)
  have h_eq : EqOn tate rhs (Ioc 1 (x + 1)) := fun x' hx' ↦
    (integral_zetaIntegrand_of_one_lt A X h_factor hc hn hv u hρ hx'.1).2
  exact h_eq.of_subset_closure h_left.continuousOn h_right Ioc_subset_Icc_self
    (closure_Ioc (by linarith)).ge ⟨hx, by linarith⟩

end

/-! ### Analytic continuation and the constant term -/

/-- Let `A` and `X` split a hyperbolic plane off `W'` and `V'`, let `f` be a datum on `Hom(W', V')`,
`g` a point of `U(W)`, `u` an idele and `ν` a character of `[U(1)]`. Tate's integral `𝒵(x)` is the
integral of `zetaIntegrand ν A X f g u x` over the idele classes, `[U(V)]` and the maximal compact
subgroup of `U(V')` (the measure `zetaMeasure V t'`). If it converges absolutely at `x` and at
`1 - x` for every `x > 1`, then it converges absolutely at every real `x`, and `𝒵` is analytic on
the real line. -/
theorem analyticOnNhd_integral_zetaIntegrand (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)
    {ν : AutChar E} {f : 𝒮 (W'.hom V')} {g : G E s} {u : (𝔸 E)ˣ}
    (h_right : ∀ x : ℝ, 1 < x → Integrable (zetaIntegrand ν A X f g u x) (zetaMeasure V t'))
    (h_left : ∀ x : ℝ, 1 < x → Integrable (zetaIntegrand ν A X f g u (1 - x)) (zetaMeasure V t')) :
    (∀ x : ℝ, Integrable (zetaIntegrand ν A X f g u x) (zetaMeasure V t')) ∧
      AnalyticOnNhd ℝ (fun x : ℝ ↦ ∫ p : ((𝔸 E)ˣ × G E t) × maxCompact E t',
        zetaIntegrand ν A X f g u x p ∂zetaMeasure V t') univ := by
  -- In `x` the integral is a Mellin transform: the integrand at `p = ((a, h), k)` is its value
  -- `T p` at `x = 0` times `N p ^ x`, where `N p = |a u|`.
  let T : ((𝔸 E)ˣ × G E t) × maxCompact E t' → ℂ := zetaIntegrand ν A X f g u 0
  let N (p : ((𝔸 E)ˣ × G E t) × maxCompact E t') : ℝ := ideleAbs (p.1.1 * u)
  have h_mellin (x : ℝ) : zetaIntegrand ν A X f g u x = fun p ↦ T p * (N p ^ x : ℝ) := by
    funext p
    simp [T, N, zetaIntegrand]
  simp only [h_mellin] at h_right h_left ⊢
  -- A Mellin transform that converges at both ends `1 - R` and `R` of a strip converges and is
  -- analytic inside it, and `x` lies inside the strip for `R = |x| + 2`.
  have h_strip (x : ℝ) : Integrable (fun p ↦ T p * (N p ^ x : ℝ)) (zetaMeasure V t') ∧
      AnalyticAt ℝ (fun z : ℝ ↦ ∫ p, T p * (N p ^ z : ℝ) ∂zetaMeasure V t') x := by
    obtain ⟨hR, h_mem⟩ : 1 < |x| + 2 ∧ x ∈ Ioo (1 - (|x| + 2)) (|x| + 2) := by grind
    obtain ⟨h_integrable, -, h_analytic⟩ := analyticOnNhd_integral_mul_rpow (fun _ ↦ ideleAbs_pos)
      (by fun_prop : Measurable N) (h_left _ hR).hasFiniteIntegral (h_right _ hR)
    exact ⟨h_integrable x (Ioo_subset_Icc_self h_mem), h_analytic x h_mem⟩
  exact ⟨fun x ↦ (h_strip x).1, fun x _ ↦ (h_strip x).2⟩

/-- Unfolding. Let the adapted splittings `A` and `X` split a hyperbolic plane off `W'` and `V'`,
let `rk W = card n` be even and `e = rk V - rk W / 2`. There is a constant `c ≠ 0`, independent of
the character, with the following property. Let `𝔠` be a split tame character, `v` a real vector
with finite Fock moments, `y` a matrix at the places `𝔠.ramifiedPlaces` and `(u, g)` a Levi point
with `u = 1` or `rk V = rk W`. If Tate's integral `𝒵(e + 1)` of `planeDatum 𝔠 A σ' v y`, the
integral of `Θ`, converges absolutely, then the constant term along `A` at `(u, g)` of the theta
integral of `(W', V')` on this datum is `c 𝒵(e + 1)`. -/
theorem exists_planeConstantTerm_eq_integral (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)
    [IsBaseAdapted A] [IsBaseAdapted X] (σ' : b ⊕ r' ≃ n') (hn : 2 ∣ card n) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ)
      {v : PairFock E s' t'}, IsSchwartzVector v → ∀ (y : Matrix b n (LocProd 𝔠.ramifiedPlaces))
        (g : G E s)
      {u : (𝔸 E)ˣ}, u = 1 ∨ card r = card n →
      let Θ : ((𝔸 E)ˣ × G E t) × maxCompact E t' → ℂ :=
        zetaIntegrand 𝔠.character A X (planeDatum 𝔠 A σ' v y) g u ((card r - card n / 2 : ℤ) + 1)
      Integrable Θ (zetaMeasure V t') →
        planeConstantTerm 𝔠 V' A σ' v y u g =
          c * ∫ p : ((𝔸 E)ˣ × G E t) × maxCompact E t', Θ p ∂zetaMeasure V t' := by
  classical
  obtain ⟨c, hc, h_unfold⟩ := exists_unfold_constant_term A X
  refine ⟨c, hc, ?_⟩
  intro μ 𝔠 v hv y g u hu Θ h_int
  let F (h : G E t') : 𝒮 (W'.hom V') := pairWeil W' V' (rankTwist 𝔠.character⁻¹ n')
    (rankTwist 𝔠.character⁻¹ n')
    (A.levi (.scalar Unit u, g), h) (planeDatum 𝔠 A σ' v y)
  let Θ₀ (p : ((𝔸 E)ˣ × G E t) × maxCompact E t') : ℂ := (ideleAbs p.1.1 ^ (card r + 1) : ℝ) *
    ∑' ξ : Eˣ, θ (W.hom V) (lineTerm A X true (toAdele ξ.val) (F (lineLevi X p.1 * p.2)))
  -- The Levi points turn the unfolded integrand into that of Tate's integral.
  have h_integrand : Θ₀ = Θ := by
    funext ⟨⟨a, h⟩, k⟩
    simp only [Θ₀, Θ, zetaIntegrand, ← tsum_mul_left, ← tsum_mul_right]
    exact tsum_congr fun ξ ↦
      theta_lineTerm_levi A X hn hu (planeDatum 𝔠 A σ' v y) g true (toAdele ξ.val) a h k
  -- The term `x = 0` of the constant term vanishes.
  have h_zero (h : G E t') : constTermAt A 0 (F h) = 0 := by
    simp only [constTermAt_zero, F, rankTwist_eq_mul_of_splitting A, A.homSlice_levi,
      Matrix.mul_zero, Matrix.zero_mul, homSlice_zero_planeDatum A σ' v y, map_zero, smul_zero]
  rw [← h_integrand] at h_int ⊢
  calc planeConstantTerm 𝔠 V' A σ' v y u g
      = ∫ h, ∑' x : r' → E, constTermAt A (Matrix.replicateCol Unit x) (F h) ∂V'.quotMeasure :=
        integral_thetaIntegral_lineRadical A _ _
          (𝔠.readsAt.isTargetBounded hv (stdRowDatum_mem σ' 𝔠.semilocalChar)) _
    _ = c * ∫ p, Θ₀ p ∂zetaMeasure V t' :=
        h_unfold (rankTwist 𝔠.character⁻¹ n') (rankTwist 𝔠.character⁻¹ n') (planeDatum 𝔠 A σ' v y)
          (A.levi (.scalar Unit u, g)) h_zero h_int

variable [Fintype b] [DecidableEq b]

/-- Let `E` be a CM field, let `W`, `V`, `W'`, `V'` be hermitian spaces with frames indexed by `n`,
`r`, `n'`, `r'` and signs `s`, `t`, `s'`, `t'`, let `A` and `X` split a plane off `W'` and `V'`, and
let `σ : b ⊕ r ≃ n` and `σ' : b ⊕ r' ≃ n'` list the rows of the standard data. For a split tame
character `𝔠 : SplitTameChar E μ` write `ν = 𝔠.character` and `S = 𝔠.ramifiedPlaces`. Let
`rk W = card n` be even and `e = rk V - rk W / 2`. For a Schwartz vector `v` (all Fock moments are
finite), an integral `b × n` matrix `y` over the completions at `S`, and a Levi point `(u, g)` with
`u = 1` or `rk V = rk W`, there is a function `𝒵`, analytic on the real line (in the proof a
multiple of Tate's integral), such that the constant term along `A` at `(u, g)` of the theta
integral of `(W', V')` on the plane datum of `v`, `y` is `𝒵(e + 1)`. Moreover, for `x ≥ 1`,
`𝒵(x) = ε |α₀| ^ x ∏_{w ∈ S} q_w ^ (x - 1/2) L^S(x, ν) I`, where `I` is the theta integral of
`(W, V)` at `g` of the datum with real part the cone integral of `v` (the integral of
`coneIntegrand` with exponent `x`) and with `stdRowDatum σ 𝔠.semilocalChar y` at `S`. The value
`𝒵(1 - x)` has the same form, with the cone integral on the other side of Poisson's formula
(`β = false`). Here `O` is the ring of integers of the product of the completions at `S`,
`α₀ = scaleIdele E`, and the modulus `C β` of the constant `ε β` of the side `β` does not depend on
the character. -/
theorem exists_zetaIntegral (σ' : b ⊕ r' ≃ n') (σ : b ⊕ r ≃ n) (hn : 2 ∣ card n)
    (μ : InfinitePlace E → ℤ) :
    ∃ C : Bool → ℝ, (∀ β : Bool, 0 < C β) ∧ ∀ 𝔠 : SplitTameChar E μ, ∃ ε : Bool → ℂ,
      (∀ β : Bool, ‖ε β‖ = C β) ∧
      ∀ v : PairFock E s' t', IsSchwartzVector v → ∀ y : Matrix b n (LocProd 𝔠.ramifiedPlaces),
        IsIntMatrix O y →
        ∀ (u : (𝔸 E)ˣ) (g : G E s), u = 1 ∨ card r = card n →
          ∃ 𝒵 : ℝ → ℂ, AnalyticOnNhd ℝ 𝒵 univ ∧
            planeConstantTerm 𝔠 V' A σ' v y u g = 𝒵 ((card r - card n / 2 : ℤ) + 1) ∧
            ∀ (β : Bool) (x : ℝ), 1 ≤ x → 𝒵 (cond β x (1 - x)) =
              ε β * (ideleAbs (scaleIdele E) ^ x * ∏ w : 𝔠.ramifiedPlaces,
                (w.val.q : ℝ) ^ (x - 1 / 2) : ℝ) *
                𝔠.character.L 𝔠.ramifiedPlaces x *
                thetaLarge W V 𝔠 (∫ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
                  coneIntegrand A X μ β x v p ∂haar.prod haar)
                  (stdRowDatum σ 𝔠.semilocalChar y) g := by
  -- Unfold the constant term to `𝒵(e + 1)`. The datum factors along the line, so for `x > 1` the
  -- sum over `Eˣ` unfolds to a product; by continuity the value is the same at `x = 1`.
  obtain ⟨cUnfold, h_cUnfold, h_unfold⟩ := exists_planeConstantTerm_eq_integral A X σ' hn
  obtain ⟨lineConst, h_lineConst⟩ := exists_lineValue_eq A X σ' σ μ
  choose ρ hρ_haar hρ using exists_haar_ideleParts E
  let vol (β : Bool) : ℝ := (ρ β).real (idelesUnitOff (K := E) ∅)
  have h_vol (β : Bool) : 0 < vol β := measureReal_idelesUnitOff_empty_pos (ρ β)
  refine ⟨fun β ↦ |cUnfold| * ‖(lineConst β).val‖ * vol β, fun β ↦ ?_, fun 𝔠 ↦ ?_⟩
  · exact mul_pos (mul_pos (abs_pos.2 h_cUnfold) (norm_pos_iff.2 (lineConst β).ne_zero)) (h_vol β)
  obtain ⟨γ, hγ, hγ_factor⟩ : ∃ γ : ℂ, ‖γ‖ ^ 2 = (∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ))⁻¹ ∧
      ∀ (v : PairFock E s' t') (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)), IsIntMatrix O y → ∀ g :
        G E s,
        LineValueFactors 𝔠 A X σ v y g (planeDatum 𝔠 A σ' v y) fun β ↦ lineConst β * γ :=
    h_lineConst 𝔠
  obtain ⟨c, hc_abs, hc⟩ : ∃ c : (𝔸f E)ˣ, finIdeleAbs c⁻¹ = ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ) ∧
      ∀ a : 𝔸f E, lineFinFactor 𝔠 ϖ.val a = lineFinFactor 𝔠 1 (a * c) :=
    exists_lineFinFactor_uniformizer_eq 𝔠
  let K : (𝔸 E)ˣ := shiftIdele c
  let Q : ℝ := ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ)
  have hQ : 0 < Q := Finset.prod_pos fun w _ ↦ by simp [FinPlace.q_bounds]
  -- The Gauss sum `γ` has modulus `Q ^ (-1/2)`, and `|K| = Q |α₀|`.
  refine ⟨fun β ↦ cUnfold * lineConst β * vol β * (γ * √Q) * 𝔠.character.baseChange.val K, fun β ↦
    ?_,
    fun v hv y hy u g hu ↦ ?_⟩
  · have h_norm : ‖γ‖ * √Q = 1 := by
      rw [← sqrt_sq (norm_nonneg γ), hγ, ← sqrt_mul (by positivity), inv_mul_cancel₀ hQ.ne',
        Real.sqrt_one]
    simp [abs_of_pos (h_vol β), abs_of_nonneg (sqrt_nonneg Q), h_norm, Circle.norm_coe]
  have h_factor : LineValueFactors 𝔠 A X σ v y g (planeDatum 𝔠 A σ' v y)
      fun β ↦ lineConst β * γ := hγ_factor v y hy g
  let f : 𝒮 (W'.hom V') := planeDatum 𝔠 A σ' v y
  have h_conv (β : Bool) (x : ℝ) (hx : 1 < x) :
      Integrable (zetaIntegrand 𝔠.character A X f g u (cond β x (1 - x))) (zetaMeasure V t') :=
    (integral_zetaIntegrand_of_one_lt A X h_factor hc hn hv u (hρ β) hx).1
  obtain ⟨h_int, h_analytic⟩ :=
    analyticOnNhd_integral_zetaIntegrand A X (h_conv true) (h_conv false)
  refine ⟨fun x ↦ cUnfold * ∫ p, zetaIntegrand 𝔠.character A X f g u x p ∂zetaMeasure V t',
    analyticOnNhd_const.mul h_analytic, h_unfold 𝔠 hv y g hu (h_int _), fun β x hx ↦ ?_⟩
  have h_value : ∫ p, zetaIntegrand 𝔠.character A X f g u (cond β x (1 - x)) p ∂zetaMeasure V t' =
      (∫ p, coneKernel 𝔠 A X σ v y g β x p ∂V.quotMeasure.prod (haar.prod haar)) *
        (lineConst β * γ * 𝔠.character.baseChange.val K * (ideleAbs K ^ x : ℝ) *
          (𝔠.character.L 𝔠.ramifiedPlaces x * vol β)) :=
    integral_zetaIntegrand_of_one_le A X h_factor hc hn hv u (hρ β)
      (continuousOn_univ.1 h_analytic.continuousOn) hx
  have h_abs : ideleAbs K ^ x =
      √Q * (ideleAbs (scaleIdele E) ^ x * ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ) ^ (x - 1 / 2)) := by
    have hK : ideleAbs K = Q * ideleAbs (scaleIdele E) := by
      rw [map_mul, show ideleAbs (finIdeleIncl c⁻¹) = Q from hc_abs]
    rw [hK, mul_rpow hQ.le ideleAbs_pos.le, finsetProd_rpow _ _ fun w _ ↦ by simp, sqrt_eq_rpow,
      rpow_sub hQ]
    field
  beta_reduce
  rw [h_value, integral_coneKernel A X y g β hv (one_pos.trans_le hx), h_abs]
  push_cast
  ring

/-- Let `rk W = card n` be even, `e = rk V - rk W / 2`, and let `e + 1` be `z + 1` (for `β = true`)
or `1 - (z + 1)` (for `β = false`). There are `C > 0`, independent of `𝔠`, and `γ` with
`|γ| = C L♯(z + 1)`, where `L♯(z) = |L^S(z, ν)| ∏_{w ∈ S} q_w ^ (z - 1/2)` (`lSharp`) for
`ν = 𝔠.character` and `S = 𝔠.ramifiedPlaces`. Then for a Schwartz vector `v'`, integral `y`, and
`u = 1` or `rk V = rk W`, the constant term along `A` at `(u, g)` of the theta integral of
`(W', V')` on `planeDatum` is `γ` times the theta integral of `(W, V)` on the datum with
`stdRowDatum σ 𝔠.semilocalChar y` at `S` and real part the cone integral of side `β` of `v'`, which
integrates `coneIntegrand` with exponent `z + 1` over `k` in the maximal compact subgroup of `U(V')`
and the archimedean ideles. -/
theorem exists_planeConstantTerm_eq_thetaLarge (σ' : b ⊕ r' ≃ n') (σ : b ⊕ r ≃ n) (hn : 2 ∣ card n)
    (μ : InfinitePlace E → ℤ) (β : Bool) {z : ℕ}
    (hz : ((card r - card n / 2 : ℤ) + 1 : ℝ) = cond β (z + 1 : ℝ) (1 - (z + 1))) :
    ∃ C > (0 : ℝ), ∀ 𝔠 : SplitTameChar E μ, ∃ γ : ℂ,
      ‖γ‖ = C * lSharp 𝔠 (z + 1) ∧
      ∀ v' : PairFock E s' t', IsSchwartzVector v' → ∀ y : Matrix b n (LocProd 𝔠.ramifiedPlaces),
        IsIntMatrix O y →
        ∀ (u : (𝔸 E)ˣ) (g : G E s), u = 1 ∨ card r = card n →
          planeConstantTerm 𝔠 V' A σ' v' y u g =
          γ * thetaLarge W V 𝔠 (∫ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
            coneIntegrand A X μ β (z + 1) v' p ∂haar.prod haar)
            (stdRowDatum σ 𝔠.semilocalChar y) g := by
  -- Take `x = z + 1` in the formula for Tate's integral.
  obtain ⟨modulus, h_modulus, h_zeta⟩ := exists_zetaIntegral A X σ' σ hn μ
  have h_scale : 0 < ideleAbs (scaleIdele E) ^ (z + 1 : ℝ) := rpow_pos_of_pos ideleAbs_pos _
  refine ⟨modulus β * ideleAbs (scaleIdele E) ^ (z + 1 : ℝ), mul_pos (h_modulus β) h_scale,
    fun 𝔠 ↦ ?_⟩
  obtain ⟨coeff, h_coeff, h_coeff_zeta⟩ := h_zeta 𝔠
  let Q : ℝ := ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ) ^ ((z : ℝ) + 1 - 1 / 2)
  refine ⟨coeff β * (ideleAbs (scaleIdele E) ^ (z + 1 : ℝ) * Q : ℝ) * 𝔠.character.L 𝔠.ramifiedPlaces
    (z + 1), ?_,
    fun v hv y hy u g hu ↦ ?_⟩
  · rw [norm_mul, norm_mul, h_coeff, norm_real, norm_of_nonneg (by positivity), lSharp]
    ring
  · obtain ⟨𝒵, -, h_term, h_zeta_eq⟩ := h_coeff_zeta v hv y hy u g hu
    rw [h_term, hz, h_zeta_eq β (z + 1) (by simp)]

/-- One plane: let `z = rk V - rk W / 2 ≥ 0`, with `rk W = card n` even. For a Schwartz vector `v'`
and integral `y`, the constant term along `A` of the theta integral of `(W', V')` is `γ` times the
theta integral of `(W, V)` on `cone A X μ (z + 1) v'` and `stdRowDatum σ 𝔠.semilocalChar y`. The
cone is the real Tate integral of `v'` with exponent `z + 1` over the vectors `k⁻¹ x a`, with `x`
spanning the isotropic line `X.k`. Here `|γ| = C L♯(z + 1)` with
`L♯(z) = |L^S(z, ν)| ∏_{w ∈ S} q_w ^ (z - 1/2)` (`lSharp`) for `ν = 𝔠.character` and
`S = 𝔠.ramifiedPlaces`, and `C > 0` does not depend on the character. This holds at the points
`(1, g)` of the Levi subgroup, and at all its points `(u, g)` if `rk V = rk W`. -/
theorem exists_planeConstantTerm_eq_thetaLarge_cone (σ' : b ⊕ r' ≃ n') (σ : b ⊕ r ≃ n)
    (hn : 2 ∣ card n) (μ : InfinitePlace E → ℤ) {z : ℕ} (hz : (card r - card n / 2 : ℤ) = z) :
    ∃ C > (0 : ℝ), ∀ 𝔠 : SplitTameChar E μ, ∃ γ : ℂ,
      ‖γ‖ = C * lSharp 𝔠 (z + 1) ∧
      ∀ v' : PairFock E s' t', IsSchwartzVector v' → ∀ y : Matrix b n (LocProd 𝔠.ramifiedPlaces),
        IsIntMatrix O y →
        ∀ (u : (𝔸 E)ˣ) (g : G E s), u = 1 ∨ card r = card n →
          planeConstantTerm 𝔠 V' A σ' v' y u g =
          γ * thetaLarge W V 𝔠 (cone A X μ (z + 1) v') (stdRowDatum σ 𝔠.semilocalChar y) g := by
  simpa only [cone] using
    exists_planeConstantTerm_eq_thetaLarge A X σ' σ hn μ true (z := z) (by simp [hz])

/-- One plane for `rk V - rk W / 2 = -z - 1 < 0`, with `rk W = card n` even: for a Schwartz vector
`v'` and integral `y`, at `u = 1` (the case `rk V = rk W` cannot occur here), the constant term
along `A` of the theta integral of `(W', V')` is `γ` times the theta integral of `(W, V)` on
`dualCone A X μ (z + 1) v'` and `stdRowDatum σ 𝔠.semilocalChar y`. The cone integral is a real Tate
integral over the isotropic cone of `V'`, and `dualCone` is this integral on the other side of
Poisson's formula. Here `|γ| = C L♯(z + 1)` with `L♯(z) = |L^S(z, ν)| ∏_{w ∈ S} q_w ^ (z - 1/2)`
(`lSharp`) for `ν = 𝔠.character` and `S = 𝔠.ramifiedPlaces`, and `C > 0` does not depend on `𝔠`. As
Poisson's formula is applied before the integral is evaluated, only values of `L` at points `≥ 1`
occur, and the functional equation of `L` is not needed. -/
theorem exists_planeConstantTerm_eq_thetaLarge_dualCone (σ' : b ⊕ r' ≃ n') (σ : b ⊕ r ≃ n)
    (hn : 2 ∣ card n)
    (μ : InfinitePlace E → ℤ) {z : ℕ} (hz : (card r - card n / 2 : ℤ) = -(z + 1)) :
    ∃ C > (0 : ℝ), ∀ 𝔠 : SplitTameChar E μ, ∃ γ : ℂ,
      ‖γ‖ = C * lSharp 𝔠 (z + 1) ∧
      ∀ v' : PairFock E s' t', IsSchwartzVector v' → ∀ y : Matrix b n (LocProd 𝔠.ramifiedPlaces),
        IsIntMatrix O y →
        ∀ (u : (𝔸 E)ˣ) (g : G E s), u = 1 ∨ card r = card n →
          planeConstantTerm 𝔠 V' A σ' v' y u g =
          γ * thetaLarge W V 𝔠 (dualCone A X μ (z + 1) v') (stdRowDatum σ 𝔠.semilocalChar y) g := by
  simpa only [dualCone] using
    exists_planeConstantTerm_eq_thetaLarge A X σ' σ hn μ false (z := z) (by simp [hz])

end

end New.Exchange

end
