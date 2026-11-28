import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability

/-!
# The idempotent e_λ, the operator π(e_λ), and rigidity of highest vectors of type Λ

The file studies the function `e_λ = New.HCParam.dsKernel l = deg_λ · conj c_λ` on `U(diag ε)`,
where `l = 2λ`, and the operator `π(f) = New.integratedRep π f = ∫ f(g) π(g) dg`. In the main
results `λ` has gap `500 n³ + A` (`New.HCParam.HasLargeGap`), `π` has growth `‖g‖ ^ A` and an
invariant positive definite sesquilinear form `B` on `X` (`New.IsUnitaryRep`), and the `gl n`-module
`ρ` on a complex space `M` is its derivative along a linear map `ι : M → X` (`New.IsDerivedAction`).

* `New.coeff_eq_dsCoeff_of_isKHighest` (rigidity): a `K`-highest vector `x` of weight
  `Λ = New.HCParam.lowestKType l` with Casimir value at least
  `κ_λ = New.HCParam.casimirValue l = |λ|² − |ρ|²` (ρ here the half-sum of positive roots) has the
  matrix coefficient `B x (π g x) = B x x c_λ(g)`.
* `New.integratedRep_fix_of_isKHighest`: if `‖g‖ ^ A f` is integrable and `f * e_λ = e_λ`, then
  `π(f)` fixes such a vector.
* `New.exists_integration_by_parts`, `New.integratedRep_dsKernel_casimir`: integration by parts, and
  `π(e_λ) Ω = κ_λ π(e_λ)`.
* `New.re_integratedRep_dsKernel_pos`, `New.integratedRep_eq_zero_of_notMem_rootCone`: a condition
  under which `π(e_λ)` does not kill a vector, and one under which it does.
* `New.HCParam.HasLargeGap.isIdempotentKernel_dsKernel`,
  `New.HCParam.HasLargeGap.exists_bump_conv_dsKernel`: `e_λ` is a minimal idempotent, reproduced by
  a bump function.

`ρ.casimirK 1` is the Casimir operator `Ω = ∑ E_ab E_ba` of all of `gl n` (all signs equal).

Notions from other files:
* `New.HCParam.IsKHighest`: `x` is a `K`-highest vector of weight `ν`: each `E a a` acts on it by
  `ν a`, and it is killed by the compact raising operators, the `E a b` with `ε a = ε b` and
  `l b < l a`.
* `New.HCParam.lowestKType`: the integer vector Λ = λ+ρ−2ρ_c for a parameter l = 2λ, the highest
  weight of the lowest K-type.
* `New.HCParam.dsCoeff`, `New.HCParam.DsModule`: The function c_λ, and the module U(𝔤)c_λ it
  generates under right derivatives (action `New.HCParam.dsAction`, generator
  `New.HCParam.dsGenerator`).
* `New.weightMinors`, `New.HCParam.kTypeNormSq`: The coefficient m_ν of a highest vector of weight ν
  (a product of principal minors), and ∫_K |m_ν|².
* `New.HCParam.rootCone`: The cone of the positive roots for the order given by l.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration`,
`Lib.DiscreteSeries.Theta.LocalCorrespondence` and `Lib.DiscreteSeries.FlenstedJensen.PsiKTypes` for
sources.
-/

namespace New

open Matrix MeasureTheory ComplexConjugate Complex DiscreteSeries Norms.L2Operator ComplexOrder
  GlModule Submodule WithLp HCParam

-- `n` indexes the signs `ε`, `π` is a representation of `U(diag ε)` on `X`, and `f` is a function
-- on `U(diag ε)`
variable {n : Type} [Fintype n] [DecidableEq n]
  {ε : n → ℤˣ} {A : ℕ} {X : Type*} {l : HCParam (n := n) ε} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (π : USign ε →* X →L[ℂ] X) (f : USign ε → ℂ)

@[fun_prop]
theorem continuous_dsKernel : Continuous l.dsKernel := by fun_prop [dsKernel]

/-- For `l = 2λ` a parameter of some gap `h` (`New.HCParam.HasGap`),
`conj ((-l).dsKernel x) = l.dsKernel x` for every `x` in `U(diag ε)`. That is, `conj(e_{−λ}) = e_λ`
for the kernel `e_λ = deg_λ · conj(c_λ)` given by `dsKernel`. -/
lemma conj_dsKernel_neg {h : ℕ} (hg : l.HasGap h) (x : USign ε) :
    conj ((-l).dsKernel x) = l.dsKernel x := by
  simp [formalDegree, dsKernel, RingHom.map_mul]

/-! ### The operator `π(f)` -/

/-- For a representation π of U(diag ε) by bounded operators and a function f, the operator π(f)
with π(f)x = ∫ f(g)π(g)x dg, when such a bounded operator exists. -/
noncomputable def integratedRep : X →L[ℂ] X := strongIntegral volume fun g ↦ f g • π g

variable {π f} [Nonempty n]
  {M Y W : Type*} [AddCommGroup M] [Module ℂ M]
  {B : X →L⋆[ℂ] X →L[ℂ] ℂ} {ι : M →ₗ[ℂ] X} {v : M} {c : ℝ} {ρ : GlModule n M}
  (hu : IsUnitaryRep A π B) [MeasurableSpace W]
  {ν : Measure W} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
  (hf : Integrable fun g : USign ε ↦ f g * ‖g.val.val‖ ^ A)

attribute [local fun_prop] IsUnitaryRep.continuous

/-- If `f` is integrable for a nonzero measure and its real part is positive everywhere, then the
real part of its integral is positive. -/
theorem re_integral_pos [NeZero ν] {f : W → ℂ} (hf_int : Integrable f ν)
    (hf_pos : ∀ w : W, 0 < re (f w)) :
    0 < (integral ν f).re := by
  refine .trans_eq ?_ (integral_re hf_int)
  refine (integral_pos_iff_support_of_nonneg (fun w ↦ (hf_pos w).le) hf_int.re).2 ?_
  simpa [Function.support_eq_univ fun w : W ↦ (hf_pos w).ne'] using NeZero.ne ν

omit [Nonempty n] in
/-- Let l be a parameter of any gap, π a representation as in `New.IsUnitaryRep` with derivative ρ
along ι, and v in M a K-highest vector of weight ν, with ν K-dominant for the order −l (ν b ≤ ν a
whenever ε a = ε b and l b < l a). Then for every continuous linear functional φ on X, ∫_K
conj(m_ν(k)) φ(π(k)ιv) dk = (∫_K |m_ν|²) φ(ιv), with m_ν = `weightMinors ν` and ∫_K
|m_ν|² = `ν.kTypeNormSq`. -/
theorem HCParam.IsKHighest.integral_conj_weightMinors_mul (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) {h : ℕ} {ν : HCParam ε}
    (hv_highest : l.IsKHighest ρ ν v) [h_gap : l.HasGap h] (hν : IsKDominant ε (-l) ν)
    (φ : X →L[ℂ] ℂ) :
    ∫ k : maxCompactU ε, conj (weightMinors ν k) * φ (π k (ι v)) ∂haarK ε =
      ν.kTypeNormSq * φ (ι v) := by
  -- The coefficient `k ↦ φ (π k (ι v))` is holomorphic of weight `ν` on `K`, so its integral
  -- against `conj (weightMinors ν k)` is `ν.kTypeNormSq` times its value at `1`. The lemmas are
  -- stated for a family of places; here the family is `Unit`.
  have h_cont (y : M) : Continuous fun g : USign ε ↦ φ (π g (ι y)) := by fun_prop
  have h_hol : IsHolOfWeight ε (-l) (fun _ : Unit ↦ ν)
      (fun k : Unit → USign ε ↦ φ (π (k ()) (ι v))) ε := by
    simpa using isHolOfWeight_coeffMap h_gap.neg.1 (fun _ : Unit ↦ by simpa using hv_highest)
      (fun _ ↦ hd.isCoeffMap φ) (.mkPiAlgebra ℂ Unit ℂ) fun _ ↦ h_cont
  simpa [mul_comm] using
    h_hol.integral_mul_conj_weightMinors h_gap.neg.1 hν ((h_cont v).comp (continuous_apply ()))

/-- If `π` is a representation as in `New.IsUnitaryRep` of growth exponent `A` and
`g ↦ f g * ‖g‖ ^ A` is integrable on `U(diag ε)`, then so is each `g ↦ f g • π g x`. -/
theorem integrable_smul_rep (hu : IsUnitaryRep A π B)
    (hf : Integrable fun g : USign ε ↦ f g * ‖g.val.val‖ ^ A) (x : X) :
    Integrable fun g : USign ε ↦ f g • π g x := by
  -- the integrable function `f g * ‖g‖ ^ A` times the bounded function `‖g‖ ^ (-A) • π g x`
  obtain ⟨c, hc⟩ := hu.growth
  have bound (g : USign ε) : ‖(‖g.val.val‖ ^ A : ℂ)⁻¹ • π g x‖ ≤ c * ‖x‖ := by
    grw [norm_smul, (π g).le_opNorm, hc]
    simp [field]
  simpa [Pi.smul_def', smul_smul] using hf.smul_bdd _ (by fun_prop) (.of_forall bound)

variable [CompleteSpace X]

include hu hf in
/-- If `g ↦ f g * ‖g‖ ^ A` is integrable and `π` is as in `New.IsUnitaryRep` with exponent `A`, then
a continuous linear map `T` takes `π(f) x` to the integral of `g ↦ f g • T (π g x)`. -/
theorem map_integratedRep (T : X →L[ℂ] Y) (x : X) :
    T (integratedRep π f x) = ∫ g : USign ε, f g • T (π g x) := by
  simp [integratedRep, ← T.integral_comp_comm, integrable_smul_rep hu hf, strongIntegral_apply]

/-! ### The kernel `e_λ`, its bump function, and the operator `π(e_λ)` -/

/-- For n ≥ 1 (`Nonempty n`) and a doubled parameter l = 2λ for the signs ε with gap 500n³+A
(`HasLargeGap`), the function `l.dsKernel` on U(diag ε), e_λ(g) = deg_λ·conj(c_λ(g)), is an
idempotent kernel in the sense of `New.IsIdempotentKernel`. That is, it is continuous and
integrable, e(g⁻¹) = conj e(g), e(1) ≠ 0, and ∫ e(z) e(x⁻¹z⁻¹y) dz = e(x⁻¹) e(y)/e(1). -/
theorem HCParam.HasLargeGap.isIdempotentKernel_dsKernel (hg : l.HasLargeGap A) :
    IsIdempotentKernel l.dsKernel where
  continuous := by fun_prop
  integrable := by simpa using hg.integrable_dsKernel_mul_norm_pow 0 (Nat.zero_le _)
  apply_inv g := by simp [↓dsCoeff_inv, dsKernel, RingHom.map_mul]
  apply_one_ne_zero := by simp [dsKernel, ne_of_gt]
  convolution_eq x y := by
    -- the integrand is that of Schur orthogonality for `dsCoeff`, times `l.formalDegree ^ 2`
    have h_schur : l.formalDegree * ∫ z : USign ε, l.dsCoeff ↑(y⁻¹ * z * x) * conj (l.dsCoeff z) =
        l.dsCoeff ↑y⁻¹ * l.dsCoeff x :=
      dsCoeff_schur_orthogonality hg y⁻¹ x
    have h_integrand (z : USign ε) : l.dsKernel z * l.dsKernel ((z * x)⁻¹ * y) = l.formalDegree *
        (l.formalDegree * (l.dsCoeff ↑(y⁻¹ * z * x) * conj (l.dsCoeff z))) := by
      simp [dsKernel, ↓← dsCoeff_inv, mul_comm, mul_left_comm, mul_assoc]
    have h_value : l.dsKernel x⁻¹ / l.dsKernel 1 * l.dsKernel y =
        l.formalDegree * (l.dsCoeff ↑y⁻¹ * l.dsCoeff x) := by
      simp [dsKernel, ↓dsCoeff_inv, ne_of_gt]
      ring
    simp only [h_integrand, integral_const_mul, h_schur, h_value]

/-- For `n ≥ 1` and `λ = l / 2` with gap `500 n³ + A`, let `e_λ = l.dsKernel`. Then there is a
smooth compactly supported `α` on `U(diag ε)` with `∫ α(x⁻¹) e_λ(x⁻¹ g) dx = e_λ(g)` for all `g`. So
`β * e_λ = e_λ` for the function `β(x) = α(x⁻¹)`; the inverse comes from the convention of
`New.DiscreteSeries.smear`. -/
theorem HCParam.HasLargeGap.exists_bump_conv_dsKernel (hg : l.HasLargeGap A) :
    ∃ α : Bumps ε, ∀ g : USign ε,
      ∫ x : USign ε, α.val.val x⁻¹ * l.dsKernel (x⁻¹ * g) = l.dsKernel g := by
  -- `smear l.dsCoeffSmooth.1 α` is `g ↦ ∫ y, α y⁻¹ • l.dsCoeff (g * y)`
  obtain ⟨α, hα⟩ : ∃ α : Bumps ε, (smear l.dsCoeffSmooth.val) α = l.dsGenerator.val :=
    exists_smear_dsCoeffSmooth_eq hg l.dsGenerator
  refine ⟨α, fun g ↦ ?_⟩
  -- evaluate at `g⁻¹`; `dsCoeff` at an inverse is the conjugate (`dsCoeff_inv`)
  have h_eval : ∫ y : USign ε, α.val.val y⁻¹ * l.dsCoeff ↑(g⁻¹ * y) = l.dsCoeff ↑g⁻¹ := by
    simpa using congrFun hα g⁻¹
  simpa [↓← dsCoeff_inv, mul_left_comm, dsKernel, integral_const_mul, ne_of_gt] using h_eval

/-- Integration by parts. Let `λ = l / 2` have gap `500 n³ + A`, and let `π` be as in
`New.IsUnitaryRep` with derivative `ρ` along `ι`. Let `(-l).DsModule` be the space U(𝔤)c_{−λ}
generated by c_{−λ} under right derivatives, with gl_n-action `dsAction`. Then there is a linear map
`P` from this space to bounded operators on `X` such that (a) `P(c_{−λ})` is `π(e_λ)`, the
integrated operator `x ↦ ∫ e_λ(g) π(g) x dg` of `e_λ = l.dsKernel` = deg_λ · conj(c_λ); (b)
`P f (ι (ρ Y v)) = −P (Y·f) (ι v)` for all `Y` in gl_n(ℂ), `f` and `v`. -/
theorem exists_integration_by_parts (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) :
    ∃ P : (-l).DsModule →ₗ[ℂ] X →L[ℂ] X,
      -- (a) the operator of the kernel is the value of `P` at the generator
      integratedRep π l.dsKernel = P (-l).dsGenerator ∧
      -- (b) integration by parts
      ∀ (Y : Matrix n n ℂ) (f : (-l).DsModule) (v : M),
        P f (ι (ρ Y v)) = -P ((-l).dsAction Y f) (ι v) := by
  -- Take `l.formalDegree` times `P f = integratedRep π f`. For `Y` in the real Lie algebra put
  -- `F g = f g • π g (ι v)` and let `F'` be its derivative along `Y`. Then `∫ F' = 0`, because
  -- `∫ t in 0..1, F' (g * expU (t • Y)) = F (g * expU Y) - F g` and the measure is right invariant.
  have h_int (f : (-l).DsModule) (x : X) : Integrable fun g : USign ε ↦ f.val.val g • π g x :=
    integrable_smul_rep hu (HasLargeGap.integrable_mul_norm_pow hg.neg f A A.le_succ) x
  -- `P f = π(f)`, linear in `f` since all these integrands are integrable
  let P : (-l).DsModule →ₗ[ℂ] X →L[ℂ] X :=
    { toFun f := integratedRep π f.val.val
      map_add' := by
        simp [DFunLike.ext_iff, integratedRep, h_int, add_smul, strongIntegral_apply, integral_add]
      map_smul' := by simp [DFunLike.ext_iff, integratedRep, h_int, mul_smul, Integrable.fun_smul,
        strongIntegral_apply, integral_smul] }
  have h_real (Y : unitaryLie (signMatrix ε)) (f : (-l).DsModule) (v : M) :
      ∫ g : USign ε, f.val.val g • π g (ι (ρ Y v)) =
        -∫ g : USign ε, ((-l).dsAction Y f).val.val g • π g (ι v) := by
    let F (g : USign ε) : X := f.val.val g • π g (ι v)
    let F' (g : USign ε) : X :=
      f.val.val g • π g (ι (ρ Y v)) + ((-l).dsAction Y f).val.val g • π g (ι v)
    have hF : Integrable F := h_int f (ι v)
    have hF' : Integrable F' := (h_int f _).add (h_int _ _)
    have h_deriv (g : USign ε) (t : ℝ) :
        HasDerivAt (fun s : ℝ ↦ F (g * expU (s • Y))) (F' (g * expU (t • Y))) t :=
      (hasDerivAt_rightDeriv_expU f.val g Y t).smul (hd.isCoeffMap 1 g Y v t)
    have h_cont (g : USign ε) : Continuous fun t : ℝ ↦ F' (g * expU (t • Y)) := by fun_prop
    have h_ftc (g : USign ε) :
        ∫ t in Set.Ioc (0 : ℝ) 1, F' (g * expU (t • Y)) = F (g * expU Y) - F g := by
      simpa [intervalIntegral.integral_of_le] using intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ ↦ h_deriv g t) ((h_cont g).intervalIntegrable 0 1)
    rw [← add_eq_zero_iff_eq_neg, ← integral_add (h_int f _) (h_int _ _)]
    calc ∫ g : USign ε, F' g = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ g : USign ε, F' g := by simp
      _ = ∫ g : USign ε, ∫ t in Set.Ioc (0 : ℝ) 1, F' (g * expU (t • Y)) :=
        (integral_skew_product (fun t ↦ map_mul_right_eq_self volume (expU (t • Y)))
          (hF'.comp_snd _)).2.symm
      _ = ∫ g : USign ε, (F (g * expU Y) - F g) := by simp only [h_ftc]
      _ = 0 := by simp [integral_sub (hF.comp_mul_right _) hF, integral_mul_right_eq_self F]
  refine ⟨l.formalDegree • P, ?_, fun Y f v ↦ ?_⟩
  · -- the generator `(-l).dsGenerator` is the conjugate of `l.dsCoeff`
    have h_kernel :
        l.dsKernel = (l.formalDegree • (-l).dsGenerator : (-l).DsModule).val.val :=
      funext fun g ↦ by simp [dsKernel]
    rw [h_kernel]
    exact P.map_smul l.formalDegree (-l).dsGenerator
  · -- a complex matrix is `Y₁ + I • Y₂` with `Y₁`, `Y₂` in the real Lie algebra
    rw [eq_unitaryLiePart_add_I_smul ε Y]
    -- expand both sides by linearity and use `h_real` on `Y₁` and `Y₂`
    simp [↓map_add, P, integratedRep, h_int, h_real, strongIntegral_apply]
    abel

/-- Let `l = 2λ` have gap `500 n³ + A`, let `e_λ = l.dsKernel`, and let `π` be a representation of
`U(diag ε)` on `X` with `IsUnitaryRep A π B` (strongly continuous, `‖π g‖ ≤ C‖g‖^A`, `B` hermitian,
positive definite and invariant) whose derivative along `ι` is the `gl n`-module `ρ`. Then
`π(e_λ) ι(Ω v) = κ_λ π(e_λ) ι(v)` for every `v`. Here `π(e_λ) = integratedRep π l.dsKernel`,
`Ω = ρ.casimirK 1` is the Casimir operator of `gl n`, and `κ_λ = New.HCParam.casimirValue l`. -/
theorem integratedRep_dsKernel_casimir (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) :
    integratedRep π l.dsKernel (ι (ρ.casimirK 1 v)) =
      ofReal l.casimirValue • integratedRep π l.dsKernel (ι v) := by
  obtain ⟨P, hP_eq, hP_ibp⟩ := exists_integration_by_parts hg hu hd
  -- the lemma on the Casimir value of `c_{-λ}` takes the gap of `-l` as an instance
  have gap_neg : (-l).HasLargeGap A := hg.neg
  have h_generator : (-l).dsAction.casimirK 1 (-l).dsGenerator =
      ofReal (-l).casimirValue • (-l).dsGenerator :=
    casimirK_generatedModule casimir_dsCoeffSmooth _
  -- integrate by parts twice (the signs cancel and `E a b`, `E b a` change places), then use the
  -- Casimir value at the generator
  calc
    integratedRep π l.dsKernel (ι (ρ.casimirK 1 v))
      = P ((-l).dsAction.casimirK 1 (-l).dsGenerator) (ι v) := by
        simpa [hP_eq, hP_ibp, casimir] using Finset.sum_comm
    _ = ofReal l.casimirValue • integratedRep π l.dsKernel (ι v) := by
        simp [hP_eq, h_generator, casimirValue, twoRho_neg]

omit [CompleteSpace X] [Nonempty n] in
/-- For `π` as in `New.IsUnitaryRep` with derivative `ρ` along `ι`, the weight `ν` of a `K`-highest
vector `v` with `ι v ≠ 0` is `K`-dominant for the order `-l`: if `ε a = ε b` and `l b < l a`, then
`ν b ≤ ν a`. -/
theorem HCParam.IsKHighest.isKDominant_of_isUnitaryRep (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) {ν : n → ℤ} (hv : l.IsKHighest ρ ν v) (hv_ne : ι v ≠ 0) :
    IsKDominant ε (-l) ν := by
  intro a b h_sign h_lt
  -- the square norm of `ι (E b a v)` is `ν a - ν b` times that of `ι v`
  obtain ⟨H, _, _, j, h_inner, -⟩ := hu.exists_innerProductSpace
  have norm_nonneg : 0 ≤ RCLike.re (B (ι (ρ.E b a v)) (ι (ρ.E b a v))) := by
    simpa only [← h_inner] using inner_self_nonneg
  rw [hd.form_E_eq_sign_mul hu] at norm_nonneg
  have h_comm : ρ.E a b (ρ.E b a v) = ((ν a : ℂ) - ν b) • v := by
    simp_all [ρ.apply_apply_eq_swap_add_bracket, IsKHighest, sub_smul]
  simp_all [hu.pos (ι v) hv_ne]

/-- Let `λ = l / 2` have gap `500 n³ + A`, let `π` be as in `New.IsUnitaryRep` with derivative `ρ`
along `ι`, and let `v` be `K`-highest of weight `ν`. Suppose `ν - New.HCParam.lowestKType l` lies
outside `New.HCParam.rootCone l`, the cone of integer vectors `β` with `o ⬝ᵥ β ≤ 0` for every
integer `o` strictly reversing the order of `l`; this cone contains all sums of the roots
`e_a − e_b` with `l b < l a`. Then `π(e_λ)` kills every translate `π y (ι v)`, where
`e_λ = New.HCParam.dsKernel l` is `g ↦ deg_λ · conj(c_λ(g))` and `π(e_λ) x = ∫ e_λ(g) π(g) x dg`. -/
theorem integratedRep_eq_zero_of_notMem_rootCone (hg : l.HasLargeGap A)
    (hu : IsUnitaryRep A π B) (hd : IsDerivedAction π ι ρ) {ν : n → ℤ}
    (hv : l.IsKHighest ρ ν v) (hν_cone : ν - l.lowestKType ∉ l.rootCone) (y : USign ε) :
    integratedRep π l.dsKernel (π y (ι v)) = 0 := by
  -- Averaging over `K` against `conj (weightMinors ν k)` multiplies `ι v` by `kTypeNormSq ν > 0`,
  -- but kills `dsCoeff` when `ν - l.lowestKType` is outside the cone. So the integral of `dsCoeff`
  -- against any coefficient of `π y (ι v)` vanishes, and the form of
  -- `integratedRep π l.dsKernel (π y (ι v))` with itself is one of these.
  by_contra h_ne
  -- `B` is an inner product for which `π` acts by isometries; so its coefficients are bounded.
  obtain ⟨H, _, _, j, h_inner, h_norm⟩ := hu.exists_innerProductSpace
  have hν : IsKDominant ε (-l) ν :=
    hv.isKDominant_of_isUnitaryRep hu hd fun h_zero ↦ h_ne (by simp [h_zero])
  let T : ℂ := (toHCParam ε ν).kTypeNormSq
  have h_vec (w : X) :
      ∫ k : maxCompactU ε, conj (weightMinors ν k) * B (π k.val⁻¹ w) (ι v) ∂haarK ε =
        T * B w (ι v) := by
    simpa [T, hu.form_apply_eq_form_inv_apply] using
      hv.integral_conj_weightMinors_mul hu hd hν (B w)
  have h_psi (g : USign ε) :
      ∫ k : maxCompactU ε, conj (weightMinors ν k) * l.dsCoeff ↑(y * k * g) ∂haarK ε = 0 :=
    integral_conj_weightMinors_mul_dsCoeff_eq_zero hg y g hν hν_cone
  have h_zero (w : X) : ∫ g : USign ε, l.dsCoeff g * B (π y⁻¹ (π g w)) (ι v) = 0 := by
    -- Move the average over `K` from the coefficient to `dsCoeff`: `integral_conv` evaluates one
    -- double integral with the average on the coefficient (`on_vec`) or on `dsCoeff` (`on_psi`).
    have h_bdd : IsBoundedMeasurable fun g : USign ε ↦ B w (π g⁻¹ (ι v)) :=
      .of_continuous ⟨‖j w‖ * ‖j (ι v)‖, fun g ↦ by grw [← h_inner, norm_inner_le_norm, h_norm]⟩
    obtain ⟨on_vec, on_psi⟩ :=
      integral_conv (fun k : maxCompactU ε ↦ (y * k.val)⁻¹) (ν := haarK ε)
        (k := fun k : maxCompactU ε ↦ conj (weightMinors ν k))
        (integrable_of_compactSpace (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero])))
        (hg.integrable l.dsGenerator) h_bdd
    have h_exchange :
        ∫ g : USign ε, l.dsCoeff g *
          (∫ k : maxCompactU ε, conj (weightMinors ν k) *
            B w (π ((y * k)⁻¹ * g)⁻¹ (ι v)) ∂haarK ε) =
        ∫ g : USign ε, (∫ k : maxCompactU ε, conj (weightMinors ν k) *
            l.dsCoeff ↑(y * k * g) ∂haarK ε) * B w (π g⁻¹ (ι v)) := by
      simpa using on_vec.symm.trans on_psi
    have h_average (g : USign ε) :
        ∫ k : maxCompactU ε, conj (weightMinors ν k) *
          B w (π ((y * k)⁻¹ * g)⁻¹ (ι v)) ∂haarK ε = T * B (π y⁻¹ (π g w)) (ι v) := by
      simpa [hu.form_apply_eq_form_inv_apply, rep_apply_apply, mul_assoc, -map_mul] using
        h_vec (π y⁻¹ (π g w))
    simp only [h_average, h_psi, zero_mul, integral_zero, mul_left_comm (l.dsCoeff _),
      integral_const_mul] at h_exchange
    exact (mul_eq_zero.1 h_exchange).resolve_left (by simp [T, ne_of_gt])
  let w : X := integratedRep π l.dsKernel (π y (ι v))
  have h_integrand (g : USign ε) : l.dsKernel g⁻¹ • B w (π g⁻¹ (π y (ι v))) =
      l.formalDegree * (l.dsCoeff g * B (π y⁻¹ (π g w)) (ι v)) := by
    simp [dsKernel, ↓dsCoeff_inv, hu.form_apply_eq_form_inv_apply, mul_assoc]
  have h_self : B w w = 0 := by
    rw [map_integratedRep hu (hg.integrable_dsKernel_mul_norm_pow A A.le_succ),
      ← integral_inv_eq_self]
    simp only [h_integrand, integral_const_mul, h_zero, mul_zero]
  simpa [h_self] using hu.pos w h_ne

/-- Let `λ = l / 2` have gap `500 n³ + A`, let `π` be a representation of `U(diag ε)` with invariant
positive form `B` and growth exponent `A` (`New.IsUnitaryRep`), and let `ρ` be its derivative along
`ι`. Let `v` be `K`-highest of weight `Λ = New.HCParam.lowestKType l` and `x = ι v`. If
`B x (π z x) > 0` for every positive definite `z` in `U(diag ε)`, then `Re B x (π(e_λ) x) > 0`,
where `e_λ = New.HCParam.dsKernel l` is the function `g ↦ deg_λ · conj(c_λ(g))` and
`π(e_λ) x = ∫ e_λ(g) π(g) x dg`. -/
theorem re_integratedRep_dsKernel_pos (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) (hv : l.IsKHighest ρ l.lowestKType v)
    (h_pos : ∀ z : USign ε, z.val.val.PosDef → 0 < B (ι v) (π z (ι v))) :
    0 < (B (ι v) (integratedRep π l.dsKernel (ι v))).re := by
  -- Average the integrand over `g ↦ k₁⁻¹ g k₂`, `k₁, k₂ ∈ K`. At `g = κ z` the average is, by
  -- `dsCoeff_polar`, `h_left` and `h_right`, a mean over `K` of positive numbers.
  set Λ : HCParam ε := l.lowestKType
  set x : X := ι v
  -- Averaging over `K` against `conj (weightMinors Λ)` in the second argument of `B`, or against
  -- `weightMinors Λ` in the first, multiplies `x` by `Λ.kTypeNormSq`.
  have h_right (w : X) (g : USign ε) :
      ∫ k : maxCompactU ε, weightMinors Λ k.val.val.valᴴ * B w (π (g * k) x) ∂haarK ε =
        Λ.kTypeNormSq * B w (π g x) := by
    simpa [rep_apply_apply, -map_mul, conj_weightMinors] using
      hv.integral_conj_weightMinors_mul hu hd hg.isKDominant_lowestKType (B w ∘L π g)
  have h_left (w : X) :
      ∫ k : maxCompactU ε, weightMinors Λ k * B x (π k.val⁻¹ w) ∂haarK ε =
        Λ.kTypeNormSq * B x w := by
    simpa [← integral_conj, hu.conj_symm, hu.form_apply_eq_form_inv_apply _ w, -map_mul,
      RingHom.map_mul, conj_weightMinors] using congrArg conj (h_right w 1)
  let μ : Measure (maxCompactU ε × maxCompactU ε) := (haarK ε).prod (haarK ε)
  let Φ (g : USign ε) : ℂ := B x (l.dsKernel g • π g x)
  have kernel_int : Integrable fun g : USign ε ↦ l.dsKernel g * (‖(g : Matrix n n ℂ)‖ : ℂ) ^ A :=
    hg.integrable_dsKernel_mul_norm_pow A A.le_succ
  have Φ_int : Integrable Φ := (B x).integrable_comp (integrable_smul_rep hu kernel_int x)
  have h_invariant (k : maxCompactU ε × maxCompactU ε) :
      Measure.map (fun g : USign ε ↦ ↑k.1⁻¹ * (g * k.2)) volume = volume :=
    ((measurePreserving_mul_right _ k.2.val).mul_left _ (k.1⁻¹).val).map_eq
  -- The average of `Φ` over `K × K` is integrable, with the same integral as `Φ`.
  obtain ⟨avg_int, avg_eq⟩ := integral_skew_product h_invariant (Φ_int.comp_snd μ)
  have h_avg : B x (integratedRep π l.dsKernel x) =
      ∫ g : USign ε, ∫ k, Φ (↑k.1⁻¹ * (g * k.2)) ∂μ := by
    rw [avg_eq]
    simp [Φ, map_integratedRep hu kernel_int]
  refine (re_integral_pos avg_int fun g ↦ ?_).trans_eq (congrArg re h_avg.symm)
  change 0 < (∫ k, Φ (↑k.1⁻¹ * (g * k.2)) ∂μ).re
  obtain ⟨κ, z, hz, rfl, -⟩ := exists_polar g
  have conj_pos (u : USign ε) : (u.val.valᴴ * z.val.val * u.val.val).PosDef :=
    hz.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 u.val.isUnit)
  -- `dsCoeff_polar` writes `Φ (k₁⁻¹ κ z k₂)` as the mean over `u ∈ K` of `Ψ (k₁, k₂) u`.
  let Ψ (k : maxCompactU ε × maxCompactU ε) (u : maxCompactU ε) : ℂ :=
    l.formalDegree * (weightMinors Λ (u.val.val.valᴴ * κ.val.val.valᴴ * k.1) *
      weightMinors Λ (k.2.val.val.valᴴ * u) /
        weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u) / Λ.kTypeNormSq) *
      B x (π (k.1⁻¹ * κ * z * k.2) x)
  have h_polar (k : maxCompactU ε × maxCompactU ε) :
      ∫ u, Ψ k u ∂haarK ε = Φ (↑k.1⁻¹ * (κ * z * k.2)) := by
    have h_coeff : conj (l.dsCoeff ↑(↑k.1⁻¹ * (κ * z * k.2) : USign ε)) =
        (∫ u : maxCompactU ε, weightMinors Λ (u.val.val.valᴴ * κ.val.val.valᴴ * k.1) *
          weightMinors Λ (k.2.val.val.valᴴ * u) /
            weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u) ∂haarK ε) / Λ.kTypeNormSq := by
      simpa [mul_assoc, maxCompactU.coe_inv, conj_weightMinors, ← integral_conj, hz.1.eq,
        RingHom.map_mul] using congrArg conj (dsCoeff_polar hg (k.1⁻¹ * κ) k.2⁻¹ hz)
    simp only [Φ, Ψ, dsKernel, h_coeff, map_smul, smul_eq_mul]
    simp only [integral_mul_const, integral_const_mul, integral_div, mul_assoc]
  have Ψ_int : Integrable Ψ.uncurry (μ.prod (haarK ε)) :=
    integrable_of_compactSpace (by fun_prop (disch :=
      simp [conj_pos, GeneralLinearGroup.det_ne_zero, weightMinors_pos, ne_of_gt]))
  -- For fixed `u`, substitute `(κ u k₁, u k₂)` for `(k₁, k₂)` and use `h_left`, `h_right`.
  have h_inner (u : maxCompactU ε) :
      ∫ k, Ψ k u ∂μ = Λ.kTypeNormSq * l.formalDegree *
        (weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u))⁻¹ *
          B x (π (u⁻¹ * z * u) x) := by
    let c : ℂ := l.formalDegree / weightMinors (-paramAddRho l) (u.val.val.valᴴ * z * u) /
      Λ.kTypeNormSq
    have h_subst (k₁ k₂ : maxCompactU ε) : Ψ ((κ * u, u) * (k₁, k₂)) u = c *
        (weightMinors Λ k₂.val.val.valᴴ *
          (weightMinors Λ k₁ * B x (π k₁.val⁻¹ (π (u⁻¹ * z * u * k₂) x)))) := by
      simp [Ψ, c, rep_apply_apply, -map_mul, ← maxCompactU.coe_inv, mul_assoc, div_eq_inv_mul,
        Matrix.mul_inv_rev]
      ring
    rw [← integral_mul_left_eq_self _ (κ * u, u), integral_prod_symm _
      (integrable_of_compactSpace (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero])))]
    simp only [h_subst, integral_const_mul, h_left, mul_left_comm _ (ofReal Λ.kTypeNormSq), h_right]
    simp [c, field]
  -- Each factor on the right of `h_inner` is positive, `u⁻¹ z u` being positive definite.
  have h_inner_pos (u : maxCompactU ε) : 0 < ∫ k, Ψ k u ∂μ := by
    simp [h_inner, h_pos, conj_pos, -map_mul, maxCompactU.coe_inv, weightMinors_pos]
  simp_rw [← h_polar, integral_integral_swap Ψ_int]
  exact re_integral_pos Ψ_int.integral_prod_right fun u ↦ (pos_iff.1 (h_inner_pos u)).1

/-! ### Rigidity of highest vectors -/

omit [Nonempty n] in
/-- Let two `gl n`-modules on inner product spaces have inner products invariant under `𝔲(ε)` and
Casimir operator at least `New.HCParam.casimirValue l` (`New.IsUnitaryCasimirGe`). Then the
componentwise action on their orthogonal direct sum is a `gl n`-module with the same property. -/
theorem IsUnitaryCasimirGe.exists_prodL2 {H₁ H₂ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {ρ₁ : GlModule n H₁} {ρ₂ : GlModule n H₂} (h₁ : IsUnitaryCasimirGe l ρ₁)
    (h₂ : IsUnitaryCasimirGe l ρ₂) :
    ∃ P : GlModule n (WithLp 2 (H₁ × H₂)),
      (∀ (Y : Matrix n n ℂ) (w : WithLp 2 (H₁ × H₂)), P Y w = toLp 2 (ρ₁ Y w.fst, ρ₂ Y w.snd)) ∧
      IsUnitaryCasimirGe l P := by
  let P : GlModule n (WithLp 2 (H₁ × H₂)) :=
    { ρ := (WithLp.linearEquiv 2 ℂ (H₁ × H₂)).symm.conj.toLinearMap ∘ₗ
        LinearMap.prodMapLinear ℂ H₁ H₂ H₁ H₂ ℂ ∘ₗ ρ₁.ρ.prod ρ₂.ρ
      map_bracket := by simp [DFunLike.ext_iff, map_bracket, WithLp.ext_iff] }
  have P_apply (Y : Matrix n n ℂ) (w : WithLp 2 (H₁ × H₂)) :
      P Y w = toLp 2 (ρ₁ Y w.fst, ρ₂ Y w.snd) := rfl
  -- inner products, square norms and Casimir operators add up over the two components
  refine ⟨P, P_apply, fun a b v w ↦ ?_, fun y ↦ ?_⟩
  · simp [P_apply, h₁.inner_E_left, h₂.inner_E_left, mul_add]
  · have h_casimir : P.casimirK 1 y = toLp 2 (ρ₁.casimirK 1 y.fst, ρ₂.casimirK 1 y.snd) := by
      simp [casimir, P_apply, WithLp.ext_iff, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
    rw [h_casimir, prod_norm_sq_eq_of_L2, mul_add, WithLp.prod_inner_apply, add_re]
    exact add_le_add (h₁.casimirValue_mul_le y.fst) (h₂.casimirValue_mul_le y.snd)

attribute [-simp] Complex.coe_smul coe_inner Subtype.forall in
omit [CompleteSpace X] [Nonempty n] in
/-- Let `π` be a representation of `U(diag ε)` on the normed space `X` with `IsUnitaryRep A π B`: it
is strongly continuous with `‖π g‖ ≤ C‖g‖^A`, and `B` is a hermitian, positive definite,
`π`-invariant bounded form. Let `ρ` be the `gl n`-module on `M` that is the derivative of `π` along
`ι`, let `j` carry `B` to the inner product of `H`, and let `ι (Ω v) = c • ι v` with
`Ω = ρ.casimirK 1` and `c ≥ κ_λ = New.HCParam.casimirValue l = |λ|² − |ρ|²`, where `l = 2λ` and this
`ρ` is the half-sum of positive roots, not the module. Then `ρ` descends to a `gl n`-module `σ` on
the range of `j ∘ ι`, compatible with `ρ`, and the submodule generated by `j (ι v)` is as in
`New.IsUnitaryCasimirGe`: its inner product is invariant under `𝔲(ε)` and its Casimir operator is at
least `κ_λ`. -/
theorem exists_isUnitaryCasimirGe_generatedModule (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (j : X ≃ₗ[ℂ] H) (inner_j : ∀ x y : X, inner ℂ (j x) (j y) = B x y)
    (hv_casimir : ι (ρ.casimirK 1 v) = ofReal c • ι v) (hc_ge : l.casimirValue ≤ c) :
    ∃ σ : GlModule n (j.toLinearMap ∘ₗ ι).range,
      (∀ (Y : Matrix n n ℂ) (w : M), σ Y ((j.toLinearMap ∘ₗ ι).rangeRestrict w) =
        (j.toLinearMap ∘ₗ ι).rangeRestrict (ρ Y w)) ∧
      IsUnitaryCasimirGe l (σ.generatedModule ((j.toLinearMap ∘ₗ ι).rangeRestrict v)) := by
  let jι : M →ₗ[ℂ] H := j.toLinearMap ∘ₗ ι
  let x : jι.range := jι.rangeRestrict v
  have skew (a b : n) (u w : M) :
      B (ι (ρ.E a b u)) (ι w) = (ε a * ε b).val * B (ι u) (ι (ρ.E b a w)) :=
    hd.form_E_eq_sign_mul hu a b u w
  -- by skewness `ρ` keeps the kernel of `ι`, so it descends to a module `σ` on the range
  have h_ker (Y : Matrix n n ℂ) (w : M) (hw : jι w = 0) : jι (ρ Y w) = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    nth_rw 1 [apply_eq_sum]
    simp_all [jι]
  obtain ⟨σ, σ_apply⟩ := ρ.exists_action_on_range jι h_ker
  refine ⟨σ, σ_apply, ?_⟩
  change IsUnitaryCasimirGe l (σ.generatedModule x)
  refine ⟨?_, fun y ↦ ?_⟩
  · rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := jι.surjective_rangeRestrict y
    obtain ⟨w, rfl⟩ := jι.surjective_rangeRestrict z
    have gen_apply (Y : Matrix n n ℂ) (u : M) (hu_mem : jι.rangeRestrict u ∈ σ.filtration 1 x 0) :
        (σ.generatedModule x Y ⟨jι.rangeRestrict u, hu_mem⟩ : H) = j (ι (ρ Y u)) :=
      congrArg Subtype.val (σ_apply Y u)
    simp [coe_inner, gen_apply, jι, inner_j, skew]
  · -- `Ω` acts on all of the generated module by `c`
    have Ω_x : σ.casimirK 1 x = ofReal c • x := by
      ext
      simpa [x, jι, casimir, σ_apply, ← map_sum] using congrArg j hv_casimir
    grw [hc_ge, casimirK_generatedModule Ω_x]
    simp [sq]

attribute [-simp] Complex.coe_smul coe_inner Subtype.forall in
omit [CompleteSpace X] in
/-- Rigidity. Let `λ` have gap `500 n³ + A`, let `π` be a representation of `U(diag ε)` with
invariant positive form `B` and growth exponent `A` (`New.IsUnitaryRep`), and `ρ` its derivative
along `ι`. Let `v` be `K`-highest of weight `New.HCParam.lowestKType l` with `ι (Ω v) = c • ι v` for
the Casimir operator `Ω` of `gl n`, where `c ≥ New.HCParam.casimirValue l`. Then
`B (ι v) (π g (ι v)) = B (ι v) (ι v) c_λ(g)` for all `g`, where `c_λ = New.HCParam.dsCoeff l`.

A variant of Parthasarathy's criterion recognizing a discrete series by its lowest `K`-type `μ`: for
a large gap, with a Casimir bound in place of the absence of the types `μ - α`, as an equality of
matrix coefficients. -/
theorem coeff_eq_dsCoeff_of_isKHighest (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) (hv : l.IsKHighest ρ l.lowestKType v)
    (hv_casimir : ι (ρ.casimirK 1 v) = ofReal c • ι v) (hc_ge : l.casimirValue ≤ c) (g : USign ε) :
    B (ι v) (π g (ι v)) = B (ι v) (ι v) * l.dsCoeff g := by
  -- Let `x` be the image of `v` in an inner product space for `B` (`inner_j`), on which `π` acts
  -- by isometries (`norm_j`). In the sum of the module generated by `x` with `l.DsModule` the
  -- vector `(x, -⟪x, x⟫ • dsGenerator)` is highest and orthogonal to `(x, dsGenerator)`, hence to
  -- all that the latter generates. Test this on coefficients.
  obtain ⟨H, _, _, j, inner_j, norm_j⟩ := hu.exists_innerProductSpace
  let jι : M →ₗ[ℂ] H := j.toLinearMap ∘ₗ ι
  let x : jι.range := jι.rangeRestrict v
  obtain ⟨σ, σ_apply, gen_unitary⟩ : ∃ σ : GlModule n jι.range,
      (∀ (Y : Matrix n n ℂ) (w : M), σ Y (jι.rangeRestrict w) = jι.rangeRestrict (ρ Y w)) ∧
      IsUnitaryCasimirGe l (σ.generatedModule x) :=
    exists_isUnitaryCasimirGe_generatedModule hu hd j inner_j hv_casimir hc_ge
  have gen_apply (Y : Matrix n n ℂ) (u : M) (hu_mem : jι.rangeRestrict u ∈ σ.filtration 1 x 0) :
      (σ.generatedModule x Y ⟨jι.rangeRestrict u, hu_mem⟩ : H) = j (ι (ρ Y u)) :=
    congrArg Subtype.val (σ_apply Y u)
  -- the componentwise action `P` on the orthogonal sum of the two modules
  obtain ⟨P, P_apply, P_unitary⟩ := gen_unitary.exists_prodL2 hg.isUnitaryCasimirGe
  let d (t : ℂ) : WithLp 2 (σ.filtration 1 x 0 × l.DsModule) :=
    toLp 2 (⟨x, self_mem_filtration⟩, t • l.dsGenerator)
  have highest (t : ℂ) : l.IsKHighest P l.lowestKType (d t) := by
    have gen_highest := isKHighest_dsGenerator hg
    have gen_mk (Y : Matrix n n ℂ) (y : σ.filtration 1 x 0) :
        σ.generatedModule x Y y = ⟨σ Y y.val, (σ.generatedModule x Y y).prop⟩ := rfl
    simp_all [d, x, jι, smul_smul, mul_comm, IsKHighest, WithLp.ext_iff]
  -- A highest vector is orthogonal to lowered vectors, and `norm_dsGenerator` handles `d 1` itself.
  have perp_zero : d (-inner ℂ x x) ∈ (P.filtration ε (d 1) 0)ᗮ :=
    (highest 1).filtration_le_of_word_mem (innerSLFlip ℂ _).ker
      (by simp +contextual [P_unitary.inner_E_left, (highest _).2, -neg_smul,
        Module.End.mem_invtSubmodule_iff_forall_mem_of_mem])
      (by simp [d, hg.norm_dsGenerator, word, ← norm_coe])
  -- Orthogonality to the step `0` of the filtration spreads to all steps.
  have perp (s : ℕ) : d (-inner ℂ x x) ∈ (P.filtration ε (d 1) s)ᗮ :=
    mem_orthogonal_filtration_of_casimirK 0 P_unitary (highest 1) _ (highest _).casimirK_eq_smul
      (by simp) perp_zero s
  -- the coefficient map `(j (ι u), w) ↦ B (ι v) (π g (ι u)) - ⟪x, x⟫ * w g` is bounded, and by
  -- `perp` it vanishes for `g = 1` on all that `d 1` generates; so it vanishes on `d 1` for every
  -- `g` (analytic vectors, `coeffMap_eq_zero`)
  let coef (g : USign ε) : WithLp 2 (σ.filtration 1 x 0 × l.DsModule) →ₗ[ℂ] ℂ :=
    { toFun w := B (ι v) (π g (j.symm w.fst)) - inner ℂ x x * w.snd.val.val g
      map_add' w w' := by simp [mul_add, add_sub_add_comm]
      map_smul' t w := by simp [mul_sub, mul_left_comm] }
  have coef_apply (g : USign ε) (w : WithLp 2 (σ.filtration 1 x 0 × l.DsModule)) :
      coef g w = B (ι v) (π g (j.symm w.fst)) - inner ℂ x x * w.snd.val.val g := rfl
  have is_coef : P.IsCoeffMap coef := by
    rintro g Y ⟨⟨y, hy⟩, w⟩ t
    obtain ⟨u, rfl⟩ := jι.surjective_rangeRestrict y
    simp only [coef_apply, P_apply, WithLp.toLp_fst, WithLp.toLp_snd, gen_apply]
    refine .sub ?_ (.const_mul _ (hasDerivAt_rightDeriv_expU ..))
    simpa [jι] using hd.isCoeffMap (B (ι v)) g Y u t
  have bounded (g : USign ε) (w : WithLp 2 (σ.filtration 1 x 0 × l.DsModule)) :
      ‖coef g w‖ ≤ (‖j (ι v)‖ + ‖inner ℂ x x‖) * ‖w‖ := by
    have h_fst : ‖B (ι v) (π g (j.symm w.fst))‖ ≤ ‖j (ι v)‖ * ‖w‖ := by
      grw [← inner_j, norm_inner_le_norm, norm_j, j.apply_symm_apply, norm_coe, norm_coe,
        WithLp.norm_fst_le]
    grw [coef_apply, norm_sub_le, norm_mul, h_fst, hg.norm_apply_le_norm, WithLp.norm_snd_le,
      add_mul]
  have at_one (s : ℕ) (w : WithLp 2 (σ.filtration 1 x 0 × l.DsModule))
      (hw : w ∈ P.filtration ε (d 1) s) : coef 1 w = 0 := by
    have h_inner : inner ℂ (d (-inner ℂ x x)) w = coef 1 w := by
      have inner_fst : inner ℂ ⟨x, self_mem_filtration⟩ w.fst = B (ι v) (j.symm w.fst) := by
        rw [← inner_j, j.apply_symm_apply, coe_inner, coe_inner]
        rfl
      have inner_snd : inner ℂ l.dsGenerator w.snd = w.snd.val.val 1 := by
        rw [← hg.isDerivedAction_toL2_and_inner_toL2.2.1, map_one]
        rfl
      simp [coef_apply, d, inner_fst, inner_snd, ↓inner_smul_left, sub_eq_add_neg]
    rw [← h_inner]
    exact inner_left_of_mem_orthogonal hw (perp s)
  have h_zero : coef g (d 1) = 0 :=
    (highest 1).coeffMap_eq_zero P_unitary is_coef bounded at_one g
  have x_norm_sq : inner ℂ x x = B (ι v) (ι v) := inner_j (ι v) (ι v)
  rw [coef_apply, x_norm_sq] at h_zero
  simpa [d, x, jι, sub_eq_zero] using h_zero

/-- Let `λ = l / 2` have gap `500 n³ + A`, let `π`, `B` be as in `New.IsUnitaryRep` with
exponent `A`, `ρ` the derivative of `π` along `ι`, and `‖g‖ ^ A • f g` integrable. Suppose (a)
`f * e_λ = e_λ` for `e_λ = New.HCParam.dsKernel l`; (b) `v` is `K`-highest of weight
`New.HCParam.lowestKType l`; (c) `ι (Ω v) = c • ι v` for the Casimir operator `Ω = ρ.casimirK 1`,
with `c ≥ New.HCParam.casimirValue l`. Then `π(f) = ∫ f(g) π(g) dg` fixes `ι v`. -/
theorem integratedRep_fix_of_isKHighest (hg : l.HasLargeGap A) (hu : IsUnitaryRep A π B)
    (hd : IsDerivedAction π ι ρ) (hf : Integrable fun g : USign ε ↦ f g * ‖g.val.val‖ ^ A)
    (hv : l.IsKHighest ρ l.lowestKType v) (hv_casimir : ι (ρ.casimirK 1 v) = ofReal c • ι v)
    (hc_ge : l.casimirValue ≤ c)
    (h_repr : ∀ g : USign ε, ∫ y : USign ε, f y * l.dsKernel (y⁻¹ * g) = l.dsKernel g) :
    integratedRep π f (ι v) = ι v := by
  -- The vector `d = π(f) x - x`, with `x = ι v`, is orthogonal to the orbit of `x`, by `h_repr` and
  -- `B x (π g x) = B x x * l.dsCoeff g` (`coeff_eq_dsCoeff_of_isKHighest`); so it is orthogonal to
  -- itself.
  by_contra h_ne
  have h_psi (g : USign ε) : ∫ y : USign ε, f y * l.dsCoeff ↑(g * y) = l.dsCoeff g := by
    simpa [↓← dsCoeff_inv, mul_left_comm (f _), dsKernel, integral_const_mul, ne_of_gt] using
      h_repr g⁻¹
  let d : X := integratedRep π f (ι v) - ι v
  have h_orth (g : USign ε) : B d (π g (ι v)) = 0 := by
    rw [← hu.conj_symm, map_sub, map_integratedRep hu hf, ← inv_inv g]
    simp only [← hu.form_apply_eq_form_inv_apply, rep_apply_apply,
      coeff_eq_dsCoeff_of_isKHighest hg hu hd hv hv_casimir hc_ge, smul_eq_mul, mul_left_comm (f _),
      integral_const_mul, h_psi, sub_self, map_zero]
  have h_zero : B d d = 0 := calc
    _ = B d (integratedRep π f (ι v)) - B d (π 1 (ι v)) := by rw [map_one, ← map_sub]; rfl
    _ = 0 := by simp only [map_integratedRep hu hf, h_orth, smul_zero, integral_zero, sub_zero]
  simpa [h_zero] using hu.pos d (sub_ne_zero.2 h_ne)

end New
