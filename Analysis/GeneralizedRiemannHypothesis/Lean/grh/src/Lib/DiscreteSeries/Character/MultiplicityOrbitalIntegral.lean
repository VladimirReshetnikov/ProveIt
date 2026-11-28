import Lib.DiscreteSeries.Character.WeylCharacterFormula
import Lib.DiscreteSeries.Rigidity.KernelFixes

/-!
# K-type multiplicities of the discrete series and orbital integrals as Laurent polynomials

Let `G = New.USign ε` be the unitary group of `diag ε`, and let `K = New.maxCompactU ε` be its
subgroup of unitary matrices. Let `ψ = New.HCParam.dsCoeff l` be the discrete series coefficient
with parameter `l = 2λ`. On the torus `New.diagTorus ε`, consider the normalised orbital integral
Θ(x) = `New.HCParam.formalDegree l` ∫_G ψ(g⁻¹ x g) dg. Θ times suitable products of differences
`x_a - x_b` is a Laurent polynomial, and the integrality of the multiplicities is the key input for
this.

## Main definitions and results

* `New.Orbital.exists_kType_multiplicity`: for a dominant weight ν and a large gap,
  `formalDegree * ∫_G ∫_K conj (kTypeChar ν k) ψ(g⁻¹ k g)` is a natural number, `1` for ν equal to
  the lowest `K`-type `New.HCParam.lowestKType l` and `0` for ν off
  `lowestKType l + New.HCParam.rootCone l`.
* `New.Orbital.integrable_mul_dsCoeff_conj`: for the gap 500 n³ + 10 n⁵, the orbital integrals times
  a power of the product over the noncompact roots converge absolutely, uniformly on `K`.
* `New.Orbital.IsConeSeriesMultiple`: `P` is `D` times a formal series with coefficient `1` at
  `x^a` whose exponents lie in alternants of weights in `a` plus the root cone.
* `New.Orbital.exists_laurent_orbital_integral`: the orbital integral times the denominators is a
  Laurent polynomial that is such a multiple.

Notions from other files:
* `New.weightMinors`: the coefficient m_ν of a highest vector of weight ν, a product of principal
  minors and a power of the determinant.
* `New.HCParam.HasLargeGap`: l = 2λ is a parameter with |λ_i - λ_j| ≥ 500 n³ + A whenever
  ε_i ≠ ε_j.
* `New.IsKDominant ε (-l) ν`, below "`K`-dominant in the order of `-l`": `ν j ≤ ν i` whenever
  `ε i = ε j` and `l j < l i`, so ν is dominant for the compact roots that are positive for l.
* `New.HCParam.lowestKType`: Λ = λ + ρ - 2ρ_c, the highest weight of the lowest K-type.
* `New.HCParam.formalDegree`: for signs ε and l = 2λ, the reciprocal of the integral of |c_λ|² over
  U(diag ε) for the compact dual measure.

## Relation to the literature

See `Lib.DiscreteSeries.Character.FormalDegree`.
-/

/-!
## Multiplicities of K-types computed via characters

`K` carries the Haar probability measure `New.haarK ε`. `New.HCParam.kTypeChar ν` is the mean over
conjugation by `K` of `New.weightMinors ν`, divided by `New.HCParam.kTypeNormSq ν`.
-/

namespace New.Orbital

open Matrix MeasureTheory Finset ComplexConjugate DiscreteSeries InnerProductSpace GlModule
  Norms.L2Operator HCParam

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {A : ℕ} {l ν : HCParam (n := n) ε}

/-- For continuous `f`, the integral over `K` of `f` against `conj (kTypeChar ν)` is the mean over
`y ∈ K` of the integrals of `k ↦ f (y k y⁻¹)` against `conj (weightMinors ν)`, divided by
`kTypeNormSq ν`. -/
lemma integral_mul_conj_kTypeChar {f : maxCompactU ε → ℂ} (hf : Continuous f := by fun_prop) :
    ∫ k : maxCompactU ε, f k * conj (ν.kTypeChar k) ∂haarK ε =
      ∫ y : maxCompactU ε, (∫ k : maxCompactU ε,
        conj (weightMinors ν k.val) * f (y * k * y⁻¹) ∂haarK ε) / ν.kTypeNormSq ∂haarK ε := by
  -- Fubini, after the substitution `k ↦ y⁻¹ * k * y` in the inner integral.
  let F (y k : maxCompactU ε) : ℂ := f (y * k * y⁻¹) * conj (weightMinors ν k)
  have h_skew : ∫ k, ∫ y, F y (y⁻¹ * k * y) ∂haarK ε ∂haarK ε =
      ∫ y, ∫ k, F y k ∂haarK ε ∂haarK ε :=
    (integral_skew_product (f := F.uncurry)
      (fun y ↦ ((measurePreserving_mul_left _ y⁻¹).mul_right _ y).map_eq)
      (integrable_of_compactSpace (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero])))).2
  have h_integrand (k : maxCompactU ε) : f k * conj (ν.kTypeChar k) =
      (∫ y : maxCompactU ε, F y (y⁻¹ * k * y) ∂haarK ε) / ν.kTypeNormSq := by
    simp [F, kTypeChar, ← integral_conj, mul_div, mul_assoc, integral_const_mul]
  simp_rw [h_integrand, integral_div, h_skew, F, mul_comm]

/-- Orthogonality to the trivial character: `∫_K conj (kTypeChar ν)` is `1` for `ν = 0` and `0`
otherwise. -/
lemma integral_conj_kTypeChar :
    ∫ k : maxCompactU ε, 1 * conj (ν.kTypeChar k) ∂haarK ε = if ν = 0 then 1 else 0 := by
  refine .trans integral_mul_conj_kTypeChar ?_
  split_ifs with hν
  · simp [hν, kTypeNormSq, Pi.zero_def, GeneralLinearGroup.det_ne_zero]
  -- Left invariance under the torus gives `t ^ ν * I = I` for all `t`, which forces `I = 0`.
  let I : ℂ := ∫ k : maxCompactU ε, weightMinors ν k ∂haarK ε
  suffices hI : I = 0 by simp [integral_conj, I, hI]
  by_contra hI
  have h_eval (t : n → Circle) : torusEval t (.single ν I) = torusEval t (.single 0 I) := by
    simpa [torusEval, diagTorus, I, hI, GeneralLinearGroup.det_ne_zero, integral_const_mul] using
      integral_mul_left_eq_self (μ := haarK ε) (weightMinors ν ·) (diagTorusK t)
  exact hν (AddMonoidAlgebra.single_left_injective hI (eq_of_torusEval_eq h_eval))

/-- Let `l` have a large gap and let `ν` be `K`-dominant in the order of `-l`. For
`u = l.dsGenerator` and `ι = hg.toL2` the embedding of the discrete series module in `L²`, let
`φ w = ∫_K conj (weightMinors ν k) * ⟪ι u, rightRegularL2 x (rightRegularL2 k w)⟫`. For indices
`a`, `c` with `ε a = ε c` and `l c ≤ l a`, applying the matrix unit `E c a` to a vector `y` of the
module multiplies `φ (ι y)` by `ν c` if `c = a`, and by `0` otherwise. -/
lemma mean_coefficient_lowering [Nonempty n] [hg : l.HasLargeGap A] (hν : IsKDominant ε (-l) ν)
    {x : USign ε} {φ : (USign ε →₂[volume] ℂ) →L[ℂ] ℂ}
    (hφ : ∀ w : Lp ℂ 2 volume, φ w = ∫ k : maxCompactU ε, conj (weightMinors ν k) *
      ⟪hg.toL2 l.dsGenerator, rightRegularL2 x (rightRegularL2 k w)⟫_ℂ ∂haarK ε)
    (y : l.DsModule) {a c : n} (hε : ε a = ε c) (hl : l c ≤ l a) :
    φ (hg.toL2 (l.dsAction.E c a y)) = (if c = a then (ν c : ℂ) else 0) * φ (hg.toL2 y) := by
  -- Extend `j ↦ φ (rightRegularL2 j (ι y))` from `K` to a function `Φ` analytic at `1`, and
  -- differentiate it in two ways.
  have h_mem : Matrix.single c a 1 ∈ blockDiagAlg ε := mem_blockDiagAlg.2 fun i j hij ↦
    single_apply_of_ne (h := fun ⟨hi, hj⟩ ↦ hij (by rw [← hi, ← hj, hε])) ..
  let Φ (g : Matrix n n ℂ) : ℂ :=
    ∫ k : maxCompactU ε, weightMinors ν (g * k⁻¹) * y.val.val (x * k) ∂haarK ε
  have Φ_an : AnalyticAt ℂ Φ 1 := IsAnalyticFamily.analyticAt_integral _
    (.of_analyticAt (.prodMk (by fun_prop) (by fun_prop))
      (fun (g, p, q) ↦ weightMinors ν (g * p) * q)
      (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero])))
  have hΦ : HasFDerivAt Φ (fderiv ℂ Φ 1) 1 := Φ_an.differentiableAt.hasFDerivAt
  have Φ_K (j : maxCompactU ε) : φ (rightRegularL2 j (hg.toL2 y)) = Φ j := by
    refine .trans ?_ (integral_mul_right_eq_self _ j)
    simp [hφ, ← weightMinors_unitary_inv, -map_mul, hg.inner_toL2_dsGenerator_rightRegularL2,
      rep_apply_apply]
  -- Along the Lie algebra of `K`, hence on all of `blockDiagAlg ε`, the derivative is the action
  -- `l.dsAction`.
  have h_lie : fderiv ℂ Φ 1 (Matrix.single c a 1) = φ (hg.toL2 (l.dsAction.E c a y)) := by
    refine fderiv_eq_on_blockDiagAlg hΦ (φ.toLinearMap ∘ₗ hg.toL2 ∘ₗ l.dsAction.ρ.flip y)
      (fun Y hY ↦ ?_) h_mem
    simpa [Φ_K ⟨_, hY _⟩] using ((hg.isDerivedAction_toL2 Y y).map_clm φ).deriv
  -- On triangular `g ∈ blockDiagAlg ε`, `Φ g = diagChar ν g * Φ 1`, as `ν` is `K`-dominant.
  have h_equivariant : ∀ᶠ g : Matrix n n ℂ in nhds 1, ∀ b ∈ blockDiagAlg ε,
      IsBorelMatrix (- -l) b → g = id b → Φ g = diagChar ν b * Φ 1 := by
    simp +contextual [Φ, hν.weightMinors_oppBorel_mul hg.neg.injective,
      GeneralLinearGroup.det_ne_zero, mul_assoc, integral_const_mul]
  have h_tri : fderiv ℂ Φ 1 (Matrix.single c a 1) = (if c = a then (ν c : ℂ) else 0) * Φ 1 :=
    fderiv_eq_of_borel_equivariant ε hΦ (o := -l) (by simpa) hε.symm id h_equivariant fun _ ↦ rfl
  have Φ_one : φ (hg.toL2 y) = Φ 1 := by simpa using Φ_K 1
  rw [← h_lie, h_tri, Φ_one]

/-- Let `l = 2λ` have a large gap and let `ν` be `K`-dominant in the order of `-l`. Let `φ` be the
mean `w ↦ ∫_K conj (weightMinors ν k) * ⟪ι u, rightRegularL2 x (rightRegularL2 k w)⟫`, where
`weightMinors ν` is the product of principal minors of weight `ν`, `u = l.dsGenerator` is `c_λ` as
generator of the discrete series module `U(𝔤)c_λ`, and `ι = hg.toL2` (`f ↦ √deg_λ · f`) is its
embedding in `L²`. Let `s` bound the excess of the `K`-Casimir eigenvalue of `ν` over that of the
lowest `K`-type. Then some vector of weight `ν` in step `s` of the filtration (increasing
finite-dimensional subspaces, each stable under `E c a` for `ε a = ε c`), killed by the compact
raising operators, represents `y ↦ φ (ι y)` on every step. -/
lemma exists_isKHighest_inner_eq_mean_coefficient [Nonempty n] [hg : l.HasLargeGap A]
    (hν : IsKDominant ε (-l) ν) {s : ℕ}
    (hs : (l.casimirKValue ν - l.casimirKValue l.lowestKType : ℝ) ≤ s)
    {x : USign ε} {φ : (USign ε →₂[volume] ℂ) →L[ℂ] ℂ}
    (hφ : ∀ w : Lp ℂ 2 volume, φ w = ∫ k : maxCompactU ε, conj (weightMinors ν k) *
      ⟪hg.toL2 l.dsGenerator, rightRegularL2 x (rightRegularL2 k w)⟫_ℂ ∂haarK ε) :
    ∃ v ∈ l.dsAction.filtration ε l.dsGenerator s, l.IsKHighest l.dsAction ν v ∧
      ∀ t : ℕ, ∀ y ∈ l.dsAction.filtration ε l.dsGenerator t, φ (hg.toL2 y) = ⟪v, y⟫_ℂ := by
  let W : ℕ → Submodule ℂ l.DsModule := l.dsAction.filtration ε l.dsGenerator
  have h_high : l.IsKHighest l.dsAction l.lowestKType l.dsGenerator := isKHighest_dsGenerator hg
  have h_inv : IsUnitaryCasimirGe l l.dsAction := hg.isUnitaryCasimirGe
  have h_fin : ∀ t : ℕ, Module.Finite ℂ (W t) := h_high.finite_filtration h_inv
  -- `z t` represents the functional `φ ∘ ι` on the finite-dimensional space `W t`.
  let z (t : ℕ) : W t := ((φ.toLinearMap ∘ₗ hg.toL2).domRestrict (W t)).adjoint 1
  have hz {t t' : ℕ} {y : l.DsModule} (hy : y ∈ W t) (ht : t ≤ t') :
      ⟪(z t').val, y⟫_ℂ = φ (hg.toL2 y) :=
    (LinearMap.adjoint_inner_left _ (⟨y, filtration_mono ht hy⟩ : W t') 1).trans (by simp)
  -- By `mean_coefficient_lowering` and the invariance of the inner product, `z t` is `K`-highest of
  -- weight `ν`.
  have z_high (t : ℕ) : l.IsKHighest l.dsAction ν (z t).val := by
    refine .of_E_eq_smul fun a c hε hl ↦ Subtype.mk.inj (ext_inner_right ℂ (x := ⟨_,
      E_mem_filtration (z t).2 hε⟩) (y := (if a = c then (ν a : ℂ) else 0) • z t) fun y ↦ ?_)
    calc
      _ = φ (hg.toL2 (l.dsAction.E c a y.val)) := by
        simp [h_inv.inner_E_left a, hε, hz (E_mem_filtration y.2 hε.symm) le_rfl]
      _ = _ := by
        rw [mean_coefficient_lowering hν hφ y hε hl]
        simp +contextual [↓inner_smul_left, hz y.2 le_rfl, apply_ite conj, eq_comm (a := c)]
  -- Rigidity: `z (s ⊔ t) - z s` is an eigenvector of `casimirK` orthogonal to `W s`. Since
  -- `casimirK` grows along the filtration and `s` is large, it is orthogonal to `W t`.
  refine ⟨z s, (z s).prop, z_high s, fun t y hy ↦ ?_⟩
  have h_perp : (z (s ⊔ t)).val - z s ∈ (W t)ᗮ :=
    mem_orthogonal_filtration_of_casimirK (θ := l.casimirKValue ν) s h_inv h_high _
      (by simp [(z_high _).casimirK_eq_smul, smul_sub]) (sub_le_iff_le_add'.1 hs)
      (fun y' hy' ↦ inner_eq_zero_symm.mpr (by simp [hz hy', inner_sub_left])) t
  simpa [hz hy, sub_eq_zero, inner_sub_left] using congrArg conj (h_perp y hy)

/-- Let `n` be nonempty, let `l = 2λ` have a large gap (`hg : l.HasLargeGap A`), and let `ν` be
`K`-dominant in the order of `-l`. Let `s` bound the excess of the `K`-Casimir eigenvalue of `ν`
over that of the lowest `K`-type. Let `b` be an orthonormal basis of the space `V` of `K`-highest
vectors of weight `ν` in step `s` of the filtration (increasing finite-dimensional subspaces, each
stable under `E c a` for `ε a = ε c`) of the discrete series module `U(𝔤)c_λ` generated by
`dsGenerator = c_λ`; its elements are functions on the group, and `b i x` is the value at `x`. Then
the mean `∫_K conj (weightMinors ν k) * dsCoeff (x * k * x⁻¹)`, divided by
`ν.kTypeNormSq = ∫_K |weightMinors ν k|²`, is `∑ i, |b i x|²`. Here `dsCoeff` is `c_λ`,
`weightMinors ν` is the product of principal minors of weight `ν`, and `K` carries Haar measure of
mass one. -/
lemma mean_coefficient_eq_sum_norm_sq [Nonempty n] [hg : l.HasLargeGap A]
    (hν : IsKDominant ε (-l) ν) {s : ℕ}
    (hs : (l.casimirKValue ν - l.casimirKValue l.lowestKType : ℝ) ≤ s) {V : Submodule ℂ l.DsModule}
    (hV : ∀ v : DsModule (l := l),
      v ∈ V ↔ l.IsKHighest l.dsAction ν v ∧ v ∈ l.dsAction.filtration ε l.dsGenerator s)
    {I : Type*} [Fintype I] (b : OrthonormalBasis I ℂ V) (x : USign ε) :
    (ν.kTypeNormSq : ℂ)⁻¹ *
        ∫ k : maxCompactU ε, conj (weightMinors ν k) * l.dsCoeff (x * k.val * x⁻¹ :) ∂haarK ε =
      ∑ i : I, (b i).val.val.val x * conj ((b i).val.val.val x) := by
  -- With `u = l.dsGenerator` and `ι = hg.toL2`, put `φ w = ∫_K conj (weightMinors ν k) * ⟪ι u,
  -- rightRegularL2 x (rightRegularL2 k w)⟫`. A vector `v` of `V` represents `φ ∘ ι`; compare the
  -- two at the translate `rightRegularL2 x⁻¹ (ι u)`.
  have hd : IsDerivedAction rightRegularL2 hg.toL2 l.dsAction := hg.isDerivedAction_toL2
  have h_coef (y : l.DsModule) (g : USign ε) :
      ⟪hg.toL2 l.dsGenerator, rightRegularL2 g (hg.toL2 y)⟫_ℂ = y.val.val g :=
    hg.inner_toL2_dsGenerator_rightRegularL2 y g
  have h_cont : ∀ w : Lp ℂ 2 volume, Continuous fun g : USign ε ↦ rightRegularL2 g w :=
    (isUnitaryRep_rightRegularL2 (ε := ε)).continuous
  let T : (USign ε →₂[volume] ℂ) →L[ℂ] ℂ := innerSL ℂ (hg.toL2 l.dsGenerator) ∘L rightRegularL2 x
  let φ : (USign ε →₂[volume] ℂ) →L[ℂ] ℂ :=
    strongIntegral (haarK ε) fun k ↦ conj (weightMinors ν k) • T ∘L rightRegularL2 k
  have hφ (w : Lp ℂ 2 volume) : φ w = ∫ k : maxCompactU ε, conj (weightMinors ν k) *
      ⟪hg.toL2 l.dsGenerator, rightRegularL2 x (rightRegularL2 k w)⟫_ℂ ∂haarK ε :=
    strongIntegral_apply _ _ (fun _ ↦ by
      simpa using integrable_of_compactSpace
        (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero]))) w
  obtain ⟨v, v_mem, v_high, v_rep⟩ := exists_isKHighest_inner_eq_mean_coefficient hν hs hφ
  have norm_eq (g : USign ε) (y : l.DsModule) : ‖rightRegularL2 g (hg.toL2 y)‖ = ‖y‖ :=
    -- the norm of `y` is by definition that of `hg.toL2 y`
    show _ = ‖hg.toL2 y‖ by simp [rightRegularL2]
  -- `u` is an analytic vector: a bounded coefficient map that kills all steps of the filtration at
  -- `1` kills `u` at every group element. So `v` also represents `φ` at the translate of `u`.
  have h_rep : (φ - innerSL ℂ (hg.toL2 v)) (rightRegularL2 x⁻¹ (hg.toL2 l.dsGenerator)) = 0 :=
    (isKHighest_dsGenerator hg).coeffMap_eq_zero hg.isUnitaryCasimirGe
      (hd.isCoeffMap (φ - innerSL ℂ (hg.toL2 v)))
      (fun g y ↦ (φ - _).le_opNorm_of_le (norm_eq g y).le)
      (fun t y hy ↦ by simpa [sub_eq_zero] using! v_rep t y hy) x⁻¹
  -- Compute both terms; for the second expand `v` in the basis `b`.
  have φ_u : φ (rightRegularL2 x⁻¹ (hg.toL2 l.dsGenerator)) = ∫ k : maxCompactU ε,
      conj (weightMinors ν k) * l.dsCoeff (x * k.val * x⁻¹ :) ∂haarK ε := by
    simp [hφ, -map_mul, h_coef, rep_apply_apply, mul_assoc]
  -- The mean against `conj (weightMinors ν)` multiplies a highest vector of weight `ν` by
  -- `ν.kTypeNormSq`.
  have v_b (i : I) : ⟪v, (b i).val⟫_ℂ = ν.kTypeNormSq * (b i).val.val.val x := by
    obtain ⟨b_high, b_mem⟩ := (hV _).mp (b i).prop
    rw [← v_rep s _ b_mem, (hφ (hg.toL2 (b i))).trans
      (b_high.integral_conj_weightMinors_mul isUnitaryRep_rightRegularL2 hd hν T)]
    simp [T, h_coef]
  have b_u (i : I) : ⟪hg.toL2 (b i), rightRegularL2 x⁻¹ (hg.toL2 l.dsGenerator)⟫_ℂ =
      conj ((b i).val.val.val x) := by
    simpa [← h_coef] using isUnitaryRep_rightRegularL2.form_apply_eq_form_inv_apply x⁻¹
      (hg.toL2 (b i)) (hg.toL2 l.dsGenerator)
  have v_sum : hg.toL2 v = ∑ i : I, ⟪(b i).val, v⟫_ℂ • hg.toL2 (b i) := by
    simpa using (congrArg (fun w : V ↦ hg.toL2 w) (b.sum_repr' ⟨v, (hV v).2 ⟨v_high, v_mem⟩⟩)).symm
  simpa [φ_u, v_sum, v_b, b_u, ← mul_sum, sub_eq_zero, ← inv_mul_eq_iff_eq_mul₀, mul_assoc,
    ne_of_gt] using h_rep

/-- Let `n` be nonempty, let `l = 2λ` have a large gap (`New.HCParam.HasLargeGap` with constant `A`)
and let `ν` be `K`-dominant in the order of `-l`. Put `R g = ∫_K ψ(g⁻¹ k g) conj (kTypeChar ν k) dk`
with `ψ = New.HCParam.dsCoeff l` the discrete series coefficient and `kTypeChar ν` the character of
the `K`-type of highest weight `ν`. Then `R` is integrable over the group, and
`formalDegree l * ∫ R` is a natural number `m`, the multiplicity of that `K`-type: `m = 1` for the
lowest `K`-type `ν = lowestKType l`, and `m = 0` unless `ν - lowestKType l` lies in the cone
`rootCone l` of positive roots. Here `m` is the dimension of the space of `K`-highest vectors of
weight `ν` in a large step of the filtration of the discrete series; no formula for `m` is given. -/
lemma exists_kType_multiplicity [Nonempty n] [hg : l.HasLargeGap A] (hν : IsKDominant ε (-l) ν) :
    let R (g : USign ε) :=
      ∫ k : maxCompactU ε, l.dsCoeff (g⁻¹ * k * g :) * conj (ν.kTypeChar k) ∂haarK ε
    Integrable R ∧ ∃ m : ℕ, l.formalDegree * ∫ g : USign ε, R g = m ∧
      (ν = l.lowestKType → m = 1) ∧ (m ≠ 0 → ν - l.lowestKType ∈ l.rootCone) := by
  -- The multiplicity is the dimension of the space `V` of `K`-highest vectors of weight `ν` in a
  -- large step `s` of the filtration: integrate `key` over the group.
  obtain ⟨s, hs⟩ := exists_nat_ge (l.casimirKValue ν - l.casimirKValue l.lowestKType : ℝ)
  have h_fin := (isKHighest_dsGenerator hg).finite_filtration hg.isUnitaryCasimirGe s
  let V : Submodule ℂ l.DsModule :=
    .ofLinearComb {v | l.IsKHighest l.dsAction ν v} ⟨0, by simp [IsKHighest]⟩ (by simp +contextual
      [smul_smul, mul_comm, IsKHighest]) ⊓ l.dsAction.filtration ε l.dsGenerator s
  let b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V := stdOrthonormalBasis ℂ V
  let S (g : USign ε) : ℂ := ∑ i, (b i).val.val.val g * conj ((b i).val.val.val g)
  have key (x : USign ε) : (ν.kTypeNormSq : ℂ)⁻¹ * ∫ k : maxCompactU ε,
      conj (weightMinors ν k) * l.dsCoeff (x * k.val * x⁻¹ :) ∂haarK ε = S x :=
    mean_coefficient_eq_sum_norm_sq hν hs (fun _ ↦ .rfl) b x
  have h_int (y : l.DsModule) : Integrable fun g : USign ε ↦ y.val.val g * conj (y.val.val g) := by
    simpa [Pi.mul_def] using (hg.memLp y).integrable_mul (hg.memLp y).star
  have b_norm (i : Fin (Module.finrank ℂ V)) : ‖hg.toL2 (b i)‖ = 1 := b.norm_eq_one i
  have b_int (i : Fin (Module.finrank ℂ V)) :
      l.formalDegree * ∫ g : USign ε, (b i).val.val.val g * conj ((b i).val.val.val g) = 1 := by
    simpa [b_norm] using (hg.inner_toL2_rightRegularL2 (b i) (b i) 1).symm
  have h_dim : (Module.finrank ℂ V : ℂ) = l.formalDegree * ∫ g : USign ε, S g := by
    simp [S, integral_finsetSum, h_int, mul_sum, b_int]
  intro R
  -- `ν.kTypeChar` is the mean of `weightMinors ν / ν.kTypeNormSq` under conjugation by `y ∈ K`;
  -- this mean is absorbed by the invariance of the measure under `g ↦ g⁻¹ * y`.
  have hR : R = fun g ↦ ∫ y : maxCompactU ε, S (g⁻¹ * y) ∂haarK ε :=
    funext fun g ↦ .trans integral_mul_conj_kTypeChar (by simp [← key, div_eq_inv_mul, mul_assoc])
  have S_int : Integrable S := integrable_finsetSum univ fun i _ ↦ h_int (b i)
  obtain ⟨R_int, R_eq⟩ := integral_skew_product
    (fun y : maxCompactU ε ↦ ((Measure.measurePreserving_inv _).mul_right _ y.val).map_eq)
    (S_int.comp_snd (haarK ε))
  refine ⟨by rwa [hR], Module.finrank ℂ V, by simp [hR, h_dim, R_eq], ?_, fun hm ↦ ?_⟩
  · -- For `ν = l.lowestKType` the left side of `key` is `|dsCoeff x|²`, of integral
    -- `1 / l.formalDegree`.
    rintro rfl
    have hS (x : USign ε) : S x = l.dsCoeff x * conj (l.dsCoeff x) := by
      rw [← key, integral_conj_weightMinors_lowestKType_mul_dsCoeff hg x x⁻¹]
      simp [↓dsCoeff_inv, ne_of_gt]
    exact Nat.cast_eq_one.1 (h_dim.trans (by simpa [hS] using dsCoeff_schur_orthogonality hg 1 1))
  · -- Off the cone the left side of `key` vanishes.
    by_contra h_cone
    have hS (x : USign ε) : S x = 0 := by
      rw [← key, integral_conj_weightMinors_mul_dsCoeff_eq_zero hg x x⁻¹ hν h_cone, mul_zero]
    exact hm (by simpa [hS] using h_dim)

end New.Orbital

/-!
## Orbital integrals times root products as Laurent polynomials

The idea: let D be a power of the product of `x_a - x_b` over `ε a ≠ ε b`, `l a < l b`. Then D Θ
converges and extends to a continuous class function on K. Its coefficients against the characters
of K are integers (`New.Orbital.exists_kType_multiplicity`) and square-summable, so only finitely
many are not zero.

Conventions: `ℂ[n → ℤ]` is the ring of Laurent polynomials, `P.coeff` the coefficient function,
`New.Orbital.torusEval x` evaluation at a point of the torus. `New.HCParam.rootProd l r` is the
product of `x_a - x_b` over the pairs with `r (ε a) (ε b)`, `l b < l a`. `New.Orbital.alternant ε μ`
is the alternant ∑ sgn(w) x^(μ ∘ w) over the permutations w that preserve `ε`; for injective `l`,
δ = `l.lowerCount Eq` is the exponent whose alternant is the Weyl denominator `l.rootProd Eq`.
-/

section OrbitalLaurent

open Matrix MeasureTheory Finset AddMonoidAlgebra Equiv ConjAct InnerProductSpace ContinuousMap
  CStarRing Norms.L2Operator Fintype Metric Int

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} (l : New.HCParam ε)

/-- `P` is `D` times a formal series `t` with `t a = 1`, each of whose exponents occurs in the
alternant `New.Orbital.alternant ε μ` for some `μ` such that `μ - a` lies in the cone of positive
roots `New.HCParam.rootCone l`. -/
def New.Orbital.IsConeSeriesMultiple (a : n → ℤ) (D P : ℂ[n → ℤ]) : Prop :=
  ∃ t : (n → ℤ) → ℂ,
    (∀ γ : n → ℤ, P.coeff γ = D.coeff.sum fun (β : n → ℤ) (c : ℂ) ↦ c * t (-β + γ)) ∧
    t a = 1 ∧
    ∀ γ : n → ℤ, t γ ≠ 0 → ∃ μ : n → ℤ, (alternant ε μ).coeff γ ≠ 0 ∧ μ - a ∈ l.rootCone

/-- Let `n` be nonempty, `u` in `U(diag ε)` and `t` a point of the torus, and put `g = u⁻¹ t u`.
For the operator norms `(‖u‖ / 2)² |∏ (t_a - t_b)| ≤ (2 ‖g‖)^m`, the product being over the
`m` pairs in `oppositePairs ε`, those with `ε a = 1 ≠ ε b`. -/
lemma New.Orbital.sq_norm_mul_norm_prod_sub_le [Nonempty n] (u : USign ε) (t : n → Circle) :
    (‖u.val.val‖ / 2) ^ 2 * ‖∏ p ∈ oppositePairs ε, (t p.1 - t p.2 : ℂ)‖ ≤
      (2 * ‖(u⁻¹ * diagTorus ε t * u).val.val‖) ^ #(oppositePairs ε) := by
  -- Bound both sides against the principal minor on the signs + of ∏ (g - t_i) over ε i ≠ 1.
  set g : USign ε := u⁻¹ * diagTorus ε t * u
  -- `φ v = u⁻¹ diag(v) u`, so `φ t = g`
  let φ : (n → ℂ) →ₐ[ℂ] Matrix n n ℂ :=
    (MulSemiringAction.toAlgHom ℂ (Matrix n n ℂ) (toConjAct u.val⁻¹)).comp (diagonalAlgHom ℂ)
  have φ_eq (v : n → ℂ) : φ v = u⁻¹.val.val * diagonal v * u.val.val := rfl
  have norm_prod (s : Finset n) :
      ‖φ (∏ i ∈ s, ((t · : n → ℂ) - (t i).val • 1))‖ ≤ (‖g.val.val‖ + ‖g.val.val‖) ^ #s := by
    induction s using cons_induction with
    | empty => simp
    | cons i s hi ih => simp [ih, hi, show φ (t ·) = g.val.val from rfl, pow_succ', norm_smul,
        norm_mul_le_of_le, norm_sub_le_of_le, U.one_le_norm, Circle.norm_coe]
  calc
    _ ≤ ‖principalMinor (φ (∏ i with ε i ≠ 1, ((t · : n → ℂ) - (t i).val • 1))) (ε · = 1)‖ := by
      -- The matrix is u⁻¹ T u with T diagonal and zero on the signs -, so the minor factors. The
      -- minors of u and u⁻¹ are conjugate, with product of modulus at least (‖u‖ / 2)².
      grw [sq_le_norm_det_blockDiagPart, norm_det_blockDiagPart 1, φ_eq, principalMinor_mul,
        principalMinor_mul, U.principalMinor_coe_inv]
      · -- the minor of T is the product of the t_a - t_b
        simp [principalMinor_eq_det (x := diagonal _), oppositePairs, prod_product,
          ← diagonal_one, sub_ite, sq, mul_right_comm, prod_ite]
      · -- T is diagonal
        exact fun _ j k _ hj hk ↦ .inr (diagonal_apply_ne _ (by grind))
      · -- the columns of u⁻¹ T of sign - vanish
        exact fun _ j _ _ hj ↦ by simp [prod_eq_zero (i := j), hj]
    _ ≤ (2 * ‖g.val.val‖) ^ #(oppositePairs ε) := by
      -- a minor of size p of a product of q matrices of norm at most 2 ‖g‖
      grw [norm_principalMinor_le_pow, Fintype.card_subtype, norm_prod, ← two_mul, ← pow_mul]
      simp [oppositePairs, mul_comm]

/-- Let `n` be nonempty, let `l = 2λ` have a large gap for `A = 10 (card n)⁵`, and let
`K = U(diag ε) ∩ U(n)`. Let `d` be a continuous class function on `K` whose value at `diag(x)` is
`D(x)^N`, with `N = 4 (card n)² + 1` and `D(x) = ((-l).rootProd Ne)(x) = ∏ (x_a - x_b)` over the
pairs with `ε a ≠ ε b` and `l a < l b` (the noncompact roots positive for `-l`). Let
`ψ g k = l.dsCoeff (g⁻¹ k g)`, where `l.dsCoeff` is the function `c_λ`. Then `g ↦ d * ψ g` on
`U(diag ε)`, with values in the continuous functions on `K` with the supremum norm, is integrable.
In particular the orbital integral of `l.dsCoeff` converges absolutely at each point of the torus
with distinct entries, where `d` is not zero. -/
lemma New.Orbital.integrable_mul_dsCoeff_conj [Nonempty n] (hg : l.HasLargeGap (10 * card n ^ 5))
    {d : C(maxCompactU ε, ℂ)} (hd : ∀ (y : maxCompactU ε) (x : n → Circle),
      d (y * diagTorusK x * y⁻¹) = torusEval x ((-l).rootProd Ne ^ (4 * card n ^ 2 + 1)))
    {ψ : C(USign ε, C(maxCompactU ε, ℂ))}
    (hψ : ∀ (g : USign ε) (k : maxCompactU ε), ψ g k = l.dsCoeff (g⁻¹ * k * g :)) :
    Integrable fun g : USign ε ↦ d * ψ g := by
  -- |d(k) l.dsCoeff(x⁻¹ k x)| ≤ 4^(mN) (2 / ‖x‖)^(2N), m = `#(oppositePairs ε)`, integrable as
  -- 2N > 8 (card n)² (`integral_decay_le`). The bound combines `sq_norm_mul_norm_prod_sub_le` with
  -- the decay |l.dsCoeff g| ≤ (2 / ‖g‖)^(mN) of `norm_dsCoeff_le_pow`.
  set N : ℕ := 4 * card n ^ 2 + 1
  refine ((DiscreteSeries.integral_decay_le _ .monoidHom_id (c := 2 * N) (by omega) 1).1.const_mul
    (2 ^ (#(oppositePairs ε) * N * 2))).mono' (by fun_prop)
    (.of_forall fun x ↦ (norm_le_of_nonempty _).2 fun k ↦ ?_)
  obtain ⟨y, t, rfl⟩ := exists_conj_diagTorusK k
  let u : USign ε := y⁻¹ * x
  let g : USign ε := u⁻¹ * diagTorus ε t * u
  have gap : #(oppositePairs ε) * N ≤ gapThreshold n (10 * card n ^ 5) := by
    grw [card_le_univ]
    simp only [N, gapThreshold, Fintype.card_prod]
    have card_pow (k : ℕ) : 1 ≤ card n ^ k := Nat.one_le_pow k _ Fintype.card_pos
    nlinarith [card_pow 1, card_pow 2, card_pow 3, card_pow 4]
  have minor : ‖∏ p ∈ oppositePairs ε, (t p.1 - t p.2 : ℂ)‖ ≤
      (2 * ‖g.val.val‖) ^ #(oppositePairs ε) / (‖u.val.val‖ / 2) ^ 2 :=
    (le_div_iff₀' (by simp)).2 (sq_norm_mul_norm_prod_sub_le u t)
  have norm_u : ‖u.val.val‖ = ‖x.val.val‖ := by
    simp [u, norm_mem_unitary_mul, Unitary.mem_iff, star, ← maxCompactU.coe_inv,
      conjTranspose_nonsing_inv]
  have g_eq : x.val.val⁻¹ * (y.val.val.val * (diagTorus ε t).val.val * y.val.val.val⁻¹) *
      x.val.val = g.val.val := by simp [g, u, mul_assoc]
  suffices key : ‖∏ p ∈ oppositePairs ε, (t p.1 - t p.2 : ℂ)‖ ^ N * ‖l.dsCoeff g.val.val‖ ≤
      ((2 ^ #(oppositePairs ε)) ^ N) ^ 2 * ((2 / ‖x.val.val‖) ^ 2) ^ N by
    simpa [g_eq, hd, hψ, pow_mul, torusEval_rootProd_noncompact hg.neg.injective, -norm_prod,
      prod_ite] using key
  calc
    _ ≤ ((2 * ‖g.val.val‖) ^ #(oppositePairs ε) / (‖u.val.val‖ / 2) ^ 2) ^ N *
        (2 / ‖g.val.val‖) ^ (#(oppositePairs ε) * N) := by
      grw [minor, DiscreteSeries.norm_dsCoeff_le_pow hg gap]
    _ = _ := by simp [norm_u, div_pow, field, mul_pow, ← pow_mul, mul_comm]

/-- If all coefficients of a vector against an orthonormal family are integers, only finitely many
are not zero: they tend to zero by Bessel's inequality. -/
lemma New.Orbital.finite_support_inner_of_int {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {v : ι → H} (hv : Orthonormal ℂ v) {x : H}
    (h_int : ∀ i : ι, ∃ z : ℤ, ⟪v i, x⟫_ℂ = z) :
    (Function.support fun i : ι ↦ ⟪v i, x⟫_ℂ).Finite := by
  have h_large : {i : ι | ¬‖⟪v i, x⟫_ℂ‖ ^ 2 < 1}.Finite :=
    (hv.inner_products_summable x).tendsto_cofinite_zero.eventually_lt_const one_pos
  refine h_large.subset fun i ↦ ?_
  obtain ⟨z, hz⟩ := h_int i
  simpa [hz] using mod_cast one_le_abs (z := z)

/-- The character `kTypeChar ν`, being a mean over conjugates, is a class function on K. -/
lemma New.Orbital.kTypeChar_mul_mul_inv (ν : n → ℤ) (y k : maxCompactU ε) :
    (toHCParam ε ν).kTypeChar (y * k * y⁻¹) = (toHCParam ε ν).kTypeChar k := by
  -- substitute `a ↦ y * a` in the mean over `a ∈ K` of `weightMinors ν (a⁻¹ * (y * k * y⁻¹) * a)`
  refine congrArg (fun I : ℂ ↦ I / _) ?_
  rw [← integral_mul_left_eq_self _ y]
  simp [mul_assoc]

/-- Weyl's formula for any exponent γ, for injective `l`. Let ν be dominant for K and let
δ = `l.lowerCount Eq`. If every function `t` antisymmetric under the Weyl group of K has
`t γ = s * t (ν + δ)`, then `s` times the character of ν is a Laurent polynomial `P` on the torus,
and the Weyl denominator `l.rootProd Eq` times `P` is the alternant of γ. -/
lemma New.Orbital.exists_alternant_eq_rootProd_mul {γ ν : n → ℤ} {s : ℤ} (hl : l.Injective)
    (hν : IsKDominant ε (-l) ν)
    (hs : ∀ t : (n → ℤ) → ℂ, IsWeylAntisymm ε t → t γ = s * t (ν + l.lowerCount Eq)) :
    ∃ P : ℂ[n → ℤ], (∀ (y : maxCompactU ε) (x : n → Circle),
        s * (toHCParam ε ν).kTypeChar (y * diagTorusK x * y⁻¹) = torusEval x P) ∧
      alternant ε γ = l.rootProd Eq * P := by
  obtain ⟨⟨P, hP⟩, formula⟩ := weyl_character_kTypeChar hl hν
  refine ⟨s * P, fun y x ↦ by simp [kTypeChar_mul_mul_inv, ← hP], eq_of_torusEval_eq fun x ↦ ?_⟩
  -- `γ ↦ torusEval x (alternant ε γ)` is antisymmetric, being a determinant
  have antisymm : IsWeylAntisymm ε fun γ ↦ torusEval x (alternant ε γ) := by
    simp +contextual [IsWeylAntisymm, torusEval_alternant, ← det_permute', submatrix, funext_iff]
  simp [hs _ antisymm, ← formula, hP, field]

/-- Let `h` be a continuous class function on K, and suppose that for each Laurent polynomial the
set `S` contains a class function equal on the torus to the mean of the polynomial over the Weyl
group W of K (the permutations that preserve `ε`). Then `h` is a uniform limit of functions
from `S`. -/
lemma New.Orbital.mem_closure_of_conj_eq {h : C(maxCompactU ε, ℂ)} {S : Set C(maxCompactU ε, ℂ)}
    (h_class : ∀ (y : maxCompactU ε) (x : n → Circle),
      h (y * diagTorusK x * y⁻¹) = h (diagTorusK x))
    (hS : ∀ p : ℂ[n → ℤ], ∃ f ∈ S, ∀ (y : maxCompactU ε) (x : n → Circle),
      f (y * diagTorusK x * y⁻¹) = ∑ w : {w : Perm n // ε ∘ w = ε},
        (card {w : Perm n // ε ∘ w = ε} : ℝ)⁻¹ • torusEval (x ∘ w.val) p) :
    h ∈ closure S := by
  refine Metric.mem_closure_iff.mpr fun r hr ↦ ?_
  -- Approximate `h` on the torus by a Laurent polynomial (Weierstrass), then average over W.
  obtain ⟨p, hp⟩ := denseRange_torusEval.exists_dist_lt (h.comp (mk diagTorusK)) hr
  obtain ⟨f, hfS, hf⟩ := hS p
  refine ⟨f, hfS, (dist_lt_iff hr).mpr fun k ↦ ?_⟩
  obtain ⟨y, x, rfl⟩ := exists_conj_diagTorusK k
  have : Nonempty {w : Perm n // ε ∘ w = ε} := ⟨1, rfl⟩
  -- `h` is constant on the W-orbit of x, so each value of p there is close to `h (diagTorusK x)`.
  have h_close (w : {w : Perm n // ε ∘ w = ε}) :
      torusEval (x ∘ w.val) p ∈ ball (h (diagTorusK x)) r := by
    rw [mem_ball', ← apply_comp_perm_of_conj_invariant _ w.prop h_class]
    exact (dist_lt_iff hr).mp hp (x ∘ w.val)
  -- The ball is convex, so it contains the mean of these values.
  rw [hf, h_class, dist_comm]
  exact (convex_ball _ r).sum_mem (by simp) (by simp) fun w _ ↦ h_close w

/-- Weyl's formula for a family of class functions: `X γ` is a class function on K that equals the
Laurent polynomial `Y γ` on the torus, and the Weyl denominator `l.rootProd Eq` times `Y γ` is
the alternant of γ. -/
structure New.Orbital.IsWeylFamily (X : (n → ℤ) → C(maxCompactU ε, ℂ))
    (Y : (n → ℤ) → ℂ[n → ℤ]) : Prop where
  /-- `X γ` is a class function with restriction `Y γ` to the torus. -/
  apply_conj (γ : n → ℤ) (y : maxCompactU ε) (x : n → Circle) :
    X γ (y * diagTorusK x * y⁻¹) = torusEval x (Y γ)
  /-- The alternant of γ is the Weyl denominator times `Y γ`. -/
  alternant_eq (γ : n → ℤ) : alternant ε γ = l.rootProd Eq * Y γ

namespace New.Orbital.IsWeylFamily

variable {l : New.HCParam ε} {X : (n → ℤ) → C(maxCompactU ε, ℂ)} {Y : (n → ℤ) → ℂ[n → ℤ]}

/-- Let `X`, `Y` satisfy Weyl's formula (`IsWeylFamily`). Replacing each monomial `x ^ γ` of `p`
by `Y γ` and multiplying by the Weyl denominator antisymmetrises `p` over the Weyl group
of K. -/
lemma torusEval_rootProd_mul (hXY : IsWeylFamily l X Y) (p : ℂ[n → ℤ]) (x : n → Circle) :
    torusEval x (l.rootProd Eq * Finsupp.linearCombination ℂ Y p.coeff) =
      ∑ w : {w : Perm n // ε ∘ w = ε}, w.val.sign * torusEval (x ∘ w.val) p := by
  have alternant_eval (γ : n → ℤ) : torusEval x (alternant ε γ) =
      ∑ w : {w : Perm n // ε ∘ w = ε}, (w.val.sign : ℂ) * ∏ i, (x (w.val i) : ℂ) ^ γ i := by
    rw [← sum_subtype {w : Perm n | ε ∘ w = ε} (by simp)
      (fun w ↦ (w.sign : ℂ) * ∏ i, (x (w i) : ℂ) ^ γ i)]
    simp [torusEval_alternant, det_apply', Fintype.prod_ite_zero, ← sum_filter, funext_iff]
  calc
    _ = ∑ γ ∈ p.coeff.support, p.coeff γ * torusEval x (alternant ε γ) := by
      simp [Finsupp.linearCombination_apply, hXY.alternant_eq, Finsupp.sum, mul_sum]
    _ = _ := by
      simp_rw [alternant_eval, mul_sum]
      rw [sum_comm]
      simp [torusEval, lift_apply', Finsupp.sum, mul_sum, mul_left_comm]

/-- Let `X`, `Y` satisfy Weyl's formula and let `l` be injective. If the antisymmetrisation of
`p` over the Weyl group of K is the Weyl denominator times `q` on the torus, then the combination
of the `X γ` with the coefficients of `p` is `q` on the torus. -/
lemma linearCombination_apply_conj (hXY : IsWeylFamily l X Y) (hl : l.Injective) {p q : ℂ[n → ℤ]}
    (hpq : ∀ x : n → Circle, ∑ w : {w : Perm n // ε ∘ w = ε}, w.val.sign * torusEval (x ∘ w.val) p =
      torusEval x (l.rootProd Eq * q))
    (y : maxCompactU ε) (x : n → Circle) :
    Finsupp.linearCombination ℂ X p.coeff (y * diagTorusK x * y⁻¹) = torusEval x q := by
  have zero_dominant : IsKDominant ε (-l) 0 := fun _ _ _ _ ↦ le_rfl
  have denominator_ne : l.rootProd Eq ≠ 0 := fun h_zero ↦ by
    simpa [hXY.alternant_eq, h_zero] using
      alternant_coeff_of_isKDominant hl zero_dominant zero_dominant
  have q_eq : Finsupp.linearCombination ℂ Y p.coeff = q := mul_left_cancel₀ denominator_ne <|
    eq_of_torusEval_eq fun x ↦ (hXY.torusEval_rootProd_mul p x).trans (hpq x)
  simp [Finsupp.linearCombination_apply, hXY.apply_conj, ← q_eq, Finsupp.sum]

/-- Let `X`, `Y` satisfy Weyl's formula and let `l` be injective. The combination of the `X γ`
with the coefficients of `l.rootProd Eq * p` is, on the torus, the symmetrisation of `p` over the
Weyl group of K, because the Weyl denominator is antisymmetric. -/
lemma linearCombination_rootProd_mul_apply_conj (hXY : IsWeylFamily l X Y) (hl : l.Injective)
    (p : ℂ[n → ℤ]) (y : maxCompactU ε) (x : n → Circle) :
    Finsupp.linearCombination ℂ X (l.rootProd Eq * p).coeff (y * diagTorusK x * y⁻¹) =
      ∑ w : {w : Perm n // ε ∘ w = ε}, torusEval (x ∘ w.val) p := by
  simp_rw [torusEval_comp_perm, ← map_sum]
  refine hXY.linearCombination_apply_conj hl (fun x ↦ ?_) y x
  have denominator_comp (w : {w : Perm n // ε ∘ w = ε}) :
      torusEval (x ∘ w.val) (alternant ε (l.lowerCount Eq)) =
        w.val.sign * torusEval x (alternant ε (l.lowerCount Eq)) :=
    (torusEval_comp_eq_mul_iff _).2 (isWeylAntisymm_alternant _ w.2) x
  simp [weyl_denominator hl, ← torusEval_comp_perm, ← mul_assoc, ← cast_mul, denominator_comp,
    mul_sum]

/-- Let `X`, `Y` satisfy Weyl's formula and let `l` be injective. A Laurent polynomial `D` that
is symmetric under the Weyl group of K extends from the torus to a continuous class function
on K. -/
lemma exists_apply_conj_eq (hXY : IsWeylFamily l X Y) (hl : l.Injective) {D : ℂ[n → ℤ]}
    (hD : ∀ w : Perm n, ε ∘ w = ε → ∀ x : n → Circle, torusEval (x ∘ w) D = torusEval x D) :
    ∃ d : C(maxCompactU ε, ℂ), ∀ (y : maxCompactU ε) (x : n → Circle),
      d (y * diagTorusK x * y⁻¹) = torusEval x D := by
  let W : Type := {w : Perm n // ε ∘ w = ε}
  have : Nonempty W := ⟨1, rfl⟩
  refine ⟨Finsupp.linearCombination ℂ X (l.rootProd Eq * (card W : ℂ)⁻¹ • D).coeff, fun y x ↦ ?_⟩
  simp [W, hXY.linearCombination_rootProd_mul_apply_conj hl, fun w : W ↦ hD w.val w.2 x]

/-- Brauer's rule. Let `l` be injective, and let `X`, `Y` be a Weyl family for `l`: each `X γ` is a
continuous class function on K = U(diag ε) ∩ U(n) that equals the Laurent polynomial `Y γ` on the
diagonal torus, and the Weyl denominator of `l` times `Y γ` is the alternant of `γ`. If a continuous
`d` on K satisfies `d (y diag(x) y⁻¹) = D(x)` for a Laurent polynomial `D = ∑ a_β x ^ β`, then
`⟪X γ, d f⟫ = ∑ a_β ⟪X (-β + γ), f⟫` in L²(K) for the Haar measure of mass one. -/
lemma inner_toLp_mul (hXY : IsWeylFamily l X Y) (hl : l.Injective) {d : C(maxCompactU ε, ℂ)}
    {D : ℂ[n → ℤ]}
    (hd : ∀ (y : maxCompactU ε) (x : n → Circle), d (y * diagTorusK x * y⁻¹) = torusEval x D)
    (γ : n → ℤ) (f : C(maxCompactU ε, ℂ)) :
    ⟪toLp (E := ℂ) 2 (haarK ε) ℂ (X γ), toLp (E := ℂ) 2 (haarK ε) ℂ (d * f)⟫_ℂ =
      D.coeff.sum fun (β : n → ℤ) (a : ℂ) ↦
        a * ⟪toLp (E := ℂ) 2 (haarK ε) ℂ (X (-β + γ)), toLp (E := ℂ) 2 (haarK ε) ℂ f⟫_ℂ := by
  -- `S` is the conjugate of `D` on the torus, and `conj d * X γ` is the combination of the `X β`
  -- with the coefficients of `S * x ^ γ`.
  let S : ℂ[n → ℤ] := D.coeff.sum fun β a ↦ .single (-β) (star a)
  have hS (x : n → Circle) : torusEval x S = star (torusEval x D) := by
    simp [S, torusEval, lift_apply' _ D, ← Circle.coe_inv_eq_conj, Finsupp.sum]
  have alternant_sum (x : n → Circle) : torusEval x (l.rootProd Eq * Y γ) =
      ∑ w : {w : Perm n // ε ∘ w = ε}, w.val.sign * torusEval (x ∘ w.val) (.single γ 1) := by
    simpa using hXY.torusEval_rootProd_mul (.single γ 1) x
  have S_apply (y : maxCompactU ε) (x : n → Circle) :
      Finsupp.linearCombination ℂ X (S * .single γ 1).coeff (y * diagTorusK x * y⁻¹) =
        torusEval x (S * Y γ) := by
    refine hXY.linearCombination_apply_conj hl (fun x ↦ ?_) y x
    rw [mul_left_comm, map_mul _ S, alternant_sum, mul_sum]
    exact sum_congr rfl fun w _ ↦ by
      simp [hS, apply_comp_perm_of_conj_invariant _ w.2 hd, mul_left_comm]
  calc
    _ = ⟪toLp (E := ℂ) 2 (haarK ε) ℂ (Finsupp.linearCombination ℂ X (S * .single γ 1).coeff),
          toLp (E := ℂ) 2 (haarK ε) ℂ f⟫_ℂ := by
      simp_rw [inner_toLp]
      congr with k
      obtain ⟨y, x, rfl⟩ := exists_conj_diagTorusK k
      rw [S_apply, ContinuousMap.mul_apply, hd, hXY.apply_conj]
      simp [hS, mul_left_comm, mul_assoc]
    _ = _ := by simp [S, sum_mul, sum_inner, Finsupp.sum, inner_smul_left]

/-- Completeness. Let `X`, `Y` satisfy Weyl's formula, let `l` be injective and let `e` be an
orthonormal family in L²(K) whose span contains every `X γ`. A continuous class function with
finitely many coefficients `a i` against `e` is `∑ a i • e i`. -/
lemma eq_linearCombination (hXY : IsWeylFamily l X Y) (hl : l.Injective) {ι : Type*}
    {e : ι → C(maxCompactU ε, ℂ)} (he : Orthonormal ℂ (toLp (E := ℂ) 2 (haarK ε) ℂ ∘ e))
    (hX : ∀ γ : n → ℤ, X γ ∈ Submodule.span ℂ (Set.range e)) {h : C(maxCompactU ε, ℂ)}
    (h_class : ∀ (y : maxCompactU ε) (x : n → Circle),
      h (y * diagTorusK x * y⁻¹) = h (diagTorusK x)) {a : ι →₀ ℂ}
    (ha : ∀ i : ι, a i = ⟪toLp (E := ℂ) 2 (haarK ε) ℂ (e i), toLp (E := ℂ) 2 (haarK ε) ℂ h⟫_ℂ) :
    h = Finsupp.linearCombination ℂ e a := by
  -- The inner product `A` with r = h - ∑ a_i e_i kills every `X γ`, hence `h`, which is a uniform
  -- limit of combinations of the `X γ` (Weierstrass on the torus); so r = 0.
  let L : C(maxCompactU ε, ℂ) →L[ℂ] Lp ℂ 2 (haarK ε) := toLp 2 (haarK ε) ℂ
  let r : C(maxCompactU ε, ℂ) := h - Finsupp.linearCombination ℂ e a
  let A : C(maxCompactU ε, ℂ) →L⋆[ℂ] ℂ := innerSLFlip ℂ (L r) ∘SL L
  have A_e (i : ι) : A (e i) = 0 := by
    have inner_sum_eq : ⟪L (e i), L (Finsupp.linearCombination ℂ e a)⟫_ℂ = a i := by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum] using he.inner_right_finsupp a i
    change ⟪L (e i), L r⟫_ℂ = 0
    rw [map_sub, inner_sub_right, inner_sum_eq, ha, sub_self]
  have A_X (γ : n → ℤ) : X γ ∈ A.ker := Submodule.span_le.2 (Set.range_subset_iff.2 A_e) (hX γ)
  have h_mem : h ∈ A.ker := by
    refine A.isClosed_ker.closure_subset (mem_closure_of_conj_eq h_class fun p ↦ ?_)
    -- the combination of the `X γ` that is the mean of p over W on the torus
    let q : ℂ[n → ℤ] := l.rootProd Eq * (card {w : Perm n // ε ∘ w = ε} : ℝ)⁻¹ • p
    refine ⟨Finsupp.linearCombination ℂ X q.coeff, ?_, fun y x ↦ ?_⟩
    · rw [Finsupp.linearCombination_apply]
      exact A.ker.sum_mem fun γ _ ↦ A.ker.smul_mem _ (A_X γ)
    · simp only [q, hXY.linearCombination_rootProd_mul_apply_conj hl, AlgHom.map_smul_of_tower]
  have A_r : A r = 0 := sub_mem h_mem (by simp [Finsupp.linearCombination_apply, A_e, Finsupp.sum])
  have L_r : L r = 0 := inner_self_eq_zero.1 A_r
  exact sub_eq_zero.1 ((map_eq_zero_iff L (toLp_injective _)).1 L_r)

/-- Let `X`, `Y` satisfy Weyl's formula. On the torus, a combination of alternants is the Weyl
denominator times the same combination of the class functions `X γ`. -/
lemma torusEval_linearCombination_alternant (hXY : IsWeylFamily l X Y) {ι : Type*}
    (μ : ι → n → ℤ) (a : ι →₀ ℂ) (y : maxCompactU ε) (x : n → Circle) :
    torusEval x (Finsupp.linearCombination ℂ (fun i : ι ↦ alternant ε (μ i)) a) =
      torusEval x (l.rootProd Eq) *
        Finsupp.linearCombination ℂ (fun i : ι ↦ X (μ i)) a (y * diagTorusK x * y⁻¹) := by
  simp [Finsupp.linearCombination_apply, hXY.alternant_eq, hXY.apply_conj, mul_left_comm,
    Finsupp.sum, mul_sum]

end New.Orbital.IsWeylFamily

/-- Straightening of exponents: every function `t` antisymmetric under the Weyl group of K has
`t γ = s γ * t (ν γ + δ)` with `ν γ` dominant, where δ = `l.lowerCount Eq`. -/
structure New.Orbital.IsStraightening (s : (n → ℤ) → ℤ) (ν : (n → ℤ) → n → ℤ) : Prop where
  /-- `ν γ` is dominant for K, so it is the highest weight of a K-type. -/
  isKDominant (γ : n → ℤ) : IsKDominant ε (-l) (ν γ)
  /-- The value of an antisymmetric function at γ is `s γ` times its value at `ν γ + δ`. -/
  apply_eq (γ : n → ℤ) (t : (n → ℤ) → ℂ) (ht : IsWeylAntisymm ε t) :
    t γ = s γ * t (ν γ + l.lowerCount Eq)

/-- The virtual character of K attached to the exponent γ: `s γ` times `kTypeChar (ν γ)`, which
is the character of the K-type with highest weight `ν γ` when this weight is dominant. -/
noncomputable def New.Orbital.virtualChar (ε : n → ℤˣ) (s : (n → ℤ) → ℤ) (ν : (n → ℤ) → n → ℤ)
    (γ : n → ℤ) : C(maxCompactU ε, ℂ) :=
  (s γ : ℂ) • (toHCParam ε (ν γ)).kTypeChar

namespace New.Orbital.IsStraightening

variable {l : New.HCParam ε} {s : (n → ℤ) → ℤ} {ν : (n → ℤ) → n → ℤ}

/-- For a straightening `s`, `ν`, injective `l` and dominant μ, the coefficient of `x ^ γ` in
the alternant of μ + δ, where δ = `l.lowerCount Eq`, is `s γ` if `ν γ = μ` and `0` otherwise. -/
lemma coeff_alternant (hs : IsStraightening l s ν) (hl : l.Injective) {μ : n → ℤ}
    (hμ : IsKDominant ε (-l) μ) (γ : n → ℤ) :
    (alternant ε (μ + l.lowerCount Eq)).coeff γ = s γ * if ν γ = μ then 1 else 0 := by
  rw [hs.apply_eq γ _ isWeylAntisymm_alternant,
    alternant_coeff_of_isKDominant hl hμ (hs.isKDominant γ)]

/-- For a straightening `s`, `ν` and injective `l`, an exponent `μ + δ` with μ dominant is
already straight: its weight is μ and its sign is `1`. Here δ = `l.lowerCount Eq`. -/
lemma apply_add_lowerCount (hs : IsStraightening l s ν) (hl : l.Injective) {μ : n → ℤ}
    (hμ : IsKDominant ε (-l) μ) : ν (μ + l.lowerCount Eq) = μ ∧ s (μ + l.lowerCount Eq) = 1 := by
  simpa [hs.coeff_alternant hl hμ, ite_eq_iff] using
    alternant_coeff_of_isKDominant hl hμ hμ

/-- For a straightening `s`, `ν` of exponents and injective `l`, the virtual characters
`s γ • kTypeChar (ν γ)` satisfy Weyl's formula for suitable Laurent polynomials `Y γ`. -/
lemma exists_isWeylFamily (hs : IsStraightening l s ν) (hl : l.Injective) :
    ∃ Y : (n → ℤ) → ℂ[n → ℤ], IsWeylFamily l (virtualChar ε s ν) Y := by
  choose Y hY alt_eq using fun γ ↦ exists_alternant_eq_rootProd_mul l hl (hs.isKDominant γ)
    (hs.apply_eq γ)
  exact ⟨Y, by simpa [virtualChar] using hY, alt_eq⟩

/-- For a straightening `s`, `ν` of exponents and injective `l`, the inner product in L²(K) of
the virtual characters of γ and μ is the coefficient of `x ^ γ` in the alternant of μ. -/
lemma inner_virtualChar (hs : IsStraightening l s ν) (hl : l.Injective) (γ μ : n → ℤ) :
    ⟪toLp (E := ℂ) 2 (haarK ε) ℂ (virtualChar ε s ν γ),
      toLp (E := ℂ) 2 (haarK ε) ℂ (virtualChar ε s ν μ)⟫_ℂ = (alternant ε μ).coeff γ := by
  -- Brauer's rule with d the virtual character of μ and f = 1; by orthogonality to the trivial
  -- character, the coefficients of 1 are those of the Weyl denominator.
  have inner_one (β : n → ℤ) :
      ⟪toLp (E := ℂ) 2 (haarK ε) ℂ (virtualChar ε s ν β), toLp (E := ℂ) 2 (haarK ε) ℂ 1⟫_ℂ =
        (alternant ε (l.lowerCount Eq)).coeff β := by
    rw [← zero_add (l.lowerCount Eq), hs.coeff_alternant hl (fun _ _ _ _ ↦ le_rfl),
      ← integral_conj_kTypeChar (ε := ε)]
    simp [virtualChar, inner_smul_left, inner_toLp]
  obtain ⟨Y, hY⟩ := hs.exists_isWeylFamily hl
  calc
    _ = (Y μ).coeff.sum fun (β : n → ℤ) (c : ℂ) ↦
        c * (alternant ε (l.lowerCount Eq)).coeff (-β + γ) := by
      rw [← mul_one (virtualChar ε s ν μ), hY.inner_toLp_mul hl (hY.apply_conj μ)]
      simp only [inner_one]
    _ = _ := by rw [hY.alternant_eq μ, weyl_denominator hl, mul_comm, coeff_mul_apply_left]

/-- For a straightening `s`, `ν` of exponents and injective `l`, the virtual characters of the
exponents μ + δ with μ dominant, that is, the characters of the K-types, are orthonormal
in L²(K). Here δ = `l.lowerCount Eq`. -/
lemma orthonormal_virtualChar (hs : IsStraightening l s ν) (hl : l.Injective) :
    Orthonormal ℂ (toLp (E := ℂ) 2 (haarK ε) ℂ ∘
      fun μ : {μ : n → ℤ // IsKDominant ε (-l) μ} ↦ virtualChar ε s ν (μ + l.lowerCount Eq)) := by
  refine orthonormal_iff_ite.2 fun i j ↦ ?_
  simp [hs.inner_virtualChar hl, hs.apply_add_lowerCount hl i.2, hs.coeff_alternant hl j.2,
    Subtype.ext_iff]

/-- For a straightening `s`, `ν` of exponents and injective `l`, every virtual character is in
the span of the characters of the K-types. -/
lemma virtualChar_mem_span (hs : IsStraightening l s ν) (hl : l.Injective) (γ : n → ℤ) :
    virtualChar ε s ν γ ∈ Submodule.span ℂ (Set.range fun μ : {μ : n → ℤ // IsKDominant ε (-l) μ} ↦
      virtualChar ε s ν (μ + l.lowerCount Eq)) := by
  rw [show virtualChar ε s ν γ = (s γ : ℂ) • virtualChar ε s ν (ν γ + l.lowerCount Eq) by
    simp [virtualChar, hs.apply_add_lowerCount hl (hs.isKDominant γ)]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨ν γ, hs.isKDominant γ⟩, rfl⟩)

end New.Orbital.IsStraightening

/-- Let the class function `d` on K equal `D` on the torus, let `ψ g k = l.dsCoeff (g⁻¹ k g)` and
let `g ↦ d * ψ g` be integrable. Its integral over G is then a class function on K, equal on the
torus to `D` times the orbital integral of the discrete series coefficient `l.dsCoeff`. -/
lemma New.Orbital.integral_mul_dsCoeff_apply_conj {d : C(maxCompactU ε, ℂ)} {D : ℂ[n → ℤ]}
    (hd : ∀ (y : maxCompactU ε) (x : n → Circle), d (y * diagTorusK x * y⁻¹) = torusEval x D)
    {ψ : C(USign ε, C(maxCompactU ε, ℂ))}
    (hψ : ∀ (g : USign ε) (k : maxCompactU ε), ψ g k = l.dsCoeff (g⁻¹ * k * g :))
    (h_int : Integrable fun g : USign ε ↦ d * ψ g) (y : maxCompactU ε) (x : n → Circle) :
    (∫ g : USign ε, d * ψ g) (y * diagTorusK x * y⁻¹) =
      torusEval x D * ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε x * g :) := by
  -- Evaluate under the integral, then substitute `g ↦ y g`.
  simp_rw [integral_apply h_int, ContinuousMap.mul_apply, hd, hψ]
  rw [integral_const_mul, ← integral_mul_left_eq_self _ y.val]
  simp [mul_assoc]

/-- Let `ψ g k = l.dsCoeff (g⁻¹ k g)`, let `d` be a class function on K that equals `D` on the
torus, with `g ↦ d * ψ g` integrable, and let `m γ` be the formal degree times the integral over G
of the coefficient of `ψ g` against the character of `ν γ`, assumed integrable. Let `l` be
injective and let the virtual characters of `s`, `ν` satisfy Weyl's formula. Then the inner product
in L²(K) of the virtual character of γ with `l.formalDegree • ∫ d * ψ g` is
`∑ D_β s (-β + γ) m (-β + γ)`, by Brauer's rule. -/
lemma New.Orbital.inner_virtualChar_formalDegree_smul_integral (hl : l.Injective)
    {s : (n → ℤ) → ℤ} {ν : (n → ℤ) → n → ℤ} {Y : (n → ℤ) → ℂ[n → ℤ]}
    (hXY : IsWeylFamily l (virtualChar ε s ν) Y) {d : C(maxCompactU ε, ℂ)} {D : ℂ[n → ℤ]}
    (hd : ∀ (y : maxCompactU ε) (x : n → Circle), d (y * diagTorusK x * y⁻¹) = torusEval x D)
    {ψ : C(USign ε, C(maxCompactU ε, ℂ))}
    (hψ : ∀ (g : USign ε) (k : maxCompactU ε), ψ g k = l.dsCoeff (g⁻¹ * k * g :))
    (h_int : Integrable fun g : USign ε ↦ d * ψ g) {m : (n → ℤ) → ℕ}
    (int_m : ∀ γ : n → ℤ, Integrable fun g : USign ε ↦ ∫ k : maxCompactU ε,
      l.dsCoeff (g⁻¹ * k * g :) * starRingEnd ℂ ((toHCParam ε (ν γ)).kTypeChar k) ∂haarK ε)
    (hm : ∀ γ : n → ℤ, l.formalDegree * ∫ g : USign ε, ∫ k : maxCompactU ε,
      l.dsCoeff (g⁻¹ * k * g :) * starRingEnd ℂ ((toHCParam ε (ν γ)).kTypeChar k) ∂haarK ε = m γ)
    (γ : n → ℤ) :
    ⟪toLp (E := ℂ) 2 (haarK ε) ℂ (virtualChar ε s ν γ),
      toLp (E := ℂ) 2 (haarK ε) ℂ (l.formalDegree • ∫ g : USign ε, d * ψ g)⟫_ℂ =
        D.coeff.sum fun (β : n → ℤ) (c : ℂ) ↦ c * (s (-β + γ) * m (-β + γ)) := by
  let L : C(maxCompactU ε, ℂ) →L[ℂ] Lp ℂ 2 (haarK ε) := toLp 2 (haarK ε) ℂ
  have inner_ψ (β : n → ℤ) (g : USign ε) : ⟪L (virtualChar ε s ν β), L (ψ g)⟫_ℂ =
      s β * ∫ k, l.dsCoeff (g⁻¹ * k * g :) *
        starRingEnd ℂ ((toHCParam ε (ν β)).kTypeChar k) ∂haarK ε := by
    simp [L, virtualChar, hψ, inner_smul_left, inner_toLp, ← integral_const_mul]
  -- move the inner product under the integral, then integrate Brauer's rule term by term
  have swap : ⟪L (virtualChar ε s ν γ), L (∫ g, d * ψ g)⟫_ℂ =
      ∫ g, ⟪L (virtualChar ε s ν γ), L (d * ψ g)⟫_ℂ :=
    ((innerSL ℂ _ ∘L L).integral_comp_comm h_int).symm
  rw [L.map_smul_of_tower, inner_smul_right_eq_smul, swap]
  simp only [L, hXY.inner_toLp_mul hl hd, Finsupp.sum] at inner_ψ ⊢
  simp only [inner_ψ]
  rw [integral_finsetSum _ fun β _ ↦ ((int_m _).const_mul _).const_mul _]
  simp [← hm, integral_const_mul, mul_sum, mul_left_comm]

/-- The powers of `l.rootProd r` have integer coefficients. -/
lemma New.Orbital.exists_int_rootProd_pow (r : ℤˣ → ℤˣ → Prop) [DecidableRel r] (N : ℕ) :
    ∃ Z : ℤ[n → ℤ], mapRingHom (n → ℤ) (castRingHom ℂ) Z = l.rootProd r ^ N :=
  ⟨(∏ a, ∏ b with r (ε a) (ε b) ∧ l b < l a,
    (.single (Pi.single a 1) 1 - .single (Pi.single b 1) 1)) ^ N, by simp [HCParam.rootProd]⟩

/-- The Laurent polynomial `P` is `Vc D Θ`. Here Θ(x) = deg ∫ ψ(g⁻¹ x g) dg is the normalised
orbital integral of ψ = `l.dsCoeff` on the diagonal torus, `Vc = l.rootProd Eq` is the Weyl
denominator of K, Λ = `l.lowestKType` and δ = `l.lowerCount Eq`. -/
structure New.Orbital.IsOrbitalLaurent (D P : ℂ[n → ℤ]) : Prop where
  /-- `P` is antisymmetric under the Weyl group of K. -/
  antisymm : IsWeylAntisymm ε P.coeff
  /-- On the torus, `P = Vc D Θ`. -/
  torusEval_eq (x : n → Circle) : torusEval x P = torusEval x (l.rootProd Eq * D) *
    (l.formalDegree * ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε x * g :))
  /-- `P` is `D` times a series with coefficient `1` at Λ + δ that lives in the Weyl translates
  of Λ + δ + `l.rootCone`. -/
  isConeSeriesMultiple : IsConeSeriesMultiple l (l.lowestKType + l.lowerCount Eq) D P

/-- Let `l` have a large gap and let the virtual characters of a straightening `s`, `ν` satisfy
Weyl's formula. With `D` the N-th power of the noncompact root product `(-l).rootProd Ne` and N = 4
(card n)² + 1, some continuous function `h` on K and multiplicities `m γ` of the K-types `ν γ`
satisfy: `h` is a class function equal to `D` times the normalised orbital integral on the torus;
its coefficient against the virtual character of γ is `∑ D_β s (-β + γ) m (-β + γ)`; `m γ = 1` at
the lowest K-type; and `m γ ≠ 0` only if `ν γ - l.lowestKType` lies in `l.rootCone`, the cone of
positive roots. -/
lemma New.Orbital.exists_classFun_orbital_integral [Nonempty n]
    (hg : l.HasLargeGap (10 * card n ^ 5)) {s : (n → ℤ) → ℤ} {ν : (n → ℤ) → n → ℤ}
    (hs : IsStraightening l s ν) {Y : (n → ℤ) → ℂ[n → ℤ]}
    (hXY : IsWeylFamily l (virtualChar ε s ν) Y) :
    let D : ℂ[n → ℤ] := (-l).rootProd Ne ^ (4 * card n ^ 2 + 1)
    ∃ (h : C(maxCompactU ε, ℂ)) (m : (n → ℤ) → ℕ),
      (∀ (y : maxCompactU ε) (x : n → Circle), h (y * diagTorusK x * y⁻¹) = torusEval x D *
        (l.formalDegree * ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε x * g :))) ∧
      (∀ γ : n → ℤ, ⟪toLp (E := ℂ) 2 (haarK ε) ℂ (virtualChar ε s ν γ),
          toLp (E := ℂ) 2 (haarK ε) ℂ h⟫_ℂ =
        D.coeff.sum fun (β : n → ℤ) (c : ℂ) ↦ c * (s (-β + γ) * m (-β + γ))) ∧
      (∀ γ : n → ℤ, ν γ = l.lowestKType → m γ = 1) ∧
      ∀ γ : n → ℤ, m γ ≠ 0 → ν γ - l.lowestKType ∈ l.rootCone := by
  intro D
  let ψ : C(USign ε, C(maxCompactU ε, ℂ)) :=
    (mk fun p : USign ε × maxCompactU ε ↦ l.dsCoeffSmooth.val (p.1⁻¹ * p.2 * p.1)).curry
  have hψ (g : USign ε) (k : maxCompactU ε) : ψ g k = l.dsCoeff (g⁻¹ * k * g :) := rfl
  -- `D` is symmetric under the Weyl group, so it extends to a continuous class function d on K.
  obtain ⟨d, hd⟩ := hXY.exists_apply_conj_eq (D := D) hg.injective fun w hw x ↦ by
    simp [D, torusEval_rootProd_noncompact_comp hg.neg.injective hw]
  have integrable : Integrable fun g ↦ d * ψ g := integrable_mul_dsCoeff_conj l hg hd hψ
  -- The multiplicities are the formal degree times the integrals over g of ⟪χ, ψ g⟫, χ the
  -- character of `ν γ`.
  choose int_m m hm m_top m_cone using fun γ ↦ exists_kType_multiplicity (hs.isKDominant γ)
  refine ⟨l.formalDegree • ∫ g, d * ψ g, m, fun y x ↦ ?_,
    inner_virtualChar_formalDegree_smul_integral l hg.injective hXY hd hψ integrable int_m hm,
    m_top, m_cone⟩
  simp [integral_mul_dsCoeff_apply_conj l hd hψ integrable, mul_left_comm]

/-- The normalised orbital integral Θ(x) = deg ∫ ψ(g⁻¹ x g) dg, for ψ = `l.dsCoeff` and `l` with a
large gap, becomes a Laurent polynomial once its denominators are cleared; here `n` is nonempty, and
`HasLargeGap` with constant 10 (card n)⁵ means a gap of at least 500 (card n)³ + 10 (card n)⁵. Let
`D` be the N-th power of ∏ (x_a - x_b) over `ε a ≠ ε b`, `l a < l b`, with N = 4 (card n)² + 1 so
that the integral times `D` converges uniformly in x. Then `Vc D Θ`, with `Vc = l.rootProd Eq` the
Weyl denominator of K, is a Laurent polynomial `P` satisfying `New.Orbital.IsOrbitalLaurent`, namely
antisymmetry of `P` and conditions on the leading term and support of `P / D` stated via
Λ = `l.lowestKType` and δ = `l.lowerCount Eq`.

This is the first step to Harish-Chandra's formula for elliptic orbital integrals; the Laurent
polynomial `P` is computed in `Lib.DiscreteSeries.Character.FormalDegree`. -/
lemma New.Orbital.exists_laurent_orbital_integral [Nonempty n]
    (hg : l.HasLargeGap (10 * card n ^ 5)) :
    ∃ P : ℂ[n → ℤ], IsOrbitalLaurent l ((-l).rootProd Ne ^ (4 * card n ^ 2 + 1)) P := by
  -- `D Θ` extends to a continuous class function `h` on K. Its coefficients against the characters
  -- of K are integers (Brauer's rule and `exists_kType_multiplicity`) and square-summable, so
  -- almost all vanish; by completeness `h` is a finite sum of characters, and Weyl's formula
  -- gives `P = Vc h`.
  let δ : n → ℤ := l.lowerCount Eq
  let D : ℂ[n → ℤ] := (-l).rootProd Ne ^ (4 * card n ^ 2 + 1)
  change ∃ P, IsOrbitalLaurent l D P
  have hl : l.Injective := hg.injective
  -- `X γ` is the virtual character of γ, `e i` is the character of the K-type i, and `L` maps
  -- continuous functions on K to L²(K).
  choose s ν hν apply_eq using exists_sign_isKDominant hl
  have hs : IsStraightening l s ν := ⟨hν, apply_eq⟩
  let X : (n → ℤ) → C(maxCompactU ε, ℂ) := virtualChar ε s ν
  obtain ⟨Y, hXY⟩ := hs.exists_isWeylFamily hl
  let e (i : {μ : n → ℤ // IsKDominant ε (-l) μ}) : C(maxCompactU ε, ℂ) := X (i + δ)
  let L : C(maxCompactU ε, ℂ) →L[ℂ] Lp ℂ 2 (haarK ε) := toLp 2 (haarK ε) ℂ
  obtain ⟨h, m, h_apply, coeff_eq, m_top, m_cone⟩ := exists_classFun_orbital_integral l hg hs hXY
  let t (γ : n → ℤ) : ℂ := s γ * m γ
  have coeff_h (γ : n → ℤ) : ⟪L (X γ), L h⟫_ℂ = D.coeff.sum fun β c ↦ c * t (-β + γ) := coeff_eq γ
  have h_class (y : maxCompactU ε) (x : n → Circle) :
      h (y * diagTorusK x * y⁻¹) = h (diagTorusK x) := by
    simpa using (h_apply y x).trans (h_apply 1 x).symm
  -- The coefficients of `h` against the `e i` are integers, as `D` has integer coefficients `Z`;
  -- so only finitely many are not zero.
  obtain ⟨Z, hZ : mapRingHom (n → ℤ) (castRingHom ℂ) Z = D⟩ := exists_int_rootProd_pow (-l) Ne _
  have orthonormal : Orthonormal ℂ (L ∘ e) := hs.orthonormal_virtualChar hl
  have finite : (Function.support fun i ↦ ⟪L (e i), L h⟫_ℂ).Finite :=
    finite_support_inner_of_int orthonormal fun i ↦
      ⟨∑ β ∈ D.coeff.support, Z.coeff β * (s (-β + (i + δ)) * m (-β + (i + δ))),
        by simp [e, coeff_h, ← hZ, t, Finsupp.sum]⟩
  -- By completeness `h = ∑ a_i e_i`.
  let a : {μ : n → ℤ // IsKDominant ε (-l) μ} →₀ ℂ :=
    Finsupp.ofSupportFinite (fun i ↦ ⟪L (e i), L h⟫_ℂ) finite
  have h_eq : h = Finsupp.linearCombination ℂ e a :=
    hXY.eq_linearCombination hl orthonormal (hs.virtualChar_mem_span hl) h_class fun _ ↦ rfl
  -- `P = ∑ a_i alternant ε (i + δ)`
  refine ⟨Finsupp.linearCombination ℂ (fun i ↦ alternant ε (i.val + δ)) a, ?_, fun x ↦ ?_, t, ?_,
    ?_, fun γ hγ ↦ ⟨ν γ + δ, ?_⟩⟩
  · -- alternants are antisymmetric
    simp +contextual [Finsupp.linearCombination_apply, IsWeylAntisymm, isWeylAntisymm_alternant _,
      mul_left_comm (a _), Finsupp.sum, mul_sum]
  · -- Weyl's formula for each character
    calc
      _ = torusEval x (l.rootProd Eq) * h (1 * diagTorusK x * 1⁻¹) := by
        rw [h_eq]
        exact hXY.torusEval_linearCombination_alternant _ a 1 x
      _ = _ := by rw [h_apply, map_mul, mul_assoc]
  · -- the coefficient of x^γ in `P` is ⟪L (X γ), L h⟫
    -- `coeff_h` must rewrite the sum before simp unfolds it
    simp [↓← coeff_h, h_eq, Finsupp.linearCombination_apply, e, X, L, hs.inner_virtualChar hl,
      Finsupp.sum, inner_sum, inner_smul_right]
  · -- the lowest K-type has multiplicity one
    simp [t, hs.apply_add_lowerCount hl hg.isKDominant_lowestKType, m_top]
  · -- the K-types that occur lie in the shifted cone
    have s_m_ne : s γ ≠ 0 ∧ m γ ≠ 0 := by simpa [t] using hγ
    simp [δ, hs.coeff_alternant hl (hν γ), m_cone, s_m_ne]

end OrbitalLaurent
