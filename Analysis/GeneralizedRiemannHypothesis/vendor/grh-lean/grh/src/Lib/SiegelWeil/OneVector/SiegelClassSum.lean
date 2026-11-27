import Lib.Analytic.EntireLFunction
import Lib.SiegelWeil.Formula.WeilRange
import Lib.Weil.MixedModel.AdaptedSplitting

/-!
# Siegel–Weil for one vector, Siegel's class sum formula and the ratio of masses

This file derives Siegel's formula for representation numbers from the Siegel–Weil formula
`New.SiegelWeil.siegel_weil`. It applies that formula to the hyperbolic plane and to the positive
definite space `stdSpace E κ` with form x*x, of rank at least 3. Laplace's integral for 1/Γ supplies
the archimedean factor.

## Main definitions and results

* `New.SiegelWeil.siegel_weil_one_vector`: the mean of `∑_ξ Ψ(h⁻¹ ξ)` is `Ψ(0)` plus the sum over
  β in E⁺ of the integrals `∫ Ψ(x) ψ(β x* x / 2) dx`.
* `New.SiegelWeil.siegel_weil_fourierCoeff`: the part of this formula that counts the vectors of
  one norm α ≠ 0, detected by a phase.
* `New.normDensity`: the density at α of a function Φ₀ of finite adelic vectors, a Fourier integral
  over the self-adjoint finite adeles.
* `New.classSum_eq_mul_normDensity`: for totally positive α, the class sum (`New.classSum`) of the
  numbers of representations of α by x*x, weighted by Φ₀, is the class sum of 1 times |D_E|^(1/4),
  the factors at the infinite places and the density of Φ₀ at α.
* One step of the mass formula, with an error term: `New.abs_log_mass_ratio_sub_le` estimates the
  ratio of the masses `New.mass E (j + 1)` and `New.mass E j` of the genera of standard lattices. It
  applies Siegel's formula `New.classSum_eq_mul_normDensity` to the vectors of norm `1` in the
  standard lattice, whose class sum is `New.mass E j` by `New.classSum_card_norm_one_eq_mass`, and
  bounds the density by a Gauss sum estimate.

Notions from other files:
* `New.SiegelWeil.mixedValue`: the slice f[x], the value of a test function f at a point x in the
  Schrödinger model. The function x ↦ f[x] is called the Schrödinger function of f.
* `New.SiegelWeil.Lagrangian.zeroTerm`: the functional ev_L attached to a Lagrangian L, the value
  at 0 in a Schrödinger model along L.
* `New.classSum`: the sum of a function over the classes of a level, weighted by 1/#Aut.
* `New.mass`: the mass of the genus of O_E^l, the sum of 1/#Aut over its classes.

## Relation to the literature

Known result: Siegel's formula for representing a number by a hermitian form. Here it is stated for
the representations of a totally positive number by a sum of at least three norms over a CM field
with enough roots of unity, a splitting character and a self-dual lattice, at any level and for any
nonnegative invariant test function. The singular series is left as one adelic Fourier integral, and
the formula is read off from the Siegel–Weil formula. The local densities are not evaluated: for the
standard lattice the integral is estimated by Gauss sums and a zeta value. Source: A. Weil, Acta
Math. 113 (1965), Thm 5 for one vector; classically, C. L. Siegel, Ann. of Math. 36 (1935), and
H. Braun, Zur Theorie der hermitischen Formen, Abh. Math. Sem. Hamburg 14 (1941).

Known result: Mass formula for unimodular hermitian lattices, as the ratio of consecutive masses.
Only this ratio in large rank is obtained, up to an explicit error that depends on the field only
through its degree, for CM fields with enough roots of unity (so unramified over the real subfield),
a splitting character and a self-dual rank-one lattice. It is derived from Siegel's formula for
vectors of norm one and a Gauss sum bound. Source: W. T. Gan, J. Hanke, J.-K. Yu, On an exact mass
formula of Shimura, Duke Math. J. 107 (2001); M. Kirschmer, Definite quadratic and hermitian forms
with small class number (2016), 4.2.7, 4.2.9.
-/

section OneVector

open NumberField Real Matrix MeasureTheory Complex Finset Function New SiegelWeil WeilData Space Int
  AddChar GaussianFourier FractionalIdeal CompleteSplitting Splitting Prod Fintype Lagrangian Nat
  FourierTransform

/-! ### The Siegel–Weil formula for the hyperbolic plane -/

/-- The splitting of the hyperbolic plane with basis `l`, `k` in which the first frame is
`l + j⁻¹ a k`, which spans an isotropic line for `a` in `E⁺`, and the second is `k`. The complement
of the two frames is `stdSpace E Empty`, of rank 0, so its embedding `i` is `0`. Here `j` is the
purely imaginary element of the Weil data. -/
noncomputable def New.SiegelWeil.shearSplitting {E : Type} [Field E] [CMType E] [WeilData E]
    (a : maximalRealSubfield E) : (hyperbolicSpace E Unit).Splitting (stdSpace E Empty) Unit where
  k := (hyperbolicSplitting E Unit).l + (j⁻¹ * a : E) • (hyperbolicSplitting E Unit).k
  l := (hyperbolicSplitting E Unit).k
  i := 0
  gram_kk := by
    simp [mem_maximalRealSubfield_iff_star_eq.1, hyperbolicSplitting,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.add_mul, fromCols_mul_fromBlocks,
      Matrix.mul_add, fromCols_mul_fromRows]
  gram_ll := by
    simp [hyperbolicSplitting, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  gram_lk := by
    simp [hyperbolicSplitting, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromBlocks, Matrix.mul_add, fromCols_mul_fromRows]
  gram_ii := by simp [← ext_iff]
  gram_ik := by simp
  gram_il := by simp
  card_eq := by simp

/-- A Lagrangian of the hyperbolic plane, that is, an isotropic line, that is none of the lines of
the `l + j⁻¹ a k` with `a ∈ E⁺` (the first frames of the `shearSplitting a`) is the line of `k`. -/
lemma New.SiegelWeil.eq_lagrangian_of_notMem_range_shear {E : Type} [Field E] [CMType E]
    [WeilData E] {L : Lagrangian (hyperbolicSpace E Unit)}
    (hL : L ∉ Set.range (lagrangian ∘ shearSplitting)) :
    L = lagrangian (hyperbolicSplitting E Unit) := by
  refine eq_of_le fun y hy ↦ ?_
  suffices hy0 : y (Sum.inl ()) = 0 by
    refine ⟨y ∘ Sum.inr, funext fun i ↦ ?_⟩
    cases i <;> simp [hy0, hyperbolicSplitting]
  -- Otherwise `L` is the line of `y`, and isotropy of `y` says that `j` times its slope is real.
  by_contra hy0
  apply hL
  have h_real : j * y (Sum.inr ()) / y (Sum.inl ()) ∈ maximalRealSubfield E :=
    mem_maximalRealSubfield_iff_star_eq.mpr <| by simpa [mulVec, hy0, dotProduct, field,
      add_eq_zero_iff_neg_eq, j_ne_zero, mul_add, sum_add_distrib] using (L.prop y).mp hy y hy
  refine ⟨⟨_, h_real⟩, eq_of_le fun w hw ↦ ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : Unit → E, (shearSplitting ⟨_, h_real⟩).k.mulVecLin t = w := hw
  have h_smul : w = (t () / y (Sum.inl ())) • y := by
    have hj : (j : E) ≠ 0 := j_ne_zero
    simp [← ht, shearSplitting, field, hyperbolicSplitting, funext_iff]
  rw [h_smul]
  exact L.val.smul_mem _ hy

/-- Let `f` be a test function for the hyperbolic plane and `stdSpace E κ` with Schrödinger function
`Ψ`. Its zero term (the value at `0` in the Schrödinger model) along the isotropic line of
`l + j⁻¹ β k`, the frame of `shearSplitting β`, is `∫ Ψ(x) ψ(β x* x / 2) dx`, with `ψ` the standard
character `stdAddChar E`. -/
lemma New.SiegelWeil.zeroTerm_shearSplitting {E κ : Type} [Field E] [CMType E] [WeilData E]
    [Fintype κ] [DecidableEq κ] {f : 𝒮 ((hyperbolicSpace E Unit).hom (stdSpace E κ))}
    {Ψ : (κ → 𝔸 E) → ℂ}
    (hf : ∀ x : κ → 𝔸 E,
      mixedValue (stdSpace E κ) (hyperbolicSplitting E Unit) (replicateCol Unit x) f = Ψ x)
    (β : maximalRealSubfield E) :
    (lagrangian (shearSplitting β)).zeroTerm (stdSpace E κ) f =
      ∫ x : κ → 𝔸 E, Ψ x * stdAddChar E ((2⁻¹ : E) * ((β : E) * (star x ⬝ᵥ x))) := by
  -- It is the integral of the Schrödinger values for the opposite splitting, which differ from
  -- those for `D` by the character.
  set D : (hyperbolicSpace E Unit).Splitting (stdSpace E Empty) Unit := hyperbolicSplitting E Unit
  have h_kCoord :
      kCoord (shearSplitting β).symm = D.kCoord + star (toAdele (j⁻¹ * β.1)) • D.lCoord := by
    simp [kCoord, lCoord, lAdelic, kAdelic, shearSplitting, D, Splitting.symm, Matrix.add_mul,
      (hyperbolicSplitting E Unit).l.map_add, Matrix.map_smulₛₗ _ toAdele]
  -- The opposite splitting has the first frame `k` of `D`, so the two have the same zero term.
  have h_frame : ((shearSplitting β).symm.homSource (stdSpace E κ)).zeroTerm =
      D.homSlice (stdSpace E κ) 0 := by
    rw [homSlice_zero]
    exact (zeroTerm_homSource_congr _ _ D.gram_kk rfl).symm
  -- Write the zero term as an integral of source terms over `x : κ → 𝔸 E`.
  have h_integral : (lagrangian (shearSplitting β)).zeroTerm (stdSpace E κ) f =
      ∫ x : κ → 𝔸 E, θ ((stdSpace E Empty).hom (stdSpace E κ))
        ((shearSplitting β).symm.homSlice (stdSpace E κ) (replicateCol Unit x) f) := by
    have h_mixed : ((shearSplitting β).homSource (stdSpace E κ)).zeroTerm f =
        ∫ y : κ × Unit → 𝔸 E, ((shearSplitting β).symm.homSource (stdSpace E κ)).slice y f :=
      (shearSplitting β).symm.symm_homSource_zeroTerm_eq_integral (stdSpace E κ) f
    have h_source (x : Matrix κ Unit (𝔸 E)) : (shearSplitting β).symm.homSlice (stdSpace E κ) x =
        ((shearSplitting β).symm.homSource (stdSpace E κ)).slice (matrixToVec x) := by
      conv_lhs => rw [← x.one_mul]
      exact (shearSplitting β).symm.homSlice_eq_slice (stdSpace E κ) x
    rw [zeroTerm_lagrangian_eq_theta, h_mixed, ← (θ _).integral_comp_comm (by fun_prop),
      ← (volume_measurePreserving_piCongrLeft _ (.symm (.prodPUnit _))).integral_comp']
    simp only [h_source]
    rfl
  rw [h_integral]
  congr with x
  -- The source term is the character times the value at `0` of the source term for `D`.
  have h_value : D.homSlice (stdSpace E κ) (replicateCol Unit x) f 0 = Ψ x := hf x
  rw [homSlice, h_frame, ContinuousLinearMap.comp_apply, homSlice_rho, h_kCoord]
  simp [trace, Matrix.add_mul, Matrix.mul_assoc, h_value, ← map_mul, ← mul_assoc, mul_comm (Ψ x),
    div_eq_inv_mul, j_ne_zero]

/-- **The Siegel–Weil formula for one vector**, for `stdSpace E κ` of rank at least 3. Let `l`, `k`
be the standard basis of the hyperbolic plane and `j` the purely imaginary element of the Weil data.
The zero terms along the isotropic lines of `l + j⁻¹ β k` (the splittings `shearSplitting β`), for
`β` in the maximal real subfield `E⁺`, are summable in operator norm. For a test function `f` with
Schrödinger function `Ψ` (slices for `hyperbolicSplitting`), the integral over the unitary quotient
(for `quotMeasure`) of the theta value of `ω(1, h) f`, which is `splitWeil (1, h) f`, equals the
total measure times the sum of `Ψ(0)` and these zero terms, which are computed in
`zeroTerm_shearSplitting`. -/
lemma New.SiegelWeil.siegel_weil_one_vector {E κ : Type} [Field E] [CMType E] [WeilData E]
    [Fintype κ] [DecidableEq κ] (h_card : 3 ≤ card κ) :
    (Summable fun β : maximalRealSubfield E ↦
      ‖(lagrangian (shearSplitting β)).zeroTerm (stdSpace E κ)‖) ∧
    ∀ f : 𝒮 ((hyperbolicSpace E Unit).hom (stdSpace E κ)),
      ∫ h : G E (1 : κ → ℤˣ), ((hyperbolicSpace E Unit).hom (stdSpace E κ)).θ
          (splitWeil (hyperbolicSpace E Unit) (stdSpace E κ) (1, h) f) ∂(stdSpace E κ).quotMeasure =
        (stdSpace E κ).quotMeasure.real Set.univ *
          (mixedValue (stdSpace E κ) (hyperbolicSplitting E Unit) 0 f +
            ∑' β : maximalRealSubfield E,
              (lagrangian (shearSplitting β)).zeroTerm (stdSpace E κ) f) := by
  -- The Siegel–Weil formula sums over all isotropic lines: the line of `k` and the sheared lines.
  set D : (hyperbolicSpace E Unit).Splitting (stdSpace E Empty) Unit := hyperbolicSplitting E Unit
  obtain ⟨h_summable, hSW⟩ := siegel_weil (stdSpace E κ) D (by simpa)
  -- The line determines the slope `a` of its frame.
  have h_inj : Injective (lagrangian ∘ shearSplitting (E := E)) := fun a b hab ↦ by
    obtain ⟨t, ht⟩ : ∃ t : Unit → E,
        (shearSplitting a).k.mulVecLin t = (shearSplitting b).k.mulVecLin 1 :=
      hab.ge (LinearMap.mem_range_self _ 1)
    revert ht
    simp +contextual [shearSplitting, hyperbolicSplitting, funext_iff, j_ne_zero]
  have h_ne (β : maximalRealSubfield E) : lagrangian (shearSplitting β) ≠ lagrangian D := fun h ↦ by
    obtain ⟨t, ht⟩ : ∃ t : Unit → E, D.k.mulVecLin t = (shearSplitting β).k.mulVecLin 1 :=
      h.le (LinearMap.mem_range_self _ 1)
    simp [shearSplitting, D, hyperbolicSplitting, funext_iff] at ht
  refine ⟨h_summable.comp_injective h_inj, fun f ↦ ?_⟩
  have h_terms : Summable fun L : Lagrangian (hyperbolicSpace E Unit) ↦
    L.zeroTerm (stdSpace E κ) f :=
    .of_norm_bounded (h_summable.mul_right ‖f‖) fun L ↦ (L.zeroTerm _).le_opNorm f
  have h_support : support (fun L ↦ if L = lagrangian D then 0 else L.zeroTerm (stdSpace E κ) f) ⊆
      Set.range (lagrangian ∘ shearSplitting) :=
    support_subset_iff'.2 fun L hL ↦ ite_eq_left (eq_lagrangian_of_notMem_range_shear hL)
  have h_zero : (lagrangian D).zeroTerm (stdSpace E κ) f = mixedValue (stdSpace E κ) D 0 f := by
    simp [zeroTerm_lagrangian_eq_theta, homSlice, mixedValue]
  -- Split off the line of `k`.
  rw [(hSW f).2, h_terms.tsum_eq_add_tsum_ite (lagrangian D), h_zero, ← h_inj.tsum_eq h_support]
  simp only [Function.comp_apply, h_ne, ite_false]

/-! ### The vectors of one norm, detected by a phase -/

/-- With `R = E⁺` the maximal real subfield of `E`, let `ι` be the diagonal map from `R` to the
product of the real functions on the places and the self-adjoint finite adeles (`Φ v` is the
embedding at the place `v`). Then there is a bounded measurable `Ω` of volume `|D_E|^(-1/4)` such
that every point has exactly one translate by `R` in `Ω ×ˢ selfAdjointCodifferent E 1`, where
`selfAdjointCodifferent E 1` is the group of self-adjoint finite adeles in the inverse different. -/
lemma New.exists_fundamentalDomain_real {E : Type} [Field E] [CMType E] [WeilData E]
    (ι : maximalRealSubfield E →+ (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E))
    (ι_fst : ∀ (a : maximalRealSubfield E) (v : InfinitePlace E), (ι a).1 v = (Φ v a).re)
    (ι_snd : ∀ a : maximalRealSubfield E, ((ι a).2 : 𝔸f E) = (a : E)) :
    ∃ Ω : Set (InfinitePlace E → ℝ),
      MeasurableSet Ω ∧
      Bornology.IsBounded Ω ∧
      √√|NumberField.discr E| * volume.real Ω = 1 ∧
      ∀ x : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E),
        ∃! a : maximalRealSubfield E, ι a + x ∈ Ω ×ˢ selfAdjointCodifferent E 1 := by
  let R : Subfield E := maximalRealSubfield E
  -- `selfAdjointCodifferent E 1` meets `R` in its inverse different `J`: as `E / R` is unramified,
  -- the different of `E` is the extension of that of `R`.
  let J : (FractionalIdeal (nonZeroDivisors (𝓞 R)) R)ˣ :=
    .mk0 (differentIdeal ℤ (𝓞 R))⁻¹ (by simp [differentIdeal_ne_bot])
  have h_meet (a : R) : (ι a).2 ∈ selfAdjointCodifferent E 1 ↔ a ∈ J.val := by
    -- Both sides say that `d a` is integral, for `d` in the different of `E`, resp. of `R`.
    suffices (∀ d ∈ Ideal.map (algebraMap (𝓞 R) (𝓞 E)) (differentIdeal ℤ (𝓞 R)),
        ((d : E) : 𝔸f E) * (a : E) ∈ Ô E) ↔
        ∀ d ∈ differentIdeal ℤ (𝓞 R), (((d : R) : E) : 𝔸f E) * (a : E) ∈ Ô E by
      simp [J, mem_inv_iff, ← algebraMap_mem_Ô, forall_ψf_mul_eq_one_iff, mul_comm a,
        ← IsIntegralClosure.isIntegral_iff (R := ℤ),
        ← isIntegral_algebraMap_iff (A := R) (B := E), R, mul_comm (ι a).2.val,
          selfAdjointCodifferent,
        differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 R) (𝓞 E), differentIdeal_ne_bot]
      rwa [ι_snd]
    -- The condition is linear, so it may be checked on generators of the extended ideal.
    let M : Ideal (𝓞 E) := (Subalgebra.toSubmodule ⟨_, coe_mem_Ô (E := E)⟩).comap
      (.toSpanSingleton (𝓞 E) (𝔸f E) ((a : E) : 𝔸f E))
    exact Ideal.map_le_iff_le_comap (K := M)
  -- `R + selfAdjointCodifferent E 1` is everything: with `c = stdLattice.traceOneAdele`, if
  -- `c z - a` is integral, then so is `z - (a + star a)`, because `c + star c = 1`.
  have h_span (z : selfAdjoint (𝔸f E)) : ∃ a : R, z - (ι a).2 ∈ selfAdjointCodifferent E 1 := by
    obtain ⟨a, ha⟩ := exists_sub_mem_Ô (stdLattice.traceOneAdele * z.val)
    refine ⟨Algebra.trace R E a, fun x hx ↦ ψf_eq_one_of_mem (mul_mem ?_ hx)⟩
    simpa [← add_mul, ← map_add, sub_add_sub_comm, ← trace_maximalRealSubfield_eq_add_star, ι_snd,
      R,
      z.2.star_eq] using add_mem ha (star_mem_Ô ha)
  obtain ⟨e, he, h_re⟩ := exists_mixedEquiv_maximalRealSubfield (E := E)
  obtain ⟨Ω, hΩ, h_bdd, h_vol, h_unique⟩ :=
    exists_fundDomain_prod ι (selfAdjointCodifferent E 1) J h_meet
    h_span e he fun a ↦ (h_re a).trans (funext fun v ↦ (ι_fst a v).symm)
  refine ⟨Ω, hΩ, h_bdd, ?_, h_unique⟩
  -- The volume of `Ω` is `N(J) √|D_R| = |D_R|^{-1/2}`, and `|D_E| = D_R²`.
  simp [h_vol, J, Int.norm_eq_abs, ← cast_abs, abs_discr_eq_discr_maximalRealSubfield_sq, field, R,
    sqrt_sq_eq_abs,
    coeIdeal_absNorm, absNorm_differentIdeal R, measureReal_def, discr_ne_zero]

/-- An adele of the real subfield `E⁺`, given by its real components and its finite part, as a
self-adjoint adele of `E`. -/
noncomputable def New.realAdele {E : Type} [Field E] [CMType E]
    (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) : 𝔸 E :=
  (fun v ↦ z.1 v, z.2)

open scoped Classical in
/-- There are an injective additive map `ι` from `E⁺` to pairs of real components and self-adjoint
finite adeles, compatible with the diagonal embedding through `realAdele`, and a bounded set `Ω` of
real components such that `Ω ×ˢ selfAdjointCodifferent E 1` (the second factor is the inverse
different) is a fundamental domain for the image of `ι`. For self-adjoint `β`, the integral over it
of `z ↦ ψ(z β / 2)`, times `|D_E|^(1/4)`, is `1` if `β = 0` and `0` otherwise. -/
lemma New.exists_isAddFundamentalDomain_realAdele (E : Type) [Field E] [CMType E] [WeilData E] :
    ∃ (ι : maximalRealSubfield E →+ (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E))
      (Ω : Set (InfinitePlace E → ℝ)),
      Injective ι ∧
      (∀ (a : maximalRealSubfield E) (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)),
        realAdele (ι a + z) = toAdele (a : E) + realAdele z) ∧
      Bornology.IsBounded Ω ∧
      IsAddFundamentalDomain ι.range (Ω ×ˢ selfAdjointCodifferent E 1) (volume.prod volume) ∧
      ∀ β : E, star β = β → (√√|discr E| : ℂ) * ∫ z in Ω ×ˢ selfAdjointCodifferent E 1,
        (stdAddChar E ((2⁻¹ : E) * (realAdele z * β)) : ℂ) ∂volume.prod volume =
        if β = 0 then 1 else 0 := by
  -- `r` passes from the self-adjoint adeles of `E` to pairs.
  let R : Subfield E := maximalRealSubfield E
  let r (x : selfAdjoint (𝔸 E)) : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E) :=
    (fun v ↦ ((x : 𝔸 E).1 v).re, ⟨(x : 𝔸 E).2, congrArg Prod.snd x.2.star_eq⟩)
  have realAdele_add (x : selfAdjoint (𝔸 E))
      (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) :
      realAdele (r x + z) = x + realAdele z := by
    ext v
    · simp [realAdele, r, conj_eq_iff_re.1 (congrFun (congrArg Prod.fst x.2.star_eq) v)]
    · simp [realAdele, r]
  let ι : R →+ (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E) :=
    .mk' (fun a ↦ r ⟨toAdele a, (star_toAdele _).trans (by simp [star])⟩) (by simp [r, funext_iff])
  obtain ⟨Ω, hΩ, h_bdd, h_vol, h_unique⟩ :=
    exists_fundamentalDomain_real ι (fun _ _ ↦ rfl) fun _ ↦ rfl
  have h_inj : Injective ι := by simp [Injective, ι, r]
  let s : R ≃+ ι.range := ι.ofInjective h_inj
  have : Countable ι.range := s.surjective.countable
  let μ : Measure ((InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) := volume.prod volume
  have h_fund : IsAddFundamentalDomain ι.range (Ω ×ˢ selfAdjointCodifferent E 1) μ :=
    .mk' (hΩ.prod (isOpen_selfAdjointCodifferent ..).measurableSet).nullMeasurableSet
      fun x ↦ s.existsUnique_congr_right.1 (h_unique x)
  refine ⟨ι, Ω, h_inj, fun a z ↦ realAdele_add _ z, h_bdd, h_fund, fun β hβ ↦ ?_⟩
  split_ifs with hβ0
  · simpa [hβ0, μ, measureReal_def] using congrArg ((↑) : ℝ → ℂ) h_vol
  -- Translating `z` by `t + star t` multiplies the integral by `stdAddChar(βt)`. If the integral
  -- is not zero, then `stdAddChar(βt) = 1` for all adeles `t`, so `β = 0`.
  contrapose hβ0
  refine IsDualFamily.eq_zero_of_forall_eq_one (B₀ := ratAdeles E) β fun t ↦
    (right_eq_mul₀ (right_ne_zero_of_mul hβ0)).1 ?_
  let χ (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) : ℂ :=
    stdAddChar E ((2⁻¹ : E) * (realAdele z * β))
  let w : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E) := r ⟨t + star t, .add_star_self t⟩
  have h_periodic (a : ι.range) (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) :
      χ (a +ᵥ z) = χ z := by
    obtain ⟨_, b, rfl⟩ := a
    simp [χ, ι, realAdele_add, AddSubgroup.vadd_def, add_mul, mul_add, ← toAdele.map_mul,
      -map_mul, map_add_eq_mul]
  have h_shift (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) :
      χ (w + z) = stdAddChar E (β * t) * χ z := by
    rw [← stdAddChar_inv_two_mul_add_star]
    simp [χ, w, realAdele_add, hβ, -map_mul, add_mul, mul_add, mul_comm _ t, map_add_eq_mul]
  open scoped Pointwise in
  calc ∫ z in Ω ×ˢ selfAdjointCodifferent E 1, χ z ∂μ
      = ∫ z in w +ᵥ Ω ×ˢ (selfAdjointCodifferent E 1 : Set (selfAdjoint (𝔸f E))), χ z ∂μ :=
        h_fund.setIntegral_eq (h_fund.vadd_of_comm w) h_periodic
    _ = ∫ z in Ω ×ˢ selfAdjointCodifferent E 1, χ (w + z) ∂μ :=
        (measurePreserving_vadd w μ).setIntegral_image_emb (measurableEmbedding_addLeft w) _ _
    _ = stdAddChar E (β * t) * ∫ z in Ω ×ˢ selfAdjointCodifferent E 1, χ z ∂μ := by
        simp_rw [h_shift, integral_const_mul]

/-- An adelic isometry keeps the norm of a rational vector: for `h` in the adelic unitary group and
a rational `ξ`, the vector `h⁻¹ ξ` has the norm `ξ* ξ`, read as a principal adele. -/
lemma New.star_adeleMatrix_mulVec_dotProduct {E κ : Type} [Field E] [CMType E] [Fintype κ]
    [DecidableEq κ] (h : G E (1 : κ → ℤˣ)) (ξ : κ → E) :
    star (h⁻¹.adeleMatrix *ᵥ toAdele ∘ ξ) ⬝ᵥ h⁻¹.adeleMatrix *ᵥ toAdele ∘ ξ =
      toAdele (star ξ ⬝ᵥ ξ) := by
  -- These are the coordinates of `ξ` at the point of the space moved by `h`.
  have h_move : star (((stdSpace E κ).move h).vecAtPoint ξ) ⬝ᵥ
      ((stdSpace E κ).move h).vecAtPoint ξ = toAdele (star ξ ⬝ᵥ ξ) := by
    simpa using ((stdSpace E κ).move h).stdForm_vecAtPoint ξ ξ
  rw [vecAtPoint_move] at h_move
  simpa [vecAtPoint] using h_move

/-- Unfolding over a fundamental domain `D` of a countable group `Γ` of translations, enumerated by
`e`: if `P (e i +ᵥ z) = T i (F z)` for continuous linear functionals `T i` with summable norms and
`F` is integrable on `D`, then `P` is integrable and `∫ P = ∑' i, T i (∫_D F)`. -/
lemma New.integrable_and_integral_eq_tsum_of_fundamentalDomain {A X I : Type*} [AddCommGroup A]
    [MeasurableSpace A] {μ : Measure A} {Γ : AddSubgroup A} [Countable Γ] [MeasurableConstVAdd Γ A]
    [VAddInvariantMeasure Γ A μ] {D : Set A} (hD : IsAddFundamentalDomain Γ D μ)
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (e : I ≃ Γ) {T : I → X →L[ℂ] ℂ}
    (hT : Summable fun i : I ↦ ‖T i‖) {F : A → X} (hF : IntegrableOn F D μ) {P : A → ℂ}
    (hP_meas : AEStronglyMeasurable P μ) (hPF : ∀ (i : I) (z : A), P (e i +ᵥ z) = T i (F z)) :
    Integrable P μ ∧ ∫ z, P z ∂μ = ∑' i : I, T i (∫ z in D, F z ∂μ) := by
  have h_int : Integrable P μ := by
    refine ⟨hP_meas, ?_⟩
    calc ∫⁻ z, ‖P z‖ₑ ∂μ = ∑' i : I, ∫⁻ z in D, ‖T i (F z)‖ₑ ∂μ := by
          simp [hD.lintegral_eq_tsum'', ← e.tsum_eq, hPF]
      _ ≤ ∑' i : I, ∫⁻ z in D, ‖T i‖ₑ * ‖F z‖ₑ ∂μ := by
          gcongr with i z
          exact (T i).le_opENorm _
      _ < ⊤ := by
          simpa [lintegral_const_mul', ENNReal.tsum_mul_right] using
            ENNReal.mul_lt_top hT.tsum_ofReal_lt_top hF.2
  refine ⟨h_int, ?_⟩
  simp [hD.integral_eq_tsum'' P h_int, ← e.tsum_eq, hPF, (T _).integral_comp_comm hF]

open scoped Classical in
/-- **The Fourier coefficient at `α` of the Siegel–Weil formula for one vector.** Let `κ` have at
least 3 elements. Let `Ψ` be the Schrödinger function of a datum `f` on `Hom` from the hyperbolic
plane to the standard definite space `stdSpace E κ` (J = 1, the form being the sum of the norms of
the coordinates). Let `α ≠ 0` lie in `E⁺`, and for an adele `z` of `E⁺` let
`P z = ∫ Ψ(x) ψ(z (x* x - α) / 2) dx`. Then `P` is integrable. The sum of `Ψ(h⁻¹ ξ)` over the
rational `ξ` with `ξ* ξ = α` converges and is a function on the unitary quotient of `stdSpace E κ`,
and its mean is `|D_E|^(1/4) ∫ P`. The measure of `z` is Lebesgue measure at the infinite places and
gives the codifferent the volume `1`; the factor `|D_E|^(1/4)` makes the covolume of `E⁺` equal to
`1`. -/
lemma New.SiegelWeil.siegel_weil_fourierCoeff {E κ : Type} [Field E] [CMType E] [WeilData E]
    [Fintype κ] [DecidableEq κ] (h_card : 3 ≤ card κ)
    (f : 𝒮 ((hyperbolicSpace E Unit).hom (stdSpace E κ))) {Ψ : (κ → 𝔸 E) → ℂ}
    (hf : ∀ x : κ → 𝔸 E,
      mixedValue (stdSpace E κ) (hyperbolicSplitting E Unit) (replicateCol Unit x) f = Ψ x)
    {α : E} (hα : star α = α) (hα_ne : α ≠ 0)
    {P : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E) → ℂ}
    (hP : ∀ z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E), P z =
      ∫ x : κ → 𝔸 E, Ψ x * stdAddChar E ((2⁻¹ : E) * (realAdele z * (star x ⬝ᵥ x - α)))) :
    let σ (h : G E (1 : κ → ℤˣ)) (ξ : κ → E) : ℂ :=
      if star ξ ⬝ᵥ ξ = α then Ψ (h⁻¹.adeleMatrix *ᵥ toAdele ∘ ξ) else 0
    Integrable P (volume.prod volume) ∧
    (∀ h : G E (1 : κ → ℤˣ), Summable (σ h)) ∧
    ((stdSpace E κ).Γ.FixesLeft fun h : G E (1 : κ → ℤˣ) ↦ ∑' ξ : κ → E, σ h ξ) ∧
    ∫ h : G E (1 : κ → ℤˣ), ∑' ξ : κ → E, σ h ξ ∂(stdSpace E κ).quotMeasure =
      (stdSpace E κ).quotMeasure.real Set.univ * (√√|discr E| *
        ∫ z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E), P z ∂volume.prod volume) := by
  -- Apply the Siegel–Weil formula for one vector to `g`, the integral over a fundamental domain of
  -- `E⁺` in its adeles of the twists of `f` by the unipotent elements `n(z)`.
  intro σ
  set D : (hyperbolicSpace E Unit).Splitting (stdSpace E Empty) Unit := hyperbolicSplitting E Unit
  let R : Subfield E := maximalRealSubfield E
  obtain ⟨ι, Ω, ι_inj, realAdele_add, h_bdd, h_fund, h_orth⟩ :=
    exists_isAddFundamentalDomain_realAdele E
  set μ : Measure ((InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) := volume.prod volume
  let s : R ≃+ ι.range := ι.ofInjective ι_inj
  have : Countable ι.range := s.surjective.countable
  -- `twist z = stdAddChar(-zα/2) ω(n(z)) f` multiplies the Schrödinger function by
  -- `stdAddChar(z(x*x - α)/2)`.
  let twist (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) :
      𝒮 ((hyperbolicSpace E Unit).hom (stdSpace E κ)) :=
    (stdAddChar E ((2⁻¹ : E) * (realAdele z * α)))⁻¹ •
      splitWeil (hyperbolicSpace E Unit) (stdSpace E κ) (D.radicalElement 0 (realAdele z • 1), 1) f
  have h_twist (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) (x : κ → 𝔸 E) :
      mixedValue (stdSpace E κ) D (replicateCol Unit x) (twist z) =
        Ψ x * stdAddChar E ((2⁻¹ : E) * (realAdele z * (star x ⬝ᵥ x - α))) := by
    rw [← hf]
    simp [twist, homSlice_radicalElement, mul_sub, mixedValue, Circle.smul_def, trace,
      map_sub_eq_div,
      div_eq_inv_mul]
    ring
  -- The zero term of `twist z` along the line of `β` is `P (β + z)`, as `stdAddChar(βα/2) = 1`.
  have h_term (β : R) (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) :
      P (s β +ᵥ z) = (lagrangian (shearSplitting β)).zeroTerm (stdSpace E κ) (twist z) := by
    have h_shift : realAdele (s β +ᵥ z) = toAdele (β : E) + realAdele z := realAdele_add β z
    rw [hP, zeroTerm_shearSplitting (h_twist z), h_shift]
    congr with x
    simp [mul_sub, ← map_mul, ← mul_assoc, div_eq_inv_mul, add_mul, mul_add, map_sub_eq_div,
      map_add_eq_mul]
    ring
  have h_twist_int : IntegrableOn twist (Ω ×ˢ selfAdjointCodifferent E 1) μ := by
    refine IntegrableOn.mono_set ?_ (Set.prod_mono subset_closure subset_rfl)
    exact (Continuous.continuousOn (by fun_prop [realAdele])).integrableOn_compact
      (h_bdd.isCompact_closure.prod (isCompact_selfAdjointCodifferent E isUnit_one))
  obtain ⟨h_summable, hSW⟩ := siegel_weil_one_vector (E := E) h_card
  -- Unfold the integral of `P` over `R`.
  have P_meas : AEStronglyMeasurable P μ := by
    have P_eq : P = fun z ↦ (lagrangian (shearSplitting 0)).zeroTerm (stdSpace E κ) (twist z) :=
      funext fun z ↦ by simpa only [s.map_zero, zero_vadd] using h_term 0 z
    rw [P_eq]
    exact Continuous.aestronglyMeasurable (by fun_prop [realAdele])
  obtain ⟨P_int, P_unfold⟩ : Integrable P μ ∧ ∫ z, P z ∂μ =
      ∑' β : R, (lagrangian (shearSplitting β)).zeroTerm (stdSpace E κ)
        (∫ z in Ω ×ˢ selfAdjointCodifferent E 1, twist z ∂μ) :=
    integrable_and_integral_eq_tsum_of_fundamentalDomain h_fund s.toEquiv h_summable h_twist_int
      P_meas h_term
  -- By orthogonality only the rational vectors of norm `α` survive the integral over `z`.
  let g : 𝒮 ((hyperbolicSpace E Unit).hom (stdSpace E κ)) :=
    (√√|discr E| : ℂ) • ∫ z in Ω ×ˢ selfAdjointCodifferent E 1, twist z ∂μ
  have hg (ξ : κ → E) (h : G E (1 : κ → ℤˣ)) :
      mixedValue (stdSpace E κ) D (replicateCol Unit (1 *ᵥ toAdele ∘ ξ))
        (splitWeil (hyperbolicSpace E Unit) (stdSpace E κ) (1, h) g) = σ h ξ := by
    have h_selfAdjoint : star (star ξ ⬝ᵥ ξ - α) = star ξ ⬝ᵥ ξ - α := by
      simp [hα, ← star_dotProduct]
    simp_rw [one_mulVec, mixedValue_splitWeil, ← replicateCol_mulVec, g, map_smul,
      ← (mixedValue (stdSpace E κ) D _).integral_comp_comm h_twist_int, h_twist, σ,
      star_adeleMatrix_mulVec_dotProduct, ← map_sub, integral_const_mul]
    rw [smul_eq_mul, mul_left_comm, h_orth (star ξ ⬝ᵥ ξ - α) h_selfAdjoint]
    simp [sub_eq_zero]
  -- So the sum of `σ h` over the rational vectors is the theta value of `ω(1, h) g`.
  have hasSum_σ (h : G E (1 : κ → ℤˣ)) : HasSum (σ h)
      (((hyperbolicSpace E Unit).hom (stdSpace E κ)).θ
        (splitWeil (hyperbolicSpace E Unit) (stdSpace E κ) (1, h) g)) := by
    let col : (κ → E) ≃ Matrix κ Unit E :=
      ⟨replicateCol Unit, fun x ↦ xᵀ (), fun _ ↦ rfl, fun _ ↦ rfl⟩
    exact (col.hasSum_iff.2 (D.hasSum_theta_homSlice (stdSpace E κ) _)).congr_fun
      fun ξ ↦ (hg ξ h).symm
  -- The value of `g` at `0` vanishes as `α ≠ 0`, and its zero terms unfold the integral of `P`.
  have h_zero : mixedValue (stdSpace E κ) D 0 g = 0 := by
    simpa [σ, hα_ne.symm, mk_one_one] using hg 0 1
  have zero_terms : ∑' β : R, (lagrangian (shearSplitting β)).zeroTerm (stdSpace E κ) g =
      √√|discr E| * ∫ z, P z ∂μ := by simp [g, P_unfold, tsum_mul_left, R]
  simp only [(hasSum_σ _).tsum_eq]
  refine ⟨P_int, fun h ↦ (hasSum_σ h).summable, fun γ hγ h ↦ ?_, ?_⟩
  · exact (pairThetaKer (hyperbolicSpace E Unit) (stdSpace E κ) _ 1).swap.theta_rat_mul γ hγ h
  · rw [hSW g, h_zero, zero_add, zero_terms]

/-! ### The factors at the infinite places and the class sum -/

/-- The density of `Φ₀` at `α`: the condition `x* x = α` is detected by the phase
`ψ_f(z (x* x - α) / 2)`, integrated over the self-adjoint finite adeles `z`. The measure of `z`
gives the codifferent the volume `1`, and that of each coordinate of `x` gives `Ô` the volume
`volÔ E`. -/
noncomputable def New.normDensity {E κ : Type} [Field E] [CMType E] [WeilData E] [Fintype κ]
    (Φ₀ : (κ → 𝔸f E) → NNReal) (α : 𝔸f E) : ℂ :=
  ∫ z : selfAdjoint (𝔸f E), ∫ x : κ → 𝔸f E,
    (ψf E ((2⁻¹ : E) * (z.1 * (star x ⬝ᵥ x - α))) : ℂ) ∂volume.withDensity fun x ↦ Φ₀ x

/-- For every Schwartz–Bruhat function `Φ₀` on the finite vectors there is a test function `f` on
`Hom` from the hyperbolic plane to `stdSpace E κ` (the space with form x*x) with the following
property. Its value `mixedValue` at the column `x`, in the Schrödinger model attached to
`hyperbolicSplitting` (the splitting with `l` the first and `k` the second basis vector), is
`exp (-∑ᵥ (x*x)ᵥ) Φ₀(x_f)`. This is a Gaussian at infinity times `Φ₀` at the finite places. -/
lemma New.SiegelWeil.exists_mixedValue_eq_gaussian_mul {E κ : Type} [Field E] [CMType E]
    [WeilData E]
    [Fintype κ] [DecidableEq κ] {Φ₀ : (κ → 𝔸f E) → ℂ} (hΦ₀ : IsSchwartzBruhat Set.univ Φ₀) :
    ∃ f : 𝒮 ((hyperbolicSpace E Unit).hom (stdSpace E κ)), ∀ x : κ → 𝔸 E,
      mixedValue (stdSpace E κ) (hyperbolicSplitting E Unit) (replicateCol Unit x) f =
        cexp (-∑ v : InfinitePlace E, ((star x ⬝ᵥ x).1 v).re) * Φ₀ fun i : κ ↦ (x i).2 := by
  classical
  let γ (x : κ → 𝔸 E) : ℂ := cexp (-∑ v, ((star x ⬝ᵥ x).1 v).re)
  -- `S`: the functions `φ` of finite vectors such that `γ φ` is the model of some datum.
  let S : Submodule ℂ ((κ → 𝔸f E) → ℂ) :=
    .comap (.pi fun x ↦ γ (xᵀ ()) • .proj fun i ↦ (x i ()).2)
      (LinearMap.pi fun x ↦
        (mixedValue (stdSpace E κ) (hyperbolicSplitting E Unit) x).toLinearMap).range
  -- `Φ₀` is a combination of cosets, so it is enough to treat these.
  suffices coset_mem : ∀ (u : (𝔸f E)ˣ) (z : κ → 𝔸f E), cosetIndicator Set.univ u z ∈ S by
    obtain ⟨f, hf⟩ : Φ₀ ∈ S :=
      hΦ₀.mem_of_cosets S fun _ _ ↦ ⟨⊤, by simp, fun u z _ _ ↦ coset_mem u z⟩
    exact ⟨f, fun x ↦ congrFun hf (replicateCol _ x)⟩
  intro u z
  -- A coset comes from a translate of `ω g vacElem` with `g` adapted to `star t` for a scalar `t`,
  -- which is `u⁻¹` up to `WeilData.α` at the finite places and scales the vacuum to `γ` at
  -- infinity.
  obtain ⟨t, ht⟩ : IsUnit ((fun w ↦ √(2 * π * (Φ w j).im)⁻¹, (WeilData.α * u⁻¹).1) : 𝔸 E) := by
    simp [Prod.isUnit_iff, Pi.isUnit_iff, ne_of_gt, im_pos, pi_pos]
  let D := (hyperbolicSplitting E Unit).homSource (stdSpace E κ)
  obtain ⟨g, hg, -⟩ := D.exists_isAdapted_and_frame_eq (star t • 1)
  let V := (hyperbolicSpace E Unit).hom (stdSpace E κ)
  obtain ⟨c, hc, h_vac⟩ : ∃ c : ℂ, c ≠ 0 ∧ ∀ x : κ × Unit → 𝔸 E,
    Splitting.slice x (V.ω g V.vacElem) =
      (c * (‖vacuumFn ((star t • 1)ᴴ *ᵥ x)‖ : ℂ) ^ 2) •
        ((stdSpace E Empty).hom (stdSpace E κ)).vacElem :=
    hg.slice_omega_vacElem
  refine ⟨c⁻¹ • ϱ _ (D.lAdelic *ᵥ fun i ↦ (0, -z i.1)) (ω _ g (vacElem _)), funext fun x ↦ ?_⟩
  -- The source term is the mixed term at `x` read as a vector, which `h_vac` evaluates.
  have h_source : (hyperbolicSplitting E Unit).homSlice (stdSpace E κ) x =
      D.slice (matrixToVec x) := by
    simpa using (hyperbolicSplitting E Unit).homSlice_eq_slice (stdSpace E κ) x
  suffices h_norm : (‖vacuumFn (t • (matrixToVec x + fun i ↦ (0, -z i.1)))‖ : ℂ) ^ 2 *
        ((stdSpace E Empty).hom (stdSpace E κ)).vacElem 0 =
      γ (xᵀ ()) * cosetIndicator Set.univ u z fun i ↦ (x i ()).2 by
    simpa [h_source, D, V, h_vac, mixedValue, smul_mulVec, hc, mul_assoc] using h_norm
  -- The vacuum is the indicator of `Ô` at the finite places and a Gaussian at infinity.
  simp [ht, vacElem_apply_eq_prod_lineTheta, γ, vacuumFn, mem_integralBox, matrixToVec,
    apply_ite norm,
    mul_assoc, sub_eq_add_neg, mul_pow, ne_of_gt, ← ofReal_pow, ← Real.exp_nat_mul, dotProduct,
    sum_comm (γ := κ), sum_prod_type, Unique.forall_iff, Units.smul_def, im_pos, le_of_lt, pi_pos,
    Complex.exp_neg, mul_add, mul_sum, norm_exp, Circle.norm_coe, funext_iff, fst_sum,
    conj_mul']
  split_ifs
  · simp [univ_eq_empty]
  · simp

/-- Laplace's integral for 1/Γ: for an integer k ≥ 1 and real x ≥ 0, the integral over real z of
e^{2πixz} (1 + 2πiz)^{−(k+1)} equals x^k e^{−x} / k!. -/
lemma New.integral_fourierChar_mul_inv_pow {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    ∫ z : ℝ, 𝐞 (x * z) * ((1 + 2 * π * Complex.I * z : ℂ) ^ (k + 1))⁻¹ =
      x ^ k * cexp (-x) / k ! := by
  -- The function `g` is the Fourier transform of the density `p` (`laplace_pow`); invert.
  let g (z : ℝ) : ℂ := ((1 + 2 * π * .I * z) ^ (k + 1))⁻¹
  let p (t : ℝ) : ℂ := toNNReal t ^ k * cexp (-t) / k.factorial
  have hg : g = 𝓕 p := by
    ext z
    calc g z = (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ k * cexp (-(1 + 2 * π * .I * z) * t)) / k ! := by
          rw [laplace_pow (by simp) k, div_div_cancel_left' (mod_cast k.factorial_ne_zero)]
      _ = 𝓕 p z := by
          rw [fourier_eq', ← integral_div, ← integral_indicator measurableSet_Ioi]
          congr with t
          rcases lt_or_ge 0 t with ht | ht
          · simp [p, ht, ht.le, Complex.exp_add, add_mul, Complex.exp_neg]
            ring_nf
          · simp [p, ht, Nat.one_le_iff_ne_zero.mp hk]
  -- The density is integrable because its integral `g 0 = 1` is not zero.
  have h_ne : 𝓕 p 0 ≠ 0 := by simp [← hg, g]
  have p_int : Integrable p := .of_integral_ne_zero (by simpa [fourier_eq] using h_ne)
  -- As `k + 1 ≥ 2`, we have `‖g z‖ ≤ (1 + (2 π z) ^ 2)⁻¹`.
  have h_norm (z : ℝ) : ‖g z‖ ≤ (1 + (2 * π * z) ^ 2)⁻¹ := calc
    ‖g z‖ = (√(1 + (2 * π * z) ^ 2) ^ (k + 1))⁻¹ := by simp [g, norm_eq_sqrt_sq_add_sq]
    _ ≤ (√(1 + (2 * π * z) ^ 2) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by simp [sq_nonneg]) (Nat.succ_le_succ hk))
    _ = (1 + (2 * π * z) ^ 2)⁻¹ := by rw [Real.sq_sqrt (by positivity)]
  have g_int : Integrable g := (integrable_inv_one_add_sq.comp_mul_left' two_pi_pos.ne').mono'
    (by fun_prop) (.of_forall h_norm)
  have h_inv : 𝓕⁻ g x = p x := by
    rw [hg, p_int.fourierInv_fourier_eq (by rwa [← hg]) (by fun_prop)]
  simpa [fourierInv_eq, hx, g, p, Circle.smul_def] using h_inv

/-- For `n ≥ 2` and `a ≥ 0`, the integral over real `t` of `𝐞 (a t)` times the `n`-th power of the
Gaussian integral `∫_ℂ exp (-(1 + 2πit) |w|²) dw` is `πⁿ aⁿ⁻¹ e^(-a) / (n-1)!`, by Laplace's
integral for 1/Γ. This is Fourier inversion for the fiber integrals of `exp (-x* x)` on `ℂⁿ`: the
sphere `x* x = a` has the mass `πⁿ aⁿ⁻¹ / (n-1)!` for the measure `dx / d(x* x)`. -/
lemma New.integral_fourierChar_mul_gaussian_pow {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 ≤ a) :
    ∫ t : ℝ, 𝐞 (a * t) * (∫ w : ℂ, cexp (-(1 + 2 * π * Complex.I * t) * ‖w‖ ^ 2)) ^ n =
      π ^ n / (n - 1)! * a ^ (n - 1) * cexp (-a) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have h_gauss (t : ℝ) : ∫ w : ℂ, cexp (-(1 + 2 * π * Complex.I * t) * ‖w‖ ^ 2) =
      π * (1 + 2 * π * Complex.I * t)⁻¹ := by
    rw [integral_cexp_neg_mul_sq_norm (by simp)]
    simp [division_def]
  simp_rw [h_gauss, mul_pow, inv_pow, mul_left_comm _ ((π : ℂ) ^ (k + 1)), integral_const_mul,
    integral_fourierChar_mul_inv_pow (show 1 ≤ k by omega) ha, Nat.add_sub_cancel]
  ring

/-- By Fubini, the integral over the adelic vectors `x` of the Gaussian times `Φ₀`, twisted by the
phase `ψ (z (x* x - α) / 2)`, with `ψ = stdAddChar E` and `z` read as an adele by `realAdele` (real
components at the infinite places, `z.2` at the finite ones), is the product over the real
components `t` of `z` of `𝐞 (α t)` times a Gaussian integral over `ℂⁿ`, times the integral over the
finite adelic vectors. Here `α` at an infinite place `v` is read as the real part of its embedding
`Φ v α` of the CM type. -/
lemma New.integral_gaussian_mul_stdAddChar {E κ : Type} [Field E] [CMType E] [WeilData E]
    [Fintype κ] (Φ₀ : LocallyConstant (κ → 𝔸f E) NNReal) (α : E)
    (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) :
    ∫ x : κ → 𝔸 E, cexp (-∑ v : InfinitePlace E, ((star x ⬝ᵥ x).1 v).re) *
        Φ₀ (fun i : κ ↦ (x i).2) *
        stdAddChar E ((2⁻¹ : E) * (realAdele z * (star x ⬝ᵥ x - α))) =
      (∏ v : InfinitePlace E, 𝐞 ((Φ v α).re * z.1 v) *
          (∫ w : ℂ, cexp (-(1 + 2 * π * Complex.I * z.1 v) * ‖w‖ ^ 2)) ^ card κ) *
        ∫ x : κ → 𝔸f E, (ψf E ((2⁻¹ : E) * (z.2.1 * (star x ⬝ᵥ x - α))) : ℂ)
          ∂volume.withDensity fun x : κ → 𝔸f E ↦ Φ₀ x := by
  -- Both sides are one integral over the vectors of pairs (infinite part, finite part).
  have h_infinite : ∏ v : InfinitePlace E, 𝐞 ((Φ v α).re * z.1 v) *
        (∫ w : ℂ, cexp (-(1 + 2 * π * Complex.I * z.1 v) * ‖w‖ ^ 2)) ^ card κ =
      ∫ y : κ → InfinitePlace E → ℂ, (∏ v, (𝐞 ((Φ v α).re * z.1 v) : ℂ)) *
        ∏ i, ∏ v, cexp (-(1 + 2 * π * Complex.I * z.1 v) * ‖y i v‖ ^ 2) := by
    rw [prod_mul_distrib, prod_pow, ← integral_fintype_prod_volume_eq_prod,
      ← integral_fintype_prod_volume_eq_pow, ← integral_const_mul]
  rw [h_infinite, integral_withDensity_eq_integral_smul Φ₀.continuous.measurable,
    ← integral_prod_mul, ← Measure.volume_eq_prod,
    ← (volume_measurePreserving_arrowProdEquivProdArrow ..).integral_comp']
  congr with x
  simp [MeasurableEquiv.arrowProdEquivProdArrow, dotProduct, stdAddChar, realAdele, map_ofNat,
    fourierChar, ← Complex.exp_add, ← Complex.exp_sum, mul_mul_mul_comm _ (Φ₀ _ : ℂ),
    sum_comm (γ := κ), ← ofReal_pow, sum_mul, ← sum_neg_distrib, ← sum_add_distrib,
    NNReal.smul_def, fst_sum, conj_mul', mul_sum, snd_sum]
  -- It remains to compare the exponents at each infinite place.
  refine .inl (congrArg cexp ?_)
  simp only [ofReal_pow]
  congr with v
  simp [← mul_sum]
  ring

/-- Let `c` be a function on the finite unitary group `Gf E κ` of x*x that is right invariant under
a level `K` (an open subgroup of the stabilizer `K₀` of the standard lattice) and, read on the
adelic group, left invariant under the rational points `Γ`. Its class sum is the index
`stdLevelIndex K = [K₀ : K]` times its integral over the adelic quotient, for the measure
`quotMeasure`. -/
lemma New.classSum_eq_mul_integral {E κ : Type} [Field E] [CMType E] [Fintype κ] [DecidableEq κ]
    (K : Subgroup (Gf E κ)) [hK : IsLevel K] {c : Gf E κ → ℝ}
    (left : (stdSpace E κ).Γ.FixesLeft fun h : G E 1 ↦ c h.2)
    (right : ∀ k ∈ K, ∀ x : Gf E κ, c (x * k) = c x) :
    classSum stdRatPoints K c =
      stdLevelIndex K * ∫ x : G E 1, c x.2 ∂(stdSpace E κ).quotMeasure := by
  have h_level : K ≤ rightStabilizer c := right
  have h_left : (stdSpace E κ).Γf.FixesLeft c := by
    rintro _ ⟨γ, rfl⟩ g
    exact left _ ⟨γ, rfl⟩ (1, g)
  rw [← classIntegral_eq_classSum h_level]
  exact Space.classIntegral_eq_integral ⟨h_left, Subgroup.isOpen_mono h_level hK.isOpen⟩ K

open scoped Classical in
/-- **Vectors of one norm.** Let `n = card κ ≥ 3`, let `K` be a level (an open subgroup of the
stabilizer of `Ôⁿ` in the finite adelic unitary group), `Φ₀ ≥ 0` locally constant, `K`-invariant and
of compact support, and `α ∈ E⁺` totally positive. The sum of `Φ₀(h⁻¹ x)` over the `x ∈ Eⁿ` with
`x* x = α` converges. Its class sum of level `K` (the sum over the classes, weighted by the inverse
orders of their automorphism groups) is the class sum of `1` times `|D_E|^(1/4)`, times the factors
`πⁿ τ(α)^(n-1) / (n-1)!` over the infinite places (where `τ = Φ v` is the embedding of the CM type
at the place `v`), times the density `New.normDensity` of `Φ₀` at `α`. That density is the integral
of `Φ₀(x) ψ_f(z (x* x - α) / 2)` over the finite vectors `x` and the self-adjoint finite adeles `z`,
with the codifferent of volume `1` and `Ô` of volume `volÔ E`.

This is Siegel's formula for the mean number of vectors of given norm (Weil's Siegel–Weil formula
for one vector, value by value), for the definite form `x* x` of rank at least 3 over a CM field. -/
lemma New.classSum_eq_mul_normDensity {E κ : Type} [Field E] [CMType E] [WeilData E] [Fintype κ]
    [DecidableEq κ] (h_card : 3 ≤ card κ) (K : Subgroup (Gf E κ)) [hK : IsLevel K]
    (Φ₀ : LocallyConstant (κ → 𝔸f E) NNReal)
    (hΦ₀_inv : ∀ k ∈ K, ∀ x : κ → 𝔸f E, Φ₀ ((k : Matrix κ κ (𝔸f E)) *ᵥ x) = Φ₀ x)
    (hΦ₀ : HasCompactSupport Φ₀) {α : E} (hα : star α = α)
    (hα_pos : ∀ v : InfinitePlace E, 0 < (Φ v α).re) :
    let σ (h : Gf E κ) (x : κ → E) : NNReal :=
      if star x ⬝ᵥ x = α then
        Φ₀ (((h⁻¹ : Gf E κ) : Matrix κ κ (𝔸f E)) *ᵥ fun i : κ ↦ (x i : 𝔸f E))
      else 0
    (∀ h : Gf E κ, Summable (σ h)) ∧
    ((classSum stdRatPoints K fun h : Gf E κ ↦ (∑' x : κ → E, σ h x : NNReal) : ℝ) : ℂ) =
      (classSum stdRatPoints K 1 * √√|NumberField.discr E| *
        ∏ v : InfinitePlace E,
          π ^ card κ / (card κ - 1)! * (Φ v α).re ^ (card κ - 1) : ℝ) *
        normDensity Φ₀ α := by
  -- Take the Fourier coefficient at `α` of the Siegel–Weil formula for one vector, applied to `Φ₀`
  -- times the Gaussian, and compute the integrals at the real places.
  intro σ
  have hΦ₀_sb : IsSchwartzBruhat Set.univ fun x : κ → 𝔸f E ↦ ((Φ₀ x : NNReal) : ℂ) :=
    { idem_smul := by simp
      locally_constant := Φ₀.isLocallyConstant.comp fun t : NNReal ↦ (t : ℂ)
      compact_support := ⟨tsupport Φ₀, hΦ₀, fun x hx ↦ subset_tsupport Φ₀ (by simpa using hx)⟩ }
  let Ψ (x : κ → 𝔸 E) : ℂ :=
    cexp (-∑ v : InfinitePlace E, ((star x ⬝ᵥ x).1 v).re) * Φ₀ fun i : κ ↦ (x i).2
  -- `Ψ` is the Schrödinger function of a datum `f`.
  obtain ⟨f, hf⟩ : ∃ f : 𝒮 ((hyperbolicSpace E Unit).hom (stdSpace E κ)), ∀ x : κ → 𝔸 E,
      mixedValue (stdSpace E κ) (hyperbolicSplitting E Unit) (replicateCol Unit x) f = Ψ x :=
    exists_mixedValue_eq_gaussian_mul hΦ₀_sb
  -- The integral over `x` is the product `P` of real factors `gauss v` and of `F`.
  let F (z : selfAdjoint (𝔸f E)) : ℂ := ∫ x : κ → 𝔸f E,
    (ψf E ((2⁻¹ : E) * (z.1 * (star x ⬝ᵥ x - α))) : ℂ) ∂volume.withDensity fun x ↦ Φ₀ x
  let gauss (v : InfinitePlace E) (t : ℝ) : ℂ :=
    𝐞 ((Φ v α).re * t) * (∫ w : ℂ, cexp (-(1 + 2 * π * .I * t) * ‖w‖ ^ 2)) ^ card κ
  let P (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) : ℂ := (∏ v, gauss v (z.1 v)) * F z.2
  have hP (z : (InfinitePlace E → ℝ) × selfAdjoint (𝔸f E)) : P z =
      ∫ x : κ → 𝔸 E, Ψ x * stdAddChar E ((2⁻¹ : E) * (realAdele z * (star x ⬝ᵥ x - α))) :=
    (integral_gaussian_mul_stdAddChar Φ₀ α z).symm
  have hα_ne : α ≠ 0 := fun h ↦ by simp [h] at hα_pos
  obtain ⟨-, h_summable, h_left, h_mean⟩ := siegel_weil_fourierCoeff h_card f hf hα hα_ne hP
  -- On the vectors of norm `α` the Gaussian is the constant `c`.
  let c : ℂ := cexp (-∑ v : InfinitePlace E, (Φ v α).re)
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have h_value (h : G E (1 : κ → ℤˣ)) (ξ : κ → E) :
      (if star ξ ⬝ᵥ ξ = α then Ψ (h⁻¹.adeleMatrix *ᵥ toAdele ∘ ξ) else 0) = c * σ h.2 ξ := by
    have h_finite : (fun i : κ ↦ ((h⁻¹.adeleMatrix *ᵥ toAdele ∘ ξ) i).2) =
        ↑(h.2⁻¹ : Gf E κ) *ᵥ fun i : κ ↦ (ξ i : 𝔸f E) :=
      funext fun i ↦ by simp [mulVec, dotProduct, snd_sum]
    by_cases hξ : star ξ ⬝ᵥ ξ = α
    · simp only [Ψ, star_adeleMatrix_mulVec_dotProduct, h_finite]
      simp [hξ, c, σ]
    · simp [hξ, σ]
  have σ_summable (h : G E (1 : κ → ℤˣ)) : Summable fun ξ : κ → E ↦ (σ h.2 ξ : ℂ) := by
    simpa only [h_value, summable_mul_left_iff hc] using h_summable h
  refine ⟨fun h ↦ mod_cast σ_summable (1, h), ?_⟩
  let C : ℝ := ∏ v : InfinitePlace E, π ^ card κ / (card κ - 1)! * (Φ v α).re ^ (card κ - 1)
  -- `∫ gauss v` is `πⁿ` times Laplace's integral with `k = n - 1` at `(Φ v α).re`.
  have h_real : ∫ z, P z ∂volume.prod volume = c * (C * normDensity Φ₀ α) := by
    have h_gauss (v : InfinitePlace E) : ∫ t, gauss v t =
        π ^ card κ / (card κ - 1)! * (Φ v α).re ^ (card κ - 1) * cexp (-(Φ v α).re) :=
      integral_fourierChar_mul_gaussian_pow (by omega) (hα_pos v).le
    rw [normDensity, integral_prod_mul (fun z : InfinitePlace E → ℝ ↦ ∏ v, gauss v (z v)) F,
      integral_fintype_prod_volume_eq_prod]
    simp [h_gauss, c, C, prod_mul_distrib, ← Complex.exp_sum]
    ring
  have h_int : ∫ h : G E (1 : κ → ℤˣ), ∑' ξ : κ → E, (σ h.2 ξ : ℂ) ∂(stdSpace E κ).quotMeasure =
      (stdSpace E κ).quotMeasure.real Set.univ * (√√|discr E| * (C * normDensity Φ₀ α)) := by
    simp only [h_value, tsum_mul_left, integral_const_mul] at h_mean
    rwa [h_real, mul_left_comm _ c, mul_left_comm _ c, mul_right_inj' hc] at h_mean
  -- Class sums are integrals over the quotient, up to the index of `K`.
  have h_coe (h : Gf E κ) : ((∑' ξ : κ → E, σ h ξ : NNReal) : ℂ) = ∑' ξ : κ → E, (σ h ξ : ℂ) := by
    norm_cast
  have sum_left : (stdSpace E κ).Γ.FixesLeft fun h : G E (1 : κ → ℤˣ) ↦
      ((∑' ξ : κ → E, σ h.2 ξ : NNReal) : ℝ) := fun γ₀ hγ₀ h ↦ by
    simpa only [← ofReal_inj, h_coe, h_value, tsum_mul_left, mul_right_inj' hc]
      using h_left γ₀ hγ₀ h
  have σ_right (k : Gf E κ) (h_mem : k ∈ K) (h : Gf E κ) : σ (h * k) = σ h := by
    have h_inv (x : κ → 𝔸f E) : Φ₀ ((k : Matrix κ κ (𝔸f E))⁻¹ *ᵥ x) = Φ₀ x := by
      simpa using hΦ₀_inv k⁻¹ (K.inv_mem h_mem) x
    simp [← mulVec_mulVec, σ, h_inv, Matrix.mul_inv_rev]
  have sum_right (k : Gf E κ) (h_mem : k ∈ K) (h : Gf E κ) :
      ((∑' ξ : κ → E, σ (h * k) ξ : NNReal) : ℝ) = (∑' ξ : κ → E, σ h ξ : NNReal) := by
    rw [σ_right k h_mem h]
  rw [classSum_eq_mul_integral K sum_left sum_right,
    classSum_eq_mul_integral K (c := 1) (by simp) (by simp)]
  simp [← integral_complex_ofReal, h_coe, h_int, C, mul_assoc]

end OneVector

/-! ## Estimate for the ratio of consecutive masses -/

section MassRatio

open NumberField Real MeasureTheory Set New stdLattice Matrix

/-- Siegel's formula for the vectors of norm `1` in `L = Ô^(j+1)`, `j ≥ 2`: `mass_j` is `mass_{j+1}`
times `|D_E|^(1/4) (π^(j+1) / j!)^f` times the density of the indicator of `L` at `1` (see
`New.normDensity`). Here `mass_j` is the mass of the genus of `O_E^j`, `f` is the number of
infinite places and `rd_E` the root discriminant, so `|D_E| = (rd_E^f)²`. -/
lemma New.mass_eq_mass_succ_mul_normDensity (E : Type) [Field E] [CMType E] [WeilData E] {j : ℕ}
    (hj : 2 ≤ j) :
    (mass E j : ℂ) = mass E (j + 1) * √√((rootDiscr E ^ Core.numInfPlaces E) ^ 2) *
      (π ^ (j + 1) / j.factorial) ^ Core.numInfPlaces E *
      normDensity ((stdLattice E (Fin j ⊕ Unit) : Set (Fin j ⊕ Unit → 𝔸f E)).indicator 1) 1 := by
  classical
  let L : Set (Fin j ⊕ Unit → 𝔸f E) := stdLattice E (Fin j ⊕ Unit)
  let χ : LocallyConstant (Fin j ⊕ Unit → 𝔸f E) NNReal :=
    LocallyConstant.indicator 1 (U := L) ⟨isCompact_stdLattice.isClosed, isOpen_stdLattice⟩
  have h_inv : ∀ k ∈ stdLevel E (Fin j ⊕ Unit), ∀ y : Fin j ⊕ Unit → 𝔸f E, χ (↑k *ᵥ y) = χ y :=
    fun _ hk _ ↦ if_congr (mulVec_mem_intVectors_iff hk) rfl rfl
  have h_card : 3 ≤ Fintype.card (Fin j ⊕ Unit) := by simpa using Nat.succ_le_succ hj
  have h_compact : HasCompactSupport χ := .intro isCompact_stdLattice fun _ h ↦ ite_eq_right h
  obtain ⟨-, formula⟩ := classSum_eq_mul_normDensity h_card (stdLevel E (Fin j ⊕ Unit)) χ h_inv
    h_compact
    (star_one E) (by simp)
  -- The two class sums are `mass E j` and `mass E (j + 1)`; write the number of vectors of norm
  -- `1` as a sum to match the left side.
  have count (s : Set (Fin j ⊕ Unit → E)) : (s.ncard : ℝ) = ∑' x, s.indicator 1 x :=
    .trans (by simp) (tsum_subtype s 1)
  have h_classSum : classSum stdRatPoints (stdLevel E (Fin j ⊕ Unit))
    (fun h ↦ ↑(∑' x : Fin j ⊕ Unit → E,
      if star x ⬝ᵥ x = 1 then χ (↑(h⁻¹ : Gf E (Fin j ⊕ Unit)) *ᵥ fun i ↦ x i) else 0)) =
      mass E j := by
    simpa [χ, L, normOneLatticeVectors, Function.comp_def, count, indicator, apply_ite,
      NNReal.coe_tsum, coe_stdLattice, ← ite_and] using classSum_card_norm_one_eq_mass E j
  rw [h_classSum, show ⇑χ = L.indicator 1 from rfl] at formula
  simpa [L, classSum_stdRatPoints_eq_mass, abs_discr_eq_rootDiscr_pow, div_pow] using formula

/-- The density of the indicator of `L = Ôⁿ` at `1` (`New.normDensity`) is close to
`vol L = volÔ E ^ n`, with `volÔ E` the measure of `Ô`: if it is `x · vol L ≠ 0`, then
`|x - 1| ≤ 2^(-u-1)`, for `n ≥ 4 u + 12` and `8 f ≤ 2^u`, with `f` the number of infinite
places. -/
lemma New.norm_sub_one_le_of_normDensity_eq {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] {u : ℕ} (hu : 8 * Core.numInfPlaces E ≤ 2 ^ u) (hn : 4 * u + 12 ≤ Fintype.card n)
    {x : ℂ} (x_ne : x ≠ 0)
    (hx : normDensity ((stdLattice E n : Set (n → 𝔸f E)).indicator 1) 1 =
      x * volÔ E ^ Fintype.card n) :
    ‖x - 1‖ ≤ (2 ^ (u + 1))⁻¹ := by
  -- The density is `∫ F`, where `F z` is the Gauss sum of `L` at `z`.
  let F (z : selfAdjoint (𝔸f E)) : ℂ := ∫ y in (stdLattice E n : Set (n → 𝔸f E)),
    (ψf E ((2⁻¹ : E) * (z.1 * (star y ⬝ᵥ y - 1))) : ℂ)
  have h_integral : ∫ z, F z = x * volÔ E ^ Fintype.card n := by
    rw [← hx, normDensity]
    have h_density : (fun y : n → 𝔸f E ↦
        (((stdLattice E n : Set (n → 𝔸f E)).indicator 1 y : NNReal) : ENNReal)) =
        (stdLattice E n : Set (n → 𝔸f E)).indicator 1 :=
      funext (ENNReal.coe_indicator _ _)
    rw [h_density, withDensity_indicator_one isOpen_stdLattice.measurableSet]
  have F_int : Integrable F := .of_integral_ne_zero (by simp [h_integral, x_ne])
  let C : Set (selfAdjoint (𝔸f E)) := selfAdjointCodifferent E 1
  have meas : MeasurableSet C := (isOpen_selfAdjointCodifferent E 1).measurableSet
  -- The Gauss sum bound `∫ ‖F‖ ≤ ζ(2u + 5) vol L`, where `ζ(2u + 5) ≤ 1 + 2⁻¹ ^ (u + 1)` by `hu`.
  have zeta : idealZeta (Ô E) (u + 1 + u + 4) ^ 1 ≤ .ofReal (1 + 2⁻¹ ^ (u + 1)) :=
    idealZeta_intAdeles_pow_le (u + 1) (by grind [finrank_eq_two_mul_card_infinitePlace])
  have gauss : ∫⁻ z, ‖F z‖ₑ ≤ idealZeta (Ô E) (u + 1 + u + 4) * volÔ E ^ Fintype.card n :=
    lintegral_gauss_sum_le_idealZeta (le_two_of_pow_le_ofReal zeta) (by omega) 1
  -- On `C`, of measure `1`, the character is trivial on `L`, so `F = vol L` there:
  -- `y* y - 1 = t + t̄` with `t = (y* y - 1) * traceOneAdele` integral, and
  -- `ψf E ((w + w̄) / 2) = ψf E w` (`ψf_inv_two_mul_add_star`) for `w = z t`.
  have main : ∫ z in C, F z = volÔ E ^ Fintype.card n := by
    have F_eq (z : selfAdjoint (𝔸f E)) (hz : z ∈ C) :
        F z = ∫ _ in (stdLattice E n : Set (n → 𝔸f E)), ((1 : Circle) : ℂ) := by
      refine setIntegral_congr_fun isOpen_stdLattice.measurableSet fun y hy ↦ congrArg _ ?_
      have ht : (star y ⬝ᵥ y - 1) * traceOneAdele ∈ Ô E :=
        mul_mem (sub_mem (star_dotProduct_mem hy hy) (one_mem _)) traceOneAdele_mem
      simpa [← mul_add, ← star_dotProduct] using (ψf_inv_two_mul_add_star _).trans (hz _ ht)
    simpa [C, coe_stdLattice, volume_pi_pi, Measure.real] using
      setIntegral_congr_fun (μ := volume) meas F_eq
  -- The part of `∫ F` off `C` is `(x - 1) vol L`; in `gauss` the part on `C` uses up `vol L`.
  have h_compl : ∫ z in Cᶜ, F z = (x - 1) * volÔ E ^ Fintype.card n := by
    rw [setIntegral_compl meas F_int, h_integral, main, sub_one_mul]
  have h_bound : ‖∫ z in C, F z‖ₑ + ‖∫ z in Cᶜ, F z‖ₑ ≤
      .ofReal (1 + 2⁻¹ ^ (u + 1)) * volÔ E ^ Fintype.card n :=
    calc ‖∫ z in C, F z‖ₑ + ‖∫ z in Cᶜ, F z‖ₑ ≤ (∫⁻ z in C, ‖F z‖ₑ) + ∫⁻ z in Cᶜ, ‖F z‖ₑ :=
        add_le_add (enorm_integral_le_lintegral_enorm _) (enorm_integral_le_lintegral_enorm _)
      _ = ∫⁻ z, ‖F z‖ₑ := lintegral_add_compl _ meas
      _ ≤ .ofReal (1 + 2⁻¹ ^ (u + 1)) * volÔ E ^ Fintype.card n := by
        grw [gauss, ← zeta, pow_one]
  rw [main, h_compl] at h_bound
  have rd_pos : 0 < rootDiscr E := rootDiscr_pos E
  simpa (disch := finiteness) [rd_pos, abs_of_pos, volÔ_eq, ← ENNReal.toReal_le_toReal,
    ENNReal.toReal_add, add_mul] using h_bound

/-- **Masses.** The logarithm of `mass_{j+1} / mass_j`, the ratio of the masses of the genera of
`O_E^(j+1)` and `O_E^j`, is `f log (rd_E^(j+1/2) j! / (2π)^(j+1))` up to `2 / 2^u`, for
`j ≥ 4 u + 12` and `8 f ≤ 2^u`. Here `f` is the number of infinite places and `rd_E` the root
discriminant. This is an approximate form of the mass formula for unitary groups (Shimura 1997). -/
lemma New.abs_log_mass_ratio_sub_le (E : Type) [Field E] [CMType E] [WeilData E] (j u : ℕ)
    (hu : 8 * Core.numInfPlaces E ≤ 2 ^ u) (hj : 4 * u + 12 ≤ j) :
    |log (mass E (j + 1)) - log (mass E j) - Core.numInfPlaces E *
      ((j + 1 / 2) * log (rootDiscr E) + log j.factorial - (j + 1) * log (2 * π))| ≤
      2 / 2 ^ u := by
  have rd_pos : 0 < rootDiscr E := rootDiscr_pos E
  have mass_succ : 0 < mass E (j + 1) := mass_pos E (j + 1)
  -- Write the density as `x · vol L`; it is not zero, as `mass E j ≠ 0`.
  obtain ⟨x, hx⟩ : ∃ x : ℂ, x * volÔ E ^ Fintype.card (Fin j ⊕ Unit) =
      normDensity ((stdLattice E (Fin j ⊕ Unit) : Set (Fin j ⊕ Unit → 𝔸f E)).indicator 1) 1 :=
    mul_right_surjective₀ (by simp) _
  have siegel : (mass E j : ℂ) = mass E (j + 1) * √√((rootDiscr E ^ Core.numInfPlaces E) ^ 2) *
      (π ^ (j + 1) / j.factorial) ^ Core.numInfPlaces E *
      (x * volÔ E ^ Fintype.card (Fin j ⊕ Unit)) := by
    rw [hx, mass_eq_mass_succ_mul_normDensity E (by omega : 2 ≤ j)]
  have x_ne : x ≠ 0 := fun h ↦ (mass_pos E j).ne' (by simpa [h] using siegel)
  have near : ‖x - 1‖ ≤ (2 ^ (u + 1))⁻¹ :=
    norm_sub_one_le_of_normDensity_eq hu (by simpa using hj.trans j.le_succ) x_ne hx.symm
  -- Take logarithms in Siegel's formula, with `vol L = ((rootDiscr E / 2) ^ f)⁻¹ ^ (j + 1)`: the
  -- difference in the claim is `-log ‖x‖`.
  have h_diff : log (mass E (j + 1)) - log (mass E j) - Core.numInfPlaces E *
      ((j + 1 / 2) * log (rootDiscr E) + log j.factorial - (j + 1) * log (2 * π)) = -log ‖x‖ := by
    have h_log : log ‖(mass E j : ℂ)‖ = log ‖(mass E (j + 1) : ℂ) *
        √√((rootDiscr E ^ Core.numInfPlaces E) ^ 2) *
        (π ^ (j + 1) / j.factorial) ^ Core.numInfPlaces E *
        (x * volÔ E ^ Fintype.card (Fin j ⊕ Unit))‖ := by
      rw [← siegel]
    simp (disch := positivity) [volÔ_eq, abs_of_pos, log_mul, log_div, log_sqrt] at h_log ⊢
    linarith
  -- Finally `|log ‖x‖| ≤ 3 / 2 * ‖x - 1‖`, as `‖x - 1‖ ≤ 1 / 2`.
  have half : ‖x - 1‖ ≤ 1 / 2 := near.trans (by simp [field, pow_succ, one_le_pow₀])
  rw [h_diff, abs_neg]
  calc |log ‖x‖| = |(Complex.log (1 + (x - 1))).re| := by rw [add_sub_cancel, Complex.log_re]
    _ ≤ 3 / 2 * ‖x - 1‖ :=
      (Complex.abs_re_le_norm _).trans (Complex.norm_log_one_add_half_le_self half)
    _ ≤ 4 * (2 ^ (u + 1))⁻¹ := mul_le_mul (by norm_num) near (norm_nonneg _) (by norm_num)
    _ = 2 / 2 ^ u := by ring

end MassRatio
