import New.Derivatives.Vacuum.JetIntegrality
import New.Derivatives.Vacuum.ShortVectors

/-!
# Standard data as products of theta functions of the curve

* `New.IsTightFrame.isResolution`: a tight frame of length `b²` gives a resolution of the identity
  on `Eⁿ`.
* `New.CMLattice.exists_prod_twistedTranslate_eq_thetaProd_mul`: a product of translates of `θ` by
  `δ`-division points, taken at `δ̄ z`, is a power of a product of copies of `θ` times an integral
  series.
* `New.Parameters.exists_isVacuumExpansion`: the integral vacuum is an integral combination of
  translates of a vector whose theta function is a product of copies of `θ` along a tight frame;
  `New.Parameters.IsVacuumExpansion` collects the properties of this expansion.
* `New.Parameters.exists_jetSeries_map_eq_thetaProd_pow_mul`: the theta function of standard data of
  level `δ ≠ 0`, taken at `δ̄ (√(2π / √d) / Ω₀) z` with `d` and `Ω₀` as below, is the power `δ δ̄`
  of the product of `θ` along a resolution of the identity times an integral series in the
  parameters of these copies.

Standard data are integral combinations of translates of the integral vacuum. The proof has three
steps. Fourier inversion writes the integral vacuum through the translates of one product of copies
of `θ`, with a denominator prime to `p`. A translate of this product is a product of translates.
Each translated factor falls under the integrality principle on one curve.

Notions from other files:
* `finiteImage x` is the finite adelic vector `α⁻¹ x` of a rational vector `x`, where `α` is the
  idele of the Weil data of `E`; its coordinates lie in `Ô E` exactly when those of `x` lie in the
  lattice `𝔞₀ = E ∩ α Ô`.
* `V.ϱ (finVec x)` is the Heisenberg translation of `𝒮 V` by the finite adelic vector `α x`, called
  the translation by `x` below, and `V.finHeisenbergOp x` is this translation times a root of unity.
* `intVacuum V`, the integral vacuum, is the vacuum `V.vacElem` (a Gaussian times the signed
  indicator of the standard lattice) times a fixed power of the vacuum scale of the parameters.
* `daggerForms u` are the linear forms `u_j† z` read in `ℂ_p`, and `C.thetaProd μ m` is the product
  `∏ θ(μ_j z) ^ m j` of copies of the theta function of the curve `C`.
* `V.jetSeries c f` is the Taylor series of the theta function of `f` in Fock's coordinates, taken
  at `c z`. Here `P.areaScale` is the number `√(2π / √d)`, where `K = ℚ(√-d)`, and `P.cmPeriod` is
  the fixed period `Ω₀` of `K`: the lattice of the curve `P.cmCurve` is `Ω₀ 𝓞_K`. The factor
  `P.areaScale / P.cmPeriod` passes from Fock's coordinates to those of the curve
  `ℂ / cmPeriod 𝓞_K`.
* `finiteImage id a ∈ Ô E` says that the element `a` of `E` lies in `𝔞₀`; `Φ τ` is the complex
  embedding of the infinite place `τ` in the CM type.
* `IsTightFrame w m M` says that the `w i` lie in `𝔞₀` and that the matrix
  `(∑ m i τ(w i) conj σ(w i))`, indexed by infinite places `τ` and `σ`, is `M` times the identity.
  The number `M` is called the length of the frame.
* `V : Space E n ε` is a hermitian space of rank `n` with signs `ε` at the infinite places, together
  with an adelic point, `𝒮 V` is its Weil model, `V.θ` the theta functional on it, and
  `V.finitePart` the span of the images of the vacuum under the operators `V.finHeisenbergOp x`.
* `taylorVia ιₚ f` is the Taylor series of `f` at `0` read in `ℂ_p`, and `linearSeries μ` the linear
  form `μ` as a power series. `C.twistedTranslate k a f` is the translate of `f`, of weight `k`, by
  `a` times the factor that keeps it a theta function.
-/

open NumberField ComplexConjugate

namespace New

section Frames
variable {E I n : Type} [DecidableEq n] [Field E] [CMType E]

/-- The vectors `w i / ν`, placed in each copy of `E` in `Eⁿ`: the vector of index `(i, c)` has
`w i / ν` in the coordinate `c` and `0` elsewhere. -/
noncomputable def resolutionVectors (w : I → E) (ν : ℕ) (j : I × n) : n → E :=
  Pi.single j.2 (w j.1 / ν)

/-- The linear form `u† z` of the vector `u` of index `(i, c)` in `resolutionVectors w ν` involves
only the coordinate `c`, with coefficient `conj (τ (w i)) / ν` at the infinite place `τ`. -/
lemma dagger_resolutionVectors (w : I → E) (ν : ℕ) (j : I × n) (x : InfinitePlace E × n) :
    dagger (resolutionVectors w ν j) x = if x.2 = j.2 then conj (Φ x.1 (w j.1)) / ν else 0 := by
  simp [dagger, resolutionVectors, Pi.single_apply, apply_ite (Φ x.1), apply_ite conj]

/-- Let `w` be a tight frame with all multiplicities one and frame bound `b * b ≠ 0`: the matrix
`(∑ Φ τ (w i) * conj (Φ σ (w i)))`, indexed by infinite places `τ` and `σ`, is `b * b` times the
identity. For `k ≠ 0` this gives a resolution of the identity `z = ∑ k² (u† z) u` on `Eⁿ`. Here `u`
runs over the vectors `w i / (b k)` (`resolutionVectors w (b * k)`), placed in each copy of `E`. -/
lemma IsTightFrame.isResolution [WeilData E] [Fintype I] [Fintype n] {w : I → E} {b k : ℕ}
    (hw : IsTightFrame w 1 (b * b)) (hb : b ≠ 0) (hk : k ≠ 0) :
    IsResolution (resolutionVectors (n := n) w (b * k)) fun _ : I × n ↦ k * k := by
  rintro ⟨σ, c⟩ ⟨τ, c'⟩
  have h_tight : ∑ i : I, Φ σ (w i) * conj (Φ τ (w i)) = if σ = τ then (b * b : ℂ) else 0 := by
    simpa using hw.sum_mul_conj σ τ
  have h_term (j : I × n) : (k * k : ℕ) * (Φ σ (resolutionVectors w (b * k) j c) *
      dagger (resolutionVectors w (b * k) j) (τ, c')) =
      if c = j.2 ∧ c = c' then Φ σ (w j.1) * conj (Φ τ (w j.1)) / (b * b) else 0 := by
    rw [dagger_resolutionVectors]
    by_cases hc : c = j.2 <;> by_cases hc' : c' = j.2 <;>
      simp [resolutionVectors, hc, hc', eq_comm (a := j.2), field]
  simp_rw [h_term, Fintype.sum_prod_type]
  by_cases hc : c = c' <;> simp [hc, ← Finset.sum_div, h_tight, apply_ite (· / (b * b : ℂ)), hb]

end Frames

/-- In the field `E = P.E s` of level `s` of the parameters `P` let `ζ = P.ζ s`, a primitive root of
unity of order `q₁ = P.q₁ s`. The vectors `ζ ^ i / q₁` for `0 ≤ i < q₁`, each taken `q₁` times and
placed in each copy of `E`, are a resolution of the identity on `Eⁿ`. -/
lemma Parameters.isResolution_resolutionVectors_zeta_pow (P : Parameters) (s : ℕ) (n : Type)
    [Fintype n] [DecidableEq n] :
    IsResolution (resolutionVectors (n := n)
      (fun x : (Σ _ : Fin (P.q₁ s), Fin (P.q₁ s)) ↦ P.ζ s ^ (x.fst : ℕ)) (P.q₁ s)) fun _ ↦ 1 := by
  -- The powers of `ζ`, each taken `q₁` times, are a tight frame of length `q₁²`.
  simpa only [mul_one] using (P.isTightFrame_zeta_pow s (P.q₁ s)).repeat_vectors.isResolution
    (NeZero.ne (P.q₁ s)) one_ne_zero

/-- Let `d` be a prime congruent to `7` modulo `8`, `C` a lattice with complex multiplication by the
integers of `ℚ(√-d)`, and `δ ≠ 0` such an integer, of norm `N`. Write `T_y` for the twisted
translation `C.twistedTranslate 1 y`, whose degree `1` is that of the theta function `θ` of `C`. If
`δ y_i` is a period of `C` for every `i`, the product of the `(T_{y_i} θ)(δ̄ z_i)` along linear
forms `z_i = μ_i z` is `∏ θ(z_i) ^ N` times an integral series in the parameters at the `z_i`, an
element of `C.multiSeriesRing μ`. -/
lemma CMLattice.exists_prod_twistedTranslate_eq_thetaProd_mul {d : ℕ} [PrimeSevenModEight d]
    (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p] {I X : Type} [Fintype I] [Fintype X]
    (μ : I → X → ℂ_[p])
    {δ : ℂ} {N : ℕ} (hδ : δ ∈ quadInt d) (hδ_ne : δ ≠ 0) (hN : δ * conj δ = N) {y : I → ℂ}
    (hy : ∀ i : I, δ * y i ∈ C.Λ) :
    ∃ H ∈ C.multiSeriesRing μ,
      ∏ i : I, (taylorVia ιₚ (C.twistedTranslate 1 (y i) C.θ)).subst
        (linearSeries (ιₚ (conj δ) • μ i)) = C.thetaProd μ (fun _ : I ↦ N) * H := by
  have h_isogeny : C.IsIsogeny C.periodPair (conj δ) N :=
    ⟨fun _ hx ↦ C.mul_mem_of_quadInt (conj_mem_quadInt hδ) hx, by simp [← hN, mul_comm]⟩
  -- On one curve the `i`-th factor, as a series in `z_i`, is `θ ^ N` times an integral series.
  choose u hu h_factor using fun i : I ↦ C.exists_rescale_twistedTranslate_eq_theta_pow_mul (p := p)
    h_isogeny hδ_ne (hy i)
  refine ⟨∏ i : I, (u i).subst (linearSeries (μ i)),
    prod_mem fun i _ ↦ subst_mem_multiSeriesRing μ (hu i) i, ?_⟩
  rw [CMLattice.thetaProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have h_smul : linearSeries (ιₚ (conj δ) • μ i) = ιₚ (conj δ) • linearSeries (μ i) := by
    simp [linearSeries, Finset.smul_sum, mul_smul]
  rw [h_smul, ← subst_rescale_eq_subst_smul _ (hasSubst_linearSeries _), h_factor,
    PowerSeries.subst_mul (hasSubst_linearSeries _),
    PowerSeries.subst_pow (hasSubst_linearSeries _)]

namespace Parameters
open Space Fintype QuadField CMLattice

section RationalTranslates
variable {P : Parameters} {s : ℕ} {n : Type} {p : ℕ} [Fact p.Prime]

lemma ne_zero_of_prime_coprime {k : ℕ} (hk : p.Coprime k) : k ≠ 0 := by
  rintro rfl
  simp [(Fact.out : p.Prime).ne_one] at hk

omit [Fact p.Prime] in
/-- Let `ν` be prime to `p` and `ν y` lie in the standard lattice `Ô E ^ n`, where `E = P.E s`. For
every integer `δ` of `K` the vector `y` lies in `integralAfter δ` of the places above `p`, that is,
the coordinates of `δ y` are integral at these places. -/
lemma mem_integralAfter_of_nsmul_mem {δ : 𝓞 P.K} {ν : ℕ} (hν : p.Coprime ν) {y : n → 𝔸f (P.E s)}
    (hy : ν • y ∈ stdLattice (P.E s) n) :
    y ∈ integralAfter δ fun u : FinPlace (P.E s) ↦ ↑p ∈ u.asIdeal := by
  intro c u hu
  have h_unit : Valued.v (ν : LocField u) = 1 := by
    simpa using v_algebraMap_eq_one (u.isPrime.notMem_of_isCoprime_of_mem hν.cast hu)
  have h_int : ν • y ∈ integralAfter δ fun u : FinPlace (P.E s) ↦ ↑p ∈ u.asIdeal :=
    integralAfter.stdLattice_le hy
  simpa [mul_left_comm, h_unit] using h_int c u hu

/-- If the `w i` lie in the lattice `𝔞₀` (their finite images are integral) and `ν` is prime to
`p`, the finite images of the vectors `w i / ν` of `Eⁿ` are integral at all places above `p`. -/
lemma finiteImage_resolutionVectors_mem [DecidableEq n] {I : Type} {w : I → P.E s}
    (hw : ∀ i : I, finiteImage w i ∈ Ô (P.E s)) {ν : ℕ} (hν : p.Coprime ν) (j : I × n) :
    finiteImage (resolutionVectors w ν j) ∈
      integralAfter (1 : 𝓞 P.K) fun u : FinPlace (P.E s) ↦ ↑p ∈ u.asIdeal := by
  refine mem_integralAfter_of_nsmul_mem hν fun c ↦ ?_
  have h_mul : ν • resolutionVectors w ν j = Pi.single j.2 (w j.1) := by
    simp [resolutionVectors, ← Pi.single_smul', mul_div_cancel₀, ne_zero_of_prime_coprime hν]
  rw [← map_nsmul, h_mul]
  by_cases hc : c = j.2
  · simpa [finiteImage, hc] using hw j.1
  · simp [finiteImage, hc]

variable [Fintype n]

/-- A finite adelic vector that is integral at the places above `p` becomes integral everywhere
when it is multiplied by a suitable number prime to `p`. -/
lemma exists_coprime_mul_mem_of_mem_integralAfter {x : n → 𝔸f (P.E s)}
    (hx : x ∈ integralAfter (1 : 𝓞 P.K) fun u : FinPlace (P.E s) ↦ ↑p ∈ u.asIdeal) :
    ∃ m : ℕ, p.Coprime m ∧ ∀ c : n, m * x c ∈ Ô (P.E s) := by
  have hp : p.Prime := Fact.out
  obtain ⟨m₀, hm₀, h_clear⟩ := exists_forall_mul_mem_Ô x
  obtain ⟨e, m, hm, rfl⟩ : ∃ e m : ℕ, ¬p ∣ m ∧ m₀ = p ^ e * m :=
    WfDvdMonoid.max_power_factor hm₀ hp
  refine ⟨m, hp.coprime_iff_not_dvd.2 hm, fun c ↦ mem_Ô.2 fun u ↦ ?_⟩
  by_cases hu : ↑p ∈ u.asIdeal
  · simpa using nsmul_mem hx m c u hu
  · have h_unit : Valued.v (p : LocField u) = 1 := by simpa using v_algebraMap_eq_one hu
    simpa [h_unit] using mem_Ô.1 (h_clear c) u

/-- Let `V` be a standard space over `E = P.E s` (its signs `ε` are `+1` and its point is the
identity), and let `F` lie in the finite part of its Weil model `𝒮 V`, the span of the translates of
the vacuum by finite adelic vectors. Here `V.ϱ (finVec x)` is the Heisenberg translation by the
adelic vector with finite part `α x` and real part zero. If `δ x` is integral above `p`, it acts on
`F` as the translation by a rational vector `γ` with `δ γ` in `𝔞₀ⁿ ⊗ ℤ_(p)`: for a number `m` prime
to `p`, the vector `m δ γ` lies in the lattice `𝔞₀ⁿ` (its finite image is integral). -/
lemma exists_rho_finiteImage_eq_and_coprime_mul_mem [DecidableEq n]
    {ε : n → ℤˣ} {V : Space (E P s) n ε} [V.IsStd] {F : 𝒮 V} (hF : F ∈ V.finitePart) {δ : 𝓞 P.K}
    {x : n → 𝔸f (P.E s)} (hx : x ∈ integralAfter δ fun u : FinPlace (P.E s) ↦ ↑p ∈ u.asIdeal) :
    ∃ (γ : n → P.E s) (m : ℕ),
      V.ϱ (finVec (finiteImage γ)) F = V.ϱ (finVec x) F ∧
      p.Coprime m ∧
      ∀ c : n, finiteImage id (m * (algebraMap P.K (P.E s) δ * γ c)) ∈ Ô (P.E s) := by
  -- Approximate `x` by a rational `γ` with `finiteImage γ - x` in the standard lattice, chosen so
  -- that the translate of `F` is unchanged.
  obtain ⟨γ, hγ, h_translate⟩ := exists_finiteImage_approx hF x
  have h_int : finiteImage γ ∈ integralAfter δ fun u ↦ ↑p ∈ u.asIdeal := by
    simpa only [sub_add_cancel] using add_mem (integralAfter.stdLattice_le hγ) hx
  have h_scaled : finiteImage (fun c ↦ algebraMap P.K (P.E s) δ * γ c) ∈
      integralAfter (1 : 𝓞 P.K) fun u ↦ ↑p ∈ u.asIdeal := fun c u hu ↦ by
    simpa [finiteImage, mul_left_comm, mul_assoc] using h_int c u hu
  obtain ⟨m, hm, h_clear⟩ := exists_coprime_mul_mem_of_mem_integralAfter h_scaled
  exact ⟨γ, m, h_translate, hm, fun c ↦ by simpa [finiteImage, mul_left_comm] using h_clear c⟩

end RationalTranslates

/-- There is a tight frame in the CM field `P.E s`, with all multiplicities one, whose length is
the square of a number `b` prime to `p`. It repeats `b` times each vector of a tight frame of
length `b`: that of the powers of `ζ` if `p` does not divide `q₁`, and otherwise that of a length
prime to `q₁`. -/
lemma exists_coprime_isTightFrame_sq (P : Parameters) (s p : ℕ) [Fact p.Prime] :
    ∃ b : ℕ, p.Coprime b ∧
      ∃ (I : Type) (_ : Fintype I) (w : I → P.E s), IsTightFrame w 1 (b * b) := by
  suffices h_frame : ∃ b : ℕ, p.Coprime b ∧
      ∃ (I : Type) (_ : Fintype I) (v : I → P.E s), IsTightFrame v 1 b by
    obtain ⟨b, hb, I, _, v, hv⟩ := h_frame
    exact ⟨b, hb, Σ _ : I, Fin (b * 1), inferInstance, fun x ↦ v x.1,
      (hv.mul_left b).repeat_vectors⟩
  by_cases hp : p ∣ P.q₁ s
  · obtain ⟨len, I, _, v, hv, -, h_coprime, -⟩ := P.exists_isTightFrame_coprime s
    exact ⟨len, (h_coprime.coprime_dvd_right hp).symm, I, inferInstance, v, hv⟩
  · exact ⟨P.q₁ s, (Fact.out : p.Prime).coprime_iff_not_dvd.2 hp, Fin (P.q₁ s), inferInstance,
      fun i ↦ P.ζ s ^ i.val, isTightFrame_pow isPrimitiveRoot_zeta⟩

/-- Let `w` and `m δ γ` have finite images in `Ô (P.E s)`, where `δ` is an integer of the imaginary
quadratic field `P.K`. If `m * b` divides `k`, then multiplying by `k δ` sends the point
`-(cmPeriod / b) ∑ Φ τ γ * conj (Φ τ w)`, summed over the infinite places `τ`, into the lattice
`P.cmCurve.Λ`, which is `cmPeriod 𝓞_K`. -/
lemma mul_neg_sum_mul_conj_mem_cmCurve_lattice {P : Parameters} {s : ℕ} {δ : 𝓞 P.K} {m b k : ℕ}
    {γ w : P.E s} (hγ : finiteImage id (m * (algebraMap P.K (P.E s) δ * γ)) ∈ Ô (P.E s))
    (hw : finiteImage id w ∈ Ô (P.E s)) (hb : b ≠ 0) (h_dvd : m * b ∣ k) :
    (k * δ : ℂ) * -(P.cmPeriod / b * ∑ τ : InfinitePlace (P.E s), Φ τ γ * conj (Φ τ w)) ∈
      P.cmCurve.Λ := by
  obtain ⟨l, rfl⟩ := h_dvd
  -- The lattice `𝔞₀` is self-dual over `𝓞_K`, so `t = w† (m δ γ)` is an integer of `K`.
  let t : ℂ := ∑ τ : InfinitePlace (P.E s), Φ τ (m * (algebraMap P.K (P.E s) δ * γ)) * conj (Φ τ w)
  have ht : t * P.cmPeriod ∈ P.cmCurve.Λ :=
    P.cmCurve.mul_mem_of_quadInt (sum_mul_conj_mem_quadInt hγ hw) cmPeriod_mem_cmCurve_lattice
  have h_eq : ((m * b * l : ℕ) * δ : ℂ) *
      -(P.cmPeriod / b * ∑ τ : InfinitePlace (P.E s), Φ τ γ * conj (Φ τ w)) =
        -(l • (t * P.cmPeriod)) := by
    simp [t, ← Finset.mul_sum, mul_assoc, field]
  simpa only [h_eq] using neg_mem (nsmul_mem ht l)

section VacuumExpansion
variable {P : Parameters} {s : ℕ} {n : Type} {p : ℕ} [Fact p.Prime] [Fintype n] [DecidableEq n]
  {ε : n → ℤˣ}

/-- A vector of `𝒮 V` is evaluated as its theta function, here at `finVec (x i)`. If
`∑ c i * V.vacElem (finVec (x i)) = M ≠ 0`, then `intVacuum V` is the sum of the `(M⁻¹ * intVacuum V
(finVec (x i))) • c i • V.vacElem`. -/
lemma intVacuum_eq_sum_smul_vacElem {V : Space (E P s) n ε} {Y : Type} [Fintype Y]
    {c : Y → ℂ} {x : Y → n → 𝔸f (P.E s)} {M : ℂ} (hM : M ≠ 0)
    (h_sum : ∑ i : Y, c i * V.vacElem (finVec (x i)) = M) :
    intVacuum V = ∑ i : Y, (M⁻¹ * intVacuum V (finVec (x i))) • c i • V.vacElem := by
  have h_term (i : Y) : (M⁻¹ * intVacuum V (finVec (x i))) • c i • V.vacElem =
      (M⁻¹ * (c i * V.vacElem (finVec (x i)))) • intVacuum V := by
    simp only [intVacuum, Space.smul_apply]
    module
  simp only [h_term, ← Finset.sum_smul, ← Finset.mul_sum, h_sum, inv_mul_cancel₀ hM, one_smul]

variable {V : Space (E P s) n ε} [V.IsStd] [PadicPlace p]

omit [V.IsStd] in
/-- Let `V` be a hermitian space over `E = P.E s` with signs `ε`, and `F` a vector of its Weil model
`𝒮 V`. The operator `V.finHeisenbergOp x` takes the translate of `F` by `y` to a multiple of the
translate of `F` by `x + y`, and the scalar lies in the valuation ring `embValRing` of the embedding
`ιₚ` of `ℂ` in `ℂ_p`. -/
lemma exists_finHeisenbergOp_rho_eq_smul (x y : n → 𝔸f (P.E s)) (F : 𝒮 V) :
    ∃ c : embValRing, V.finHeisenbergOp x (V.ϱ (finVec y) F) = c • V.ϱ (finVec (x + y)) F := by
  let z : 𝔸f (P.E s) :=
    stdLattice.traceOneAdele * stdLattice.half * star x ⬝ᵥ x + stdLattice.half * star y ⬝ᵥ x
  refine ⟨⟨stdLattice.selfDualAddChar (P.E s) z, (norm_map_selfDualAddChar ιₚ z).le⟩, ?_⟩
  rw [finHeisenbergOp, stdLattice.semichar, _root_.smul_apply, rho_finVec_rho_finVec,
    smul_smul,
    ← AddChar.map_add_eq_mul, Subring.smul_def]

variable (V p) in
/-- An expansion of the integral vacuum of a standard space `V` (of rank `n`, with signs `ε` at the
infinite places) along a tight frame in `E = P.E s`. The frame `w` has length `b²` with `b` prime
to `p`. The integral vacuum is a combination, with `ιₚ`-integral coefficients `a j`, of the
translates of a vector `F` of the Weil model `𝒮 V` by the points `y j`. The vector `F` lies in the
finite part `V.finitePart`, spanned by the images of the vacuum under finite Heisenberg operators,
and the theta functions of its rational translates are products of translates of `θ` along the
frame. -/
structure IsVacuumExpansion (b : ℕ) {I : Type} [Fintype I] (w : I → P.E s) (F : 𝒮 V)
    {J : Type} [Fintype J] (y : J → n → 𝔸f (P.E s)) (a : J → embValRing) : Prop where
  /-- The number `b` is prime to `p`. -/
  coprime : p.Coprime b
  /-- The vectors `w i`, each taken once, are a tight frame of length `b²`. -/
  isTightFrame : IsTightFrame w 1 (b * b)
  /-- The vector `F` lies in the finite part of `𝒮 V`. -/
  mem_finitePart : F ∈ V.finitePart
  /-- The vectors `b y j` are integral. -/
  nsmul_mem_stdLattice (j : J) : b • y j ∈ stdLattice (P.E s) n
  /-- The integral vacuum is the sum of the translates of `F` by `y j` with coefficients `a j`. -/
  intVacuum_eq_sum : intVacuum V = ∑ j : J, a j • V.ϱ (finVec (y j)) F
  /-- For rational `γ` and complex `c`, the Taylor series of the theta function of the translate of
  `F` by `γ`, taken at `c (areaScale / cmPeriod) z` with `areaScale = √(2π / √d)` and `cmPeriod`
  the period `Ω₀` of `K = ℚ(√-d)`, is a product of twisted translates of the function `θ` of the
  curve `ℂ / Ω₀ 𝓞_K` along the forms `c u† z`, over the vectors `u` of
  `resolutionVectors w b`. -/
  jetSeries_eq_prod (γ : n → P.E s) (c : ℂ) :
    V.jetSeries (c * (P.areaScale / P.cmPeriod)) (V.ϱ (finVec (finiteImage γ)) F) =
      ∏ i : I × n, (taylorAtZero (P.cmCurve.twistedTranslate 1
        (-(P.cmPeriod / b * ∑ τ : InfinitePlace (P.E s), Φ τ (γ i.2) * conj (Φ τ (w i.1))))
        P.cmCurve.θ)).subst (linearSeries (c • dagger (resolutionVectors w b i)))

open scoped Pointwise in
/-- Let `V` be a standard space, `b` a number prime to `p`, and `F` a vector of its Weil model on
which the theta functional `V.θ` takes the value `1`. Suppose that `entireTheta F`, the theta
function of `F` in Fock's coordinates divided by the Gaussian, is entire and fixed by the signed
translations by the lattice `b 𝔞₀ⁿ`. Then `intVacuum V` is `∑ a j • V.ϱ (finVec (y j)) F`, with
coefficients `a j` in `embValRing` (integral under `ιₚ`) and points `y j` with `b y j` in the
standard lattice `Ô E ^ n`. -/
lemma exists_intVacuum_eq_sum_of_isThetaFunction {b : ℕ} (hb : p.Coprime b) {F : 𝒮 V}
    (hF_value : V.θ F = 1)
    (hF_theta : IsThetaFunction ((b : P.E s) • idealLattice (P.E s) n) (entireTheta F)) :
    ∃ (J : Type) (_ : Fintype J) (y : J → n → 𝔸f (P.E s)) (a : J → embValRing),
      (∀ j : J, b • y j ∈ stdLattice (P.E s) n) ∧
      intVacuum V = ∑ j : J, a j • V.ϱ (finVec (y j)) F := by
  have hbb_ne : b * b ≠ 0 := mul_self_ne_zero.2 (ne_zero_of_prime_coprime hb)
  -- Fourier inversion gives points `pt i` in `b⁻¹ 𝔞₀ⁿ`, periods `period j` and coefficients
  -- `coeff i`: each `coeff i • vacuum` is the sum over the periods of translates of `F` by `-pt i`,
  -- and `∑ coeff i • (translate of the vacuum by pt i)` is `M • F`, with `M` a power of `b * b`.
  obtain ⟨Y, Γ, _, _, pt, period, coeff, hpt, hperiod, -, h_average, h_inversion⟩ :=
    V.exists_fourier_coefficients (δ := (b : P.E s)) (by simp) hbb_ne (by simp)
      (by rwa [star_natCast])
  set M : ℂ := (b * b : ℕ) ^ card (InfinitePlace (P.E s) × n) with hM
  -- Apply the theta functional `V.θ` to `h_inversion`, then insert `h_average` in the vacuum.
  have h_values : ∑ i : Y, coeff i * V.vacElem (finVec (finiteImage (pt i))) = M := by
    simpa only [map_sum, map_smul, theta_rho, hF_value, smul_eq_mul, mul_one]
      using congrArg V.θ h_inversion
  -- The values of the integral vacuum are integral and `M` is a power of `b`, prime to `p`.
  have h_coeff (i : Y) : ‖ιₚ (M⁻¹ * intVacuum V (finVec (finiteImage (pt i))))‖ ≤ 1 := by
    simpa [hM, hb.norm_natCast_eq_one] using norm_intVacuum_le_one
  let a (i : Y) : embValRing := ⟨M⁻¹ * intVacuum V (finVec (finiteImage (pt i))), h_coeff i⟩
  have h_vacuum : intVacuum V = ∑ i : Y, a i •
      ∑ j : Γ, V.finHeisenbergOp (finiteImage (period j))
        (V.ϱ (finVec (finiteImage (-pt i))) F) := by
    rw [intVacuum_eq_sum_smul_vacElem (pow_ne_zero _ (Nat.cast_ne_zero.2 hbb_ne)) h_values]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (a i • ·) (h_average i)
  -- Each term of the inner sum is an integral multiple `r x` of a translate of `F`.
  choose r hr using fun x : Y × Γ ↦
    exists_finHeisenbergOp_rho_eq_smul (finiteImage (period x.2)) (finiteImage (-pt x.1)) F
  refine ⟨Y × Γ, inferInstance, fun x ↦ finiteImage (period x.2 - pt x.1), fun x ↦ a x.1 * r x,
    fun x ↦ ?_, ?_⟩
  · rw [← map_nsmul, ← mem_idealLattice, smul_sub, ← Nat.cast_smul_eq_nsmul (P.E s) b (pt x.1)]
    exact sub_mem (nsmul_mem (hperiod x.2) b) (hpt x.1)
  · simp only [h_vacuum, Fintype.sum_prod_type, Finset.smul_sum, mul_smul, sub_eq_add_neg, map_add]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [hr (i, j)]

end VacuumExpansion

open scoped Pointwise in
/-- The integral vacuum `intVacuum V` of a standard space `V` has an expansion along a tight frame,
`IsVacuumExpansion p V b w F y a`. There are vectors `w i` in `𝔞₀` whose matrix
`(∑ τ(w i) conj σ(w i))` is `b²` times the identity, with `b` prime to `p`. There is a vector `F` in
the finite part of `𝒮 V`, and there are points `y j` with `b y j` integral. The integral vacuum is a
combination, with coefficients `a j` in `embValRing`, of the translates of `F` by the `y j`. -/
lemma exists_isVacuumExpansion {P : Parameters} {s : ℕ} {n : Type} (p : ℕ) [Fact p.Prime]
    [Fintype n] [DecidableEq n] {ε : n → ℤˣ} (V : Space (E P s) n ε) [V.IsStd] [PadicPlace p] :
    ∃ (b : ℕ) (I : Type) (_ : Fintype I) (w : I → P.E s) (F : 𝒮 V)
      (J : Type) (_ : Fintype J) (y : J → n → 𝔸f (P.E s)) (a : J → embValRing),
      IsVacuumExpansion p V b w F y a := by
  obtain ⟨b, hb, I, _, w, hw⟩ : ∃ b : ℕ, p.Coprime b ∧
      ∃ (I : Type) (_ : Fintype I) (w : I → P.E s), IsTightFrame w 1 (b * b) :=
    exists_coprime_isTightFrame_sq P s p
  have hb_ne : b ≠ 0 := ne_zero_of_prime_coprime hb
  have h_area : P.cmCurve.area = ‖(P.cmPeriod : ℂ)‖ ^ 2 / (b * b : ℕ) * (b * b : ℕ) * √P.d / 2 := by
    simp [area_eq_of_eq_scaledIdeal latticeModule_cmCurve, hb_ne]
  have hb_norm : (b : 𝓞 P.K) * conj ((b : 𝓞 P.K) : ℂ) = (b * b : ℕ) := by simp
  -- All factors of `F` are `θ`, the monomial with exponents `(1, 0, 0)`.
  obtain ⟨F, hF, hF_theta⟩ : ∃ F : 𝒮 V,
      IsResolutionProduct V P.cmCurve (P.cmPeriod / conj ((b : 𝓞 P.K) : ℂ)) w 1
        (fun _ : I × n ↦ P.cmCurve.monomialSection (1, 0, 0)) F ∧
      IsThetaFunction ((b : P.E s) • idealLattice (P.E s) n) (entireTheta F) := by
    obtain ⟨F, hF, -, h_periods⟩ := exists_isResolutionProduct_of_isTightFrame V b
      (mul_ne_zero hb_ne hb_ne) hb_norm hw (fun _ ↦ (1, 0, 0)) (by simp)
      cmPeriod_mem_cmCurve_lattice h_area
    exact ⟨F, hF, by simpa using h_periods⟩
  have hF_value : V.θ F = 1 := by
    simpa [monomialSection, resolutionShift] using hF.theta_translate 0
  obtain ⟨J, _, y, a, hy, h_vacuum⟩ :
      ∃ (J : Type) (_ : Fintype J) (y : J → n → 𝔸f (P.E s)) (a : J → embValRing),
        (∀ j : J, b • y j ∈ stdLattice (P.E s) n) ∧
        intVacuum V = ∑ j : J, a j • V.ϱ (finVec (y j)) F :=
    exists_intVacuum_eq_sum_of_isThetaFunction hb hF_value hF_theta
  refine ⟨b, I, inferInstance, w, F, J, inferInstance, y, a,
    { coprime := hb, isTightFrame := hw, mem_finitePart := hF.mem_finitePart,
      nsmul_mem_stdLattice := hy, intVacuum_eq_sum := h_vacuum,
      jetSeries_eq_prod := fun γ c ↦ ?_ }⟩
  -- `F` is a product along the frame; it remains to match the linear forms and the shifts.
  refine (hF.jetSeries_translate γ _).trans (Finset.prod_congr rfl fun i _ ↦ ?_)
  have h_form : resolutionFormCoeff (P.cmPeriod / conj ((b : 𝓞 P.K) : ℂ) / P.areaScale *
      (c * (P.areaScale / P.cmPeriod))) w i = c • dagger (resolutionVectors w b i) := by
    ext x
    by_cases hx : x.2 = i.2 <;> simp [resolutionFormCoeff, dagger_resolutionVectors, hx, field]
  rw [h_form]
  simp [monomialSection, resolutionShift]

variable {P : Parameters} {s : ℕ} {n : Type} {p : ℕ} [Fact p.Prime] [Fintype n] [DecidableEq n]
  {ε : n → ℤˣ} {V : Space (E P s) n ε} [V.IsStd] [PadicPlace p]

variable (V) in
/-- Let `V` be a space of rank `n` over `E = P.E s` with signs `ε`, and `μ` a family of linear
forms. These are the vectors `g` of its Weil model `𝒮 V` such that the Taylor series of the theta
function of `g` at `c z`, read in `ℂ_p`, is `Θ` times an integral series in the parameters of the
curve `P.cmCurve`, which is `ℂ / cmPeriod 𝓞_K`, at the forms `μ` (an element of
`multiSeriesRing μ`). -/
def thetaMultiples {J : Type} [Fintype J] (μ : J → InfinitePlace (P.E s) × n → ℂ_[p]) (c : ℂ)
    (Θ : MvPowerSeries (InfinitePlace (P.E s) × n) ℂ_[p]) : Submodule embValRing (𝒮 V) where
  carrier := {g : 𝒮 V | ∃ H ∈ P.cmCurve.multiSeriesRing μ, (V.jetSeries c g).map ιₚ = Θ * H}
  zero_mem' := ⟨0, zero_mem (P.cmCurve.multiSeriesRing μ), by simp⟩
  add_mem' := by
    rintro g g' ⟨H, hH, hg⟩ ⟨H', hH', hg'⟩
    exact ⟨H + H', add_mem hH hH', by rw [map_add, map_add, hg, hg', mul_add]⟩
  smul_mem' := by
    rintro a g ⟨H, hH, hg⟩
    refine ⟨ιₚ a • H, P.cmCurve.smul_mem_multiSeriesRing a.2 hH, ?_⟩
    rw [mul_smul_comm, ← hg]
    change MvPowerSeries.map ιₚ (V.jetSeries c ((a : ℂ) • g)) =
      ιₚ a • MvPowerSeries.map ιₚ (V.jetSeries c g)
    simp [MvPowerSeries.smul_eq_C_mul]

/-- For `k ≠ 0` the form `c̄ (w i / b)† z`, read in `ℂ_p`, is `k c̄` times the form
`(w i / (b k))† z`. -/
lemma map_linearSeries_smul_dagger_resolutionVectors {I : Type} (w : I → P.E s) (b : ℕ) {k : ℕ}
    (hk : k ≠ 0) (c : ℂ) (i : I × n) :
    (linearSeries (conj c • dagger (resolutionVectors w b i))).map ιₚ =
      linearSeries (ιₚ (conj (k * c)) • daggerForms (resolutionVectors w (b * k)) i) := by
  have h_coeff (z : InfinitePlace (P.E s) × n) :
    ιₚ ((conj c • dagger (resolutionVectors w b i)) z) =
      (ιₚ (conj (k * c)) • daggerForms (resolutionVectors w (b * k)) i) z := by
    by_cases hz : z.2 = i.2 <;> simp [daggerForms, dagger_resolutionVectors, hz, field]
  simp only [linearSeries, map_sum, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C,
    MvPowerSeries.map_X, h_coeff]

omit [V.IsStd] in
/-- Let `δ ≠ 0` have norm `N`. Suppose the theta function of `g` at `c z` is a product of the
translates `twistedTranslate 1 (t i)` of `θ` along the forms `δ̄ u† z`. Here `u` runs over the
vectors `resolutionVectors w b i`, which for `i = (i', c')` have `w i' / b` in coordinate `c'` and
`0` elsewhere. If `k ≠ 0` and `k δ` takes the `t i` to periods, then `g` lies in `thetaMultiples`:
this product, read in `ℂ_p`, is `θ_u ^ N` times an integral series. Here `θ_u` is the product of the
`θ(u† z) ^ k²` over `u` in `resolutionVectors w (b k)`. -/
lemma mem_thetaMultiples_of_jetSeries_eq_prod {δ : 𝓞 P.K} {N : ℕ} (hδ_ne : δ ≠ 0)
    (hN : δ * conj (δ : ℂ) = N) {I : Type} [Fintype I] {w : I → P.E s} {b k : ℕ} (hk : k ≠ 0)
    {t : I × n → ℂ} (ht : ∀ i : I × n, (k * δ : ℂ) * t i ∈ P.cmCurve.Λ) {c : ℂ} {g : 𝒮 V}
    (hg : V.jetSeries c g =
      ∏ i : I × n, (taylorAtZero (P.cmCurve.twistedTranslate 1 (t i) P.cmCurve.θ)).subst
        (linearSeries (conj (δ : ℂ) • dagger (resolutionVectors w b i)))) :
    g ∈ thetaMultiples V (daggerForms (resolutionVectors w (b * k))) c
      (P.cmCurve.thetaProd (daggerForms (resolutionVectors w (b * k))) (fun _ : I × n ↦ k * k) ^
        N) := by
  set μ : I × n → InfinitePlace (P.E s) × n → ℂ_[p] := daggerForms (resolutionVectors w (b * k))
  have h_norm : (k * δ : ℂ) * conj (k * δ : ℂ) = (k * k * N : ℕ) := by
    simp [← hN, mul_mul_mul_comm]
  obtain ⟨H, hH, h_prod⟩ : ∃ H ∈ P.cmCurve.multiSeriesRing μ,
      ∏ i : I × n, (taylorVia ιₚ (P.cmCurve.twistedTranslate 1 (t i) P.cmCurve.θ)).subst
        (linearSeries (ιₚ (conj (k * δ : ℂ)) • μ i)) =
        P.cmCurve.thetaProd μ (fun _ ↦ k * k * N) * H :=
    P.cmCurve.exists_prod_twistedTranslate_eq_thetaProd_mul μ ⟨k * δ, by simp⟩ (by simp [hk, hδ_ne])
      h_norm ht
  have h_power : P.cmCurve.thetaProd μ (fun _ ↦ k * k) ^ N =
      P.cmCurve.thetaProd μ fun _ ↦ k * k * N := by simp [thetaProd, ← Finset.prod_pow, pow_mul]
  refine ⟨H, hH, ?_⟩
  rw [hg, h_power, ← h_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [PowerSeries.map_subst (hasSubst_linearSeries _),
    map_linearSeries_smul_dagger_resolutionVectors w b hk]

/-- Let `f` be standard data of level `δ ≠ 0` on a standard space `V`, that is, an integral
combination of images of the integral vacuum under the finite Heisenberg operators of points that
`δ` makes integral above `p`, and let `N = δ δ̄`. There are vectors `u j` with multiplicities `m j`
forming a resolution of the identity (`IsResolution u m`), with each `finiteImage (u j)` integral at
the places above `p`. For these, the Taylor series of the theta function of `f` at
`δ̄ (areaScale / cmPeriod) z`, read in `ℂ_p` through `ιₚ`, is `(∏ θ(u_j† z) ^ m j) ^ N` times an
integral series in the parameters of the curve at the forms `u_j† z`. -/
lemma exists_jetSeries_map_eq_thetaProd_pow_mul {δ : 𝓞 P.K} {N : ℕ} (hδ_ne : δ ≠ 0)
    (hN : δ * conj (δ : ℂ) = N) {f : 𝒮 V} (hf : f ∈ standardData V δ) :
    ∃ (J : Type) (_ : Fintype J) (u : J → n → P.E s) (m : J → ℕ),
      IsResolution u m ∧
      (∀ j : J, finiteImage (u j) ∈
        integralAfter (1 : 𝓞 P.K) fun v : FinPlace (P.E s) ↦ ↑p ∈ v.asIdeal) ∧
      ∃ H ∈ P.cmCurve.multiSeriesRing (daggerForms u),
        (V.jetSeries (conj (δ : ℂ) * (P.areaScale / P.cmPeriod)) f).map ιₚ =
          P.cmCurve.thetaProd (daggerForms u) m ^ N * H := by
  obtain ⟨b, I, _, w, F, J, _, y, a, h_exp⟩ :
      ∃ (b : ℕ) (I : Type) (_ : Fintype I) (w : I → P.E s) (F : 𝒮 V) (J : Type) (_ : Fintype J)
        (y : J → n → 𝔸f (P.E s)) (a : J → embValRing), IsVacuumExpansion p V b w F y a :=
    exists_isVacuumExpansion p V
  have hb : p.Coprime b := h_exp.coprime
  have hw_int : ∀ i : I, finiteImage w i ∈ Ô (P.E s) := h_exp.isTightFrame.finiteImage_mem
  -- `M k` consists of the vectors for which the claim holds with the resolution `w / (b k)`.
  let μ (k : ℕ) : I × n → InfinitePlace (P.E s) × n → ℂ_[p] :=
    daggerForms (resolutionVectors w (b * k))
  let M (k : ℕ) : Submodule embValRing (𝒮 V) := thetaMultiples V (μ k)
    (conj (δ : ℂ) * (P.areaScale / P.cmPeriod)) (P.cmCurve.thetaProd (μ k) (fun _ ↦ k * k) ^ N)
  have hb_ne : b ≠ 0 := ne_zero_of_prime_coprime hb
  -- A translate of `F` by a point `x` with `δ x` integral above `p` is the translate by a rational
  -- `γ` with `m δ γ` in the lattice, so its series is a product of translates of `θ` by points
  -- that `m b δ` takes to periods. It lies in `M k` for the nonzero multiples `k` of `m b`.
  have h_translate (x : n → 𝔸f (P.E s)) (hx : x ∈ integralAfter δ fun u ↦ ↑p ∈ u.asIdeal) :
      ∃ m : ℕ, p.Coprime m ∧ ∀ k : ℕ, k ≠ 0 → m ∣ k → V.ϱ (finVec x) F ∈ M k := by
    obtain ⟨γ, m, h_eq, hm, hγ⟩ : ∃ (γ : n → P.E s) (m : ℕ),
        V.ϱ (finVec (finiteImage γ)) F = V.ϱ (finVec x) F ∧ p.Coprime m ∧
        ∀ c : n, finiteImage id (m * (algebraMap P.K (P.E s) δ * γ c)) ∈ Ô (P.E s) :=
      exists_rho_finiteImage_eq_and_coprime_mul_mem h_exp.mem_finitePart hx
    refine ⟨m * b, hm.mul_right hb, fun k hk h_dvd ↦ ?_⟩
    rw [← h_eq]
    exact mem_thetaMultiples_of_jetSeries_eq_prod hδ_ne hN hk
      (fun i ↦ mul_neg_sum_mul_conj_mem_cmCurve_lattice (hγ i.2) (hw_int i.1) hb_ne h_dvd)
      (h_exp.jetSeries_eq_prod γ (conj δ))
  obtain ⟨m, hm, hf_mem⟩ : ∃ m : ℕ, p.Coprime m ∧ ∀ k : ℕ, k ≠ 0 → m ∣ k → f ∈ M k := by
    induction hf using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      -- A generator is a combination of the translates of `F` by the `x + y j`, and the `y j` are
      -- integral above `p`. Take the product over `j` of the numbers given by `h_translate`.
      choose m hm h_mem using fun j : J ↦ h_translate (x + y j)
        (add_mem hx (mem_integralAfter_of_nsmul_mem hb (h_exp.nsmul_mem_stdLattice j)))
      refine ⟨∏ j : J, m j, .prod_right fun j _ ↦ hm j, fun k hk h_dvd ↦ ?_⟩
      rw [h_exp.intVacuum_eq_sum, map_sum]
      refine sum_mem fun j _ ↦ ?_
      obtain ⟨c, hc⟩ : ∃ c : embValRing,
          V.finHeisenbergOp x (V.ϱ (finVec (y j)) F) = c • V.ϱ (finVec (x + y j)) F :=
        exists_finHeisenbergOp_rho_eq_smul x (y j) F
      rw [(V.finHeisenbergOp x).map_smul_of_tower, hc]
      exact (M k).smul_mem (a j) <| (M k).smul_mem c <|
        h_mem j k hk ((Finset.dvd_prod_of_mem m (Finset.mem_univ j)).trans h_dvd)
    | zero => exact ⟨1, by simp, fun k _ _ ↦ zero_mem (M k)⟩
    | add g g' _ _ hg hg' =>
      rcases hg, hg' with ⟨⟨m, hm, hg⟩, ⟨m', hm', hg'⟩⟩
      exact ⟨m * m', hm.mul_right hm', fun k hk h_dvd ↦ add_mem
        (hg k hk (dvd_of_mul_right_dvd h_dvd)) (hg' k hk (dvd_of_mul_left_dvd h_dvd))⟩
    | smul c g _ hg =>
      exact hg.imp fun m ⟨hm, hg⟩ ↦ ⟨hm, fun k hk h_dvd ↦ (M k).smul_mem c (hg k hk h_dvd)⟩
  have hm_ne : m ≠ 0 := ne_zero_of_prime_coprime hm
  -- Membership of `f` in `M m` is the asserted factorization for the resolution `w / (b m)`.
  exact ⟨I × n, inferInstance, resolutionVectors w (b * m), fun _ ↦ m * m,
    h_exp.isTightFrame.isResolution hb_ne hm_ne,
    finiteImage_resolutionVectors_mem hw_int (hb.mul_right hm), hf_mem m hm_ne dvd_rfl⟩

end Parameters

end New
