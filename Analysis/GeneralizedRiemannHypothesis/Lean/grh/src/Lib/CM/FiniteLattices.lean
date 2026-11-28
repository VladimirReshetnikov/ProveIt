import Lib.CM.GoodReduction

/-!
# Finitely many CM lattices

* `New.CMLattice.finite_range_latticeModule`: for a prime `d ≡ 7 mod 8`, only finitely many lattices
  in `ℂ` underlie a CM lattice for `K = ℚ(√-d)`.
* `New.CMLattice.theta_eq_of_latticeModule_eq`: the theta function `θ` depends only on the lattice;
  in particular it does not depend on the representative `t` of the point of order two.
* `New.CMLattice.exists_norm_twistedTranslate_theta_le`: the values `(T_u θ)(0)` are bounded
  uniformly in the CM lattice and in `u`.

Each CM lattice is a multiple of one of finitely many ideals, and the scaling `℘''(t) = 2` fixes the
factor up to a fourth root of unity.

Notions from other files:
* `C : CMLattice d`: a lattice `C.Λ` in `ℂ` stable under `𝓞_K`, with a point `C.t` of order two
  modulo `C.Λ` such that neither `ω t` nor `ω̄ t` lies in `C.Λ` (`ω = quadGen d = (1 + √-d) / 2`),
  scaled so that `℘''(C.t) = 2`.
* `C.latticeModule`: the lattice `C.Λ` as an `𝓞_K`-submodule of `ℂ`.
* `QuadField.scaledIdeal d (u, 𝔞)`: the submodule `u 𝔞` of `ℂ`, for a fractional ideal `𝔞` of `K`.
* `C.twistedTranslate 1 u f`: the function `(T_u f)(z) = exp(-π (z ū + |u|² / 2) / C.area)
  f(z + u)`.
* `C.θ`: the translate `T_t σ` of the sigma function, normalised to `1` at `0`.

## Relation to the literature

Known result: lattices with complex multiplication by `𝓞_K` up to homothety correspond to the ideal
classes. Source: Silverman, Advanced topics in the arithmetic of elliptic curves, Chapter II.
-/

open NumberField PeriodPair ComplexConjugate nonZeroDivisors

namespace New

/-- The sum `L.sumInvPow y 4 = ∑ (l - y)⁻⁴` over the lattice of `L` is homogeneous of degree `-4`:
if `L' = c L` with `c ≠ 0` and `z ≡ c y` modulo `L'`, then the sum for `L'` at `z` is `c⁻⁴` times
the sum for `L` at `y`. -/
lemma sumInvPow_four_of_mul_mem_iff {L L' : PeriodPair} {c y z : ℂ} (hc : c ≠ 0)
    (hL' : ∀ x : ℂ, c * x ∈ L'.lattice ↔ x ∈ L.lattice) (hz : c * y - z ∈ L'.lattice) :
    L'.sumInvPow z 4 = L.sumInvPow y 4 / c ^ 4 := by
  classical
  -- Write both sums as sums over `ℂ`, centred at the base point, and substitute `x ↦ c x`.
  let term (M : PeriodPair) (w : ℂ) : ℂ → ℂ :=
    (M.lattice : Set ℂ).indicator fun l : ℂ ↦ ((l - w) ^ 4)⁻¹
  have h_sum (M : PeriodPair) (w : ℂ) :
      HasSum (fun x : ℂ ↦ term M w (w + x)) (M.sumInvPow w 4) := by
    have h_lattice : HasSum (term M w) (M.sumInvPow w 4) :=
      hasSum_subtype_iff_indicator.1 (M.hasSum_sumInvPow w (by norm_num))
    simpa only [Function.comp_def, Equiv.coe_addLeft]
      using (Equiv.addLeft w).hasSum_iff.2 h_lattice
  have h_term (x : ℂ) : term L' z (z + c * x) = term L y (y + x) / c ^ 4 := by
    have h_mem : z + c * x ∈ L'.lattice ↔ y + x ∈ L.lattice := by
      rw [← hL', ← add_mem_cancel_left hz, ← add_assoc, sub_add_cancel, mul_add]
    simp only [term, Set.indicator, SetLike.mem_coe, h_mem, add_sub_cancel_left]
    split_ifs <;> ring
  have h_left : HasSum (fun x : ℂ ↦ term L' z (z + c * x)) (L'.sumInvPow z 4) := by
    simpa only [Function.comp_def, Equiv.mulLeft₀_apply]
      using (Equiv.mulLeft₀ c hc).hasSum_iff.2 (h_sum L' z)
  exact h_left.unique (by simpa only [h_term] using (h_sum L y).div_const (c ^ 4))

namespace CMLattice

variable {d : ℕ} {C D : CMLattice d}

/-- The normalisation `℘''(t) = 2` of a CM lattice `C` at its point `t = C.t` of order two (a field
of `C` fixes `g₂` accordingly), written with the series `℘''(t) = 6 ∑ (l - t)⁻⁴`, where `l` runs
over the lattice. -/
lemma six_mul_sumInvPow_t (C : CMLattice d) : 6 * C.sumInvPow C.t 4 = 2 := by
  rw [← deriv_derivWeierstrassP_eq_sumInvPow C.t_notMem, deriv_derivWeierstrassP _ C.t_notMem,
    C.g₂_eq]
  ring

variable [PrimeSevenModEight d]

/-- Let `d` be a prime `≡ 7 mod 8` and let `C`, `D` be CM lattices for `ℚ(√-d)`. If multiplication
by `c` maps the lattice `C.Λ` onto `D.Λ`, then it takes the marked point `C.t` of order two to
`D.t` modulo `D.Λ`: the marked point is the only point of order two that neither
`ω = quadGen d = (1 + √-d) / 2` nor `ω̄` multiplies into the lattice. -/
lemma mul_t_sub_t_mem {c : ℂ} (h_mem : ∀ x : ℂ, c * x ∈ D.Λ ↔ x ∈ C.Λ) :
    c * C.t - D.t ∈ D.Λ := by
  have h_two : c * C.t + c * C.t ∈ D.Λ := by simpa [← mul_add, h_mem] using C.two_t_mem
  have h_mul {a : ℂ} (ha : a = quadGen d ∨ a = conj (quadGen d)) (hat : a * C.t ∉ C.Λ) :
      a * (c * C.t - D.t) ∈ D.Λ :=
    (D.mul_mem_or_mul_sub_t_mem ha (c * C.t) h_two).resolve_left
      (by rwa [mul_left_comm, h_mem])
  obtain ⟨hω, hω_conj⟩ := C.quadGen_mul_t_notMem
  -- Conclude with `ω + ω̄ = 1`.
  simpa [← add_mul, conj_quadGen] using add_mem (h_mul (.inl rfl) hω) (h_mul (.inr rfl) hω_conj)

/-- Let `d` be a prime `≡ 7 mod 8`. If multiplication by `c ≠ 0` maps the lattice `C.Λ` of one CM
lattice onto the lattice `D.Λ` of another, then `c` is a fourth root of unity, as both are scaled
so that `℘''(t) = 2` at their marked points `t` of order two. -/
lemma pow_four_eq_one_of_mul_mem_iff {c : ℂ} (hc : c ≠ 0)
    (h_mem : ∀ x : ℂ, c * x ∈ D.Λ ↔ x ∈ C.Λ) : c ^ 4 = 1 := by
  have h_scale : D.sumInvPow D.t 4 = C.sumInvPow C.t 4 / c ^ 4 :=
    sumInvPow_four_of_mul_mem_iff hc h_mem (mul_t_sub_t_mem h_mem)
  rw [eq_div_iff (pow_ne_zero 4 hc)] at h_scale
  have hC : 6 * C.sumInvPow C.t 4 = 2 := C.six_mul_sumInvPow_t
  have hD : 6 * D.sumInvPow D.t 4 = 2 := D.six_mul_sumInvPow_t
  linear_combination 3 * h_scale + (hC - c ^ 4 * hD) / 2

/-- If `C` and `D` lie in the same ideal class `𝒞` (their lattices are complex multiples of ideals
in `𝒞`), then the lattice of `C` is `c` times that of `D` for a fourth root of unity `c`. -/
lemma IsInClass.exists_pow_four_eq_one_and_eq_scaledIdeal_mul {𝒞 : ClassGroup (𝓞 (QuadField d))}
    (hC : C.IsInClass 𝒞) (hD : D.IsInClass 𝒞) :
    ∃ c : ℂˣ, c ^ 4 = 1 ∧ C.latticeModule = QuadField.scaledIdeal d (c, 1) * D.latticeModule := by
  obtain ⟨c, hc⟩ : ∃ c : ℂˣ, C.latticeModule = QuadField.scaledIdeal d (c, 1) * D.latticeModule :=
    hD.exists_eq_scaledIdeal_mul (by rwa [map_one, one_mul])
  obtain ⟨v, 𝔞, -, hv⟩ := hD
  have h_mem (x : ℂ) : c * x ∈ C.Λ ↔ x ∈ D.Λ := by
    change c * x ∈ C.latticeModule ↔ x ∈ D.latticeModule
    rw [hc, hv, ← map_mul, Prod.mk_mul_mk, one_mul]
    simp only [QuadField.mem_scaledIdeal, Units.val_mul, mul_assoc, Units.mul_right_inj]
  exact ⟨c, Units.ext (by simpa using pow_four_eq_one_of_mul_mem_iff c.ne_zero h_mem), hc⟩

/-- For a prime `d ≡ 7 mod 8`, only finitely many `𝓞_K`-submodules of `ℂ` are the lattice
`C.latticeModule` of a CM lattice `C` for `K = ℚ(√-d)`. -/
lemma finite_range_latticeModule :
    (Set.range fun C : CMLattice d ↦ C.latticeModule).Finite := by
  -- Take a CM lattice `B 𝒞` in each ideal class `𝒞`. Every CM lattice is `c` times one of these,
  -- and `c⁴ = 1`. The choice of `B` starts from any one CM lattice `C₀`.
  obtain ⟨C₀, -⟩ := QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal (d := d) 1
  obtain ⟨B, hB : ∀ 𝒞 : ClassGroup (𝓞 (QuadField d)), (B 𝒞).IsInClass 𝒞, -⟩ :=
    C₀.exists_forall_isInClass
  have h_roots : {c : ℂˣ | c ^ 4 = 1}.Finite :=
    (Set.finite_coe_iff.1 (inferInstanceAs (Finite (rootsOfUnity 4 ℂ)))).subset
      fun c hc ↦ (mem_rootsOfUnity 4 c).2 hc
  let multiple (c : ℂˣ) (𝒞 : ClassGroup (𝓞 (QuadField d))) : Submodule (𝓞 (QuadField d)) ℂ :=
    QuadField.scaledIdeal d (c, 1) * (B 𝒞).latticeModule
  refine (h_roots.image2 multiple Set.finite_univ).subset ?_
  rintro _ ⟨C, rfl⟩
  obtain ⟨⟨u, 𝔟⟩, hC : C.latticeModule = QuadField.scaledIdeal d (u, 𝔟)⟩ :=
    C.exists_latticeModule_eq_scaledIdeal
  obtain ⟨c, hc_pow, hc⟩ : ∃ c : ℂˣ,
      c ^ 4 = 1 ∧ C.latticeModule = multiple c (ClassGroup.mk (QuadField d) 𝔟) :=
    IsInClass.exists_pow_four_eq_one_and_eq_scaledIdeal_mul ⟨u, 𝔟, rfl, hC⟩ (hB _)
  exact ⟨c, hc_pow, _, Set.mem_univ _, hc.symm⟩

/-- Two CM lattices with the same underlying lattice have the same area of a period
parallelogram. -/
lemma area_eq_of_latticeModule_eq (h : C.latticeModule = D.latticeModule) : C.area = D.area := by
  obtain ⟨x, hx⟩ := D.exists_latticeModule_eq_scaledIdeal
  rw [QuadField.area_eq_of_eq_scaledIdeal hx, QuadField.area_eq_of_eq_scaledIdeal (h.trans hx)]

/-- The theta function `θ` of a CM lattice depends only on the underlying lattice. -/
lemma theta_eq_of_latticeModule_eq (h : C.latticeModule = D.latticeModule) : C.θ = D.θ := by
  -- Both are sections of degree one for `C`, which form a line, and both have value `1` at `0`.
  have h_isog : C.IsIsogeny D.periodPair 1 1 :=
    ⟨fun x hx ↦ show 1 * x ∈ D.latticeModule by rwa [one_mul, ← h],
      by simp [area_eq_of_latticeModule_eq h]⟩
  have hD : D.θ ∈ C.sections 1 := by
    simpa only [one_mul] using C.comp_mul_mem_sections h_isog D.theta_mem
  have hθ_ne : C.θ ≠ 0 := Function.ne_iff.2 ⟨0, by simp [theta_zero]⟩
  have h_rank : Module.finrank ℂ (C.sections 1) = 1 := IsAppellHumbert.finrank_thetaSpace_nsmul
  have h_span : C.sections 1 = ℂ ∙ C.θ :=
    eq_span_singleton_of_mem_of_finrank_eq_one h_rank C.theta_mem hθ_ne
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • C.θ = D.θ := Submodule.mem_span_singleton.1 (h_span.le hD)
  have hc_one : c = 1 := by simpa [theta_zero] using congrFun hc 0
  simpa [hc_one] using hc

variable (d) in
/-- For a prime `d ≡ 7 mod 8`, the values `(T_u θ)(0) = exp(-π |u|² / (2 A)) θ(u)` are bounded
uniformly in the CM lattice `C` and in `u : ℂ`. Here `θ = C.θ` is the theta function of `C`,
`A = C.area`, and `T_u = C.twistedTranslate 1 u` is the twisted translation of degree one. -/
lemma exists_norm_twistedTranslate_theta_le :
    ∃ M : ℝ, ∀ (C : CMLattice d) (u : ℂ), ‖C.twistedTranslate 1 u C.θ 0‖ ≤ M := by
  -- For one lattice the modulus is continuous and periodic in `u`, so bounded; it depends only
  -- on the lattice, and there are finitely many.
  let values (C : CMLattice d) : Set ℝ := Set.range fun u : ℂ ↦ ‖C.twistedTranslate 1 u C.θ 0‖
  have h_compact (C : CMLattice d) : IsCompact (values C) :=
    IsAppellHumbert.isCompact_range_norm_thetaShift C.theta_mem
  have h_congr (C D : CMLattice d) (h : C.latticeModule = D.latticeModule) :
      values C = values D := by
    simp [values, thetaShift_apply, hermitianForm_apply, theta_eq_of_latticeModule_eq h,
      area_eq_of_latticeModule_eq h]
  let lattices : Set (Submodule (𝓞 (QuadField d)) ℂ) :=
    Set.range fun C : CMLattice d ↦ C.latticeModule
  have : Finite lattices := finite_range_latticeModule.to_subtype
  have h_rep (x : lattices) : ∃ C : CMLattice d, C.latticeModule = x := x.property
  choose B hB using h_rep
  obtain ⟨M, hM⟩ : BddAbove (⋃ x : lattices, values (B x)) :=
    (isCompact_iUnion fun x ↦ h_compact (B x)).bddAbove
  refine ⟨M, fun C u ↦ hM (Set.mem_iUnion.2 ⟨⟨C.latticeModule, C, rfl⟩, ?_⟩)⟩
  exact (h_congr _ C (hB _)).ge ⟨u, rfl⟩

end CMLattice

end New
