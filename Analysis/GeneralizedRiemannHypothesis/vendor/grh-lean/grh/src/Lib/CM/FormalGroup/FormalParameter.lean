import Lib.CM.FormalGroup.InseparableDegree
import Lib.CM.Integrality.LogTheta

/-!
# The formal parameter

Let `d ≡ 7` mod `8` be a prime and `C` a lattice with complex multiplication by the integers of
`K = ℚ(√-d)`. Let `p` be a prime, `ιₚ : ℂ →+* ℂ_[p]` a fixed embedding and `𝒪` the valuation ring of
`ℂ_[p]`. Power series are in the variable `z`, which is `X` in the code; so the formal parameter is
written `T`.

* `New.CMLattice.isSeriesGenerator_formalParam`: the part `T` of `y` in degrees `≡ 1` mod `q - 1`
  generates `𝒪[[y]]`.
* `New.CMLattice.exists_scaled_formalParam`: for some `ϖ` of valuation `ρ_p` the series
  `Y = T(ϖ z) / ϖ` is integral, and `Y - Y ^ q ≡ z`, `Y ≡ ∑ z ^ q ^ j` mod `π_p`. The proof writes
  `T(π_p z) = π_p T + b₁ T ^ q + ⋯` with a unit `b₁` and takes `ϖ ^ (q - 1) = -π_p / b₁`.
* `New.CMLattice.rescale_mem_range_seriesToCp`, `New.CMLattice.norm_coeff_le_one_of_lt`: for
  `g ∈ 𝒪[[y]]` the series `g(ϖ z)` is integral, and `g` is integral in the degrees below `q`.

## Notation

* `q = primeNorm d p` is the norm of a prime of `K` above `p`.
* `π_p = piPrime d p` is `√-d` if `p = d` and `p` otherwise; `piPrimeInt d` is its image in `𝒪`.
* `y = taylorVia ιₚ C.translatedY` is the Taylor series at `0` of the coordinate function
  `C.translatedY`, moved to `ℂ_[p]` by the embedding `ιₚ`.
* `𝒪[[y]] = C.integralSeriesRing` is the ring of the series `g(y)` with `g` a series over `𝒪`.
* `ρ_p = varpiValuation d p` is the valuation of `π_p` divided by `q - 1`.

## Relation to the literature

Known result: multiplication by `π_p` on the formal group of a curve with complex multiplication is
an endomorphism in the sense of Lubin and Tate. That `b₁` is a unit follows from the bound for the
height of the formal group (`New.CMLattice.insepDegree_piPrime_le`), and the scaling is an
elementary consequence. Lubin–Tate, Formal complex multiplication in local fields.
-/

open PowerSeries IsLocalRing

namespace New
variable {d p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] [PadicPlace p]

/-- If `ζ ^ (q - 1) = 1`, where `q = primeNorm d p`, then the pair `(ζ, ζ ^ (p + 1))` is a limit in
`ℂ_[p] × ℂ_[p]` of pairs `(α, α ᾱ)` with `α` an integer of `ℚ(√-d)`. -/
lemma mem_normPairClosure_of_pow_eq_one {ζ : ℂ_[p]} (hζ : ζ ^ (primeNorm d p - 1) = 1) :
    (ζ, ζ ^ (p + 1)) ∈ normPairClosure d := by
  refine mem_normPairClosure_of_pow_eq d
    (isOfFinOrder_iff_pow_eq_one.2 ⟨_, NeZero.pos _, hζ⟩).norm_eq_one ?_
  rw [← pow_sub_one_mul (Nat.ne_zero_of_lt (one_lt_primeNorm d p)), hζ, one_mul]

/-- The number `π_p` (`√-d` if `p = d`, and `p` otherwise) is not a unit of the valuation ring of
`ℂ_[p]`. -/
lemma not_isUnit_piPrimeInt : ¬IsUnit (piPrimeInt d : valRingCp p) := by
  rw [isUnit_integer_iff_norm_eq_one, coe_piPrimeInt]
  exact (norm_piPrime_lt_one d).ne

/-- If `ϖ ^ (q - 1) = π_p u` with `q = primeNorm d p`, `π_p = piPrimeInt d` and `u` a unit of the
valuation ring of `ℂ_[p]`, then `ϖ` has valuation `ρ_p = varpiValuation d p`. -/
lemma norm_eq_rpow_neg_varpiValuation_of_pow_eq {ϖ : ℂ_[p]} {u : valRingCp p} (hu : IsUnit u)
    (hϖ : ϖ ^ (primeNorm d p - 1) = (piPrimeInt d * u : valRingCp p)) :
    ‖ϖ‖ = (p : ℝ) ^ (-varpiValuation d p) := by
  rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) (NeZero.ne (primeNorm d p - 1))]
  simp [← norm_piPrime_eq_rpow_pow, ← norm_pow, hϖ, isUnit_integer_iff_norm_eq_one.1 hu,
    coe_piPrimeInt]

namespace CMLattice
variable (C : CMLattice d)

/-- For a prime `d ≡ 7 (mod 8)` and `q = primeNorm d p` (`p²` if `(p/d) = −1`, else `p`), if
`ζ ^ (q - 1) = 1` then `y(ζ z)` lies in the ring `𝒪[[y]] = C.integralSeriesRing` of integral series
in `y`. Here `y = taylorVia ιₚ C.translatedY` is the `p`-adic Taylor series at `0` of
`C.translatedY`, i.e. of `½(℘′(z + t) − a₁(℘(z + t) − ℘(t)))`. -/
lemma rescale_translatedY_mem_of_pow_eq_one {ζ : ℂ_[p]} (hζ : ζ ^ (primeNorm d p - 1) = 1) :
    rescale ζ (taylorVia ιₚ C.translatedY) ∈ C.integralSeriesRing :=
  C.rescale_translatedY_mem_of_mem_normPairClosure (mem_normPairClosure_of_pow_eq_one hζ)

/-- Let `q = primeNorm d p`, which is `p²` if `(p/d) = -1` and `p` otherwise, and let
`g = C.negLogTheta` be the series `-log θ` with `g(0) = 0`, that is, minus the logarithm of the
Taylor series at `0` of the theta function `C.θ` of the lattice `C`, read in `ℂ_[p]`. If
`ζ ^ (q - 1) = 1`, then `exp (ζ⁻¹ ^ (p + 1) g(ζ X) - g(X))` lies in `C.integralSeriesRing`. That
ring is `𝒪[[y]]`, the integral power series in the `p`-adic Taylor series `y` of `C.translatedY`. -/
lemma expSubst_rescale_sub_mem_of_pow_eq_one {ζ : ℂ_[p]} (hζ : ζ ^ (primeNorm d p - 1) = 1) :
    expSubst (ζ⁻¹ ^ (p + 1) • rescale ζ C.negLogTheta - C.negLogTheta) ∈ C.integralSeriesRing := by
  -- Take the pair `(ζ⁻¹, ζ ^ (-p - 1))`, then replace `z` by `ζ z`.
  have hζ₀ : ζ ≠ 0 := ne_zero_pow (NeZero.ne _) (hζ.trans_ne one_ne_zero)
  set f : ℂ_[p]⟦X⟧ := ζ⁻¹ ^ (p + 1) • C.negLogTheta - rescale ζ⁻¹ C.negLogTheta with hf
  have h_inv : expSubst f ∈ C.integralSeriesRing :=
    C.expSubst_sub_rescale_mem (mem_normPairClosure_of_pow_eq_one (by rw [inv_pow, hζ, inv_one]))
  have h_rescale : rescale ζ (expSubst f) ∈ C.integralSeriesRing :=
    C.isSeriesGenerator_translatedY.rescale_mem
      (C.rescale_translatedY_mem_of_pow_eq_one hζ) h_inv
  have h_eq : rescale ζ f = ζ⁻¹ ^ (p + 1) • rescale ζ C.negLogTheta - C.negLogTheta := by
    simp [hf, rescale_smul, rescale_rescale, inv_mul_cancel₀ hζ₀, rescale_one]
  rwa [rescale_subst (by simp [hf, constantCoeff_rescale, constantCoeff_negLogTheta]), h_eq]
    at h_rescale

/-- The formal parameter `T`: the part in degrees `≡ 1` mod `q - 1` of `y`, the `p`-adic Taylor
series of `C.translatedY`, where `q = primeNorm d p`. -/
noncomputable def formalParam : ℂ_[p]⟦X⟧ :=
  congruencePart (primeNorm d p - 1) 1 (taylorVia ιₚ C.translatedY)

/-- Let `d` be a prime `≡ 7` mod 8 and `p` a prime with a `p`-adic place `ιₚ`, and set
`q = primeNorm d p` (`p²` if `(p/d) = -1`, otherwise `p`). The formal parameter `T = C.formalParam`
is the part in degrees `≡ 1` mod `q - 1` of `y`, the `p`-adic Taylor series of `C.translatedY`. `T`
generates `C.integralSeriesRing = 𝒪[[y]]`: it has the form `X + ⋯`, and the ring consists exactly of
the series `g(T)` with `g` a power series over the valuation ring `𝒪` of `ℂ_[p]`. -/
lemma isSeriesGenerator_formalParam :
    IsSeriesGenerator C.integralSeriesRing (C.formalParam : ℂ_[p]⟦X⟧) := by
  -- `T` is the mean of the `ζ⁻¹ y(ζ z)` over `ζ ^ (q - 1) = 1`.
  have hy := C.isSeriesGenerator_translatedY (p := p)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ_[p] (primeNorm d p - 1)
  have h_mem : C.formalParam ∈ C.integralSeriesRing := by
    rw [formalParam, congruencePart_eq_sum hζ]
    refine hy.smul_mem (by simp [(coprime_primeNorm_sub_one d p).norm_natCast_eq_one])
      (sum_mem fun i _ ↦ hy.smul_mem (by simp [(hζ.isOfFinOrder (NeZero.ne _)).norm_eq_one]) ?_)
    exact C.rescale_translatedY_mem_of_pow_eq_one
      (by rw [pow_right_comm, hζ.pow_eq_one, one_pow])
  refine hy.of_mem h_mem ?_ ?_
  · simp [formalParam, ← coeff_zero_eq_constantCoeff_apply, coeff_congruencePart]
  · simp [formalParam, coeff_congruencePart, hy.coeff_one, Nat.ModEq.refl]

lemma constantCoeff_formalParam : constantCoeff (C.formalParam : ℂ_[p]⟦X⟧) = 0 :=
  C.isSeriesGenerator_formalParam.constantCoeff_eq_zero

lemma coeff_one_formalParam : coeff 1 (C.formalParam : ℂ_[p]⟦X⟧) = 1 :=
  C.isSeriesGenerator_formalParam.coeff_one

/-- Let `y` be the `p`-adic Taylor series of `C.translatedY`, let `q = primeNorm d p`, and let
`T = C.formalParam` be the part of `y` in degrees `≡ 1` mod `q - 1`. A series `f` over `ℂ_[p]` lies
in `𝒪[[y]] = C.integralSeriesRing` if and only if `f = g(T)` for some power series `g` with
coefficients in the valuation ring `valRingCp p`. -/
lemma mem_integralSeriesRing_iff_exists_subst_formalParam {f : ℂ_[p]⟦X⟧} :
    f ∈ C.integralSeriesRing ↔ ∃ g : (valRingCp p)⟦X⟧, f = subst C.formalParam (seriesToCp g) :=
  C.isSeriesGenerator_formalParam.mem_iff f

/-- Taking the part of a series in degrees `≡ r` mod `q - 1`, where `q = primeNorm d p`, commutes
with the substitution of the formal parameter. -/
lemma congruencePart_subst_formalParam (r : ℕ) (f : ℂ_[p]⟦X⟧) :
    congruencePart (primeNorm d p - 1) r (f.subst C.formalParam) =
      (congruencePart (primeNorm d p - 1) r f).subst C.formalParam :=
  congruencePart_subst C.constantCoeff_formalParam (congruencePart_congruencePart _) r f

/-- Let `d` be a prime `≡ 7 mod 8`, `p` a prime with fixed `p`-adic place `ιₚ`, `q = primeNorm d p`
(`p²` if `(p/d) = -1`, else `p`), `π = piPrime d p` (`√-d` if `p = d`, else `p`; `piPrimeInt d` is
`ιₚ π` in the valuation ring of `ℂ_[p]`), and `T = C.formalParam` the part in degrees `≡ 1` mod
`q - 1` of the `p`-adic Taylor series of `C.translatedY`. If `T(π z) = g(T)` with `g = π z + ⋯` an
integral series (`seriesToCp g` as a series over `ℂ_[p]`) supported in degrees `1 + i (q - 1)`, then
the coefficient of `z ^ q` in `g` is a unit. -/
lemma isUnit_coeff_primeNorm_of_rescale_formalParam_eq {g : (valRingCp p)⟦X⟧}
    (hg : rescale (ιₚ (piPrime d p)) C.formalParam = subst C.formalParam (seriesToCp g))
    (h_degree : ∀ n : ℕ, coeff n g ≠ 0 → ∃ i : ℕ, n = 1 + i * (primeNorm d p - 1))
    (hg₁ : coeff 1 g = piPrimeInt d) : IsUnit (coeff (primeNorm d p) g) := by
  -- The order of `g` modulo the maximal ideal is `C.insepDegree π ≤ q`, computed with `T` in place
  -- of `y`. If the coefficient were not a unit, this order would exceed `q`.
  by_contra hb₁
  have hq : 1 < primeNorm d p := one_lt_primeNorm d p
  have hT_mem := (C.isSeriesGenerator_formalParam (p := p)).generator_mem
  have hT_order : C.reducedOrder (C.formalParam : ℂ_[p]⟦X⟧) = 1 :=
    C.reducedOrder_eq_one hT_mem C.constantCoeff_formalParam (by simp [coeff_one_formalParam])
  have h_order : (g.map (residue (valRingCp p))).order = C.insepDegree (piPrime d p) := calc
    _ = C.reducedOrder (rescale (ιₚ (piPrime d p)) C.formalParam) := by
      rw [hg, C.reducedOrder_subst hT_mem C.constantCoeff_formalParam, hT_order, mul_one]
    _ = _ := by rw [C.reducedOrder_rescale (piPrime_mem_quadInt d) hT_mem, hT_order, one_mul]
  have h_lt : (primeNorm d p + 1 : ℕ) ≤ (g.map (residue (valRingCp p))).order := by
    refine nat_le_order _ _ fun n hn ↦ ?_
    rw [coeff_map, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
    intro h_unit
    obtain ⟨i, rfl⟩ := h_degree n h_unit.ne_zero
    rcases i with _ | _ | i
    · rw [zero_mul, add_zero, hg₁] at h_unit
      exact not_isUnit_piPrimeInt h_unit
    · rw [zero_add, one_mul, Nat.add_sub_cancel' hq.le] at h_unit
      exact hb₁ h_unit
    · rw [add_mul, add_mul] at hn
      omega
  exact Nat.not_succ_le_self _
    (mod_cast h_lt.trans (h_order.trans_le C.insepDegree_piPrime_le) :
      primeNorm d p + 1 ≤ primeNorm d p)

/-- Let `d` be a prime `≡ 7 mod 8`, `p` a prime with fixed `p`-adic place `ιₚ`, `q = primeNorm d p`
(`p²` if `(p/d) = -1`, else `p`), `π = piPrime d p` (`√-d` if `p = d`, else `p`; `piPrimeInt d` is
`ιₚ π` in the valuation ring of `ℂ_[p]`), and `T = C.formalParam` the part in degrees `≡ 1` mod
`q - 1` of the `p`-adic Taylor series of `C.translatedY`. Then `T(π z) = g(T)` for an integral
series `g = π z + b₁ z ^ q + ∑_{i ≥ 2} bᵢ z ^ (1 + i (q - 1))` (`seriesToCp g` as a series over
`ℂ_[p]`) with `b₁` a unit. -/
lemma exists_rescale_piPrime_formalParam_eq : ∃ g : (valRingCp p)⟦X⟧,
    rescale (ιₚ (piPrime d p)) C.formalParam = subst C.formalParam (seriesToCp g) ∧
    (∀ n : ℕ, coeff n g ≠ 0 → ∃ i : ℕ, n = 1 + i * (primeNorm d p - 1)) ∧
    coeff 1 g = piPrimeInt d ∧
    IsUnit (coeff (primeNorm d p) g) := by
  have hT := C.isSeriesGenerator_formalParam (p := p)
  have h_mem : rescale (ιₚ (piPrime d p)) C.formalParam ∈ C.integralSeriesRing :=
    C.isSeriesGenerator_translatedY.rescale_mem
      (C.rescale_translatedY_mem_of_mem_quadInt (piPrime_mem_quadInt d)) hT.generator_mem
  obtain ⟨g, hg⟩ := C.mem_integralSeriesRing_iff_exists_subst_formalParam.1 h_mem
  have h_part : congruencePart (primeNorm d p - 1) 1 (seriesToCp g) = seriesToCp g := by
    apply hT.subst_injective
    rw [← congruencePart_subst_formalParam, ← hg, congruencePart_rescale, formalParam,
      congruencePart_congruencePart]
  have hg₀ : coeff 0 g = 0 := by
    simpa [constantCoeff_rescale, constantCoeff_subst_eq C.constantCoeff_formalParam,
      constantCoeff_formalParam, constantCoeff_seriesToCp] using (congrArg constantCoeff hg).symm
  have hg₁ : coeff 1 g = piPrimeInt d := by
    simpa [← Subtype.coe_inj, coe_piPrimeInt, coeff_seriesToCp, coeff_rescale,
      coeff_one_subst C.constantCoeff_formalParam, coeff_one_formalParam]
      using (congrArg (coeff 1) hg).symm
  have h_degree (n : ℕ) (hn : coeff n g ≠ 0) : ∃ i : ℕ, n = 1 + i * (primeNorm d p - 1) := by
    have h_mod : n ≡ 1 [MOD primeNorm d p - 1] := by
      by_contra h_mod
      refine hn ?_
      rw [← ZeroMemClass.coe_eq_zero, ← coeff_seriesToCp, ← h_part, coeff_congruencePart,
        ite_eq_right h_mod]
    have h_pos : 1 ≤ n := Nat.pos_of_ne_zero fun hn₀ ↦ hn (by rw [hn₀, hg₀])
    exact ((Nat.modEq_iff_exists_eq_add h_pos).1 h_mod.symm).imp fun i hi ↦ by simp [hi, mul_comm]
  exact ⟨g, hg, h_degree, hg₁, C.isUnit_coeff_primeNorm_of_rescale_formalParam_eq hg h_degree hg₁⟩

open scoped Classical in
/-- Let `d` be a prime `≡ 7 mod 8`, `p` a prime, and `ιₚ : ℂ → ℂ_p` the fixed `p`-adic place. Let
`q = primeNorm d p` (`p²` if `(p/d) = -1`, else `p`), and let `T = C.formalParam` be the part in
degrees `≡ 1` mod `q - 1` of the `p`-adic Taylor series of `C.translatedY`. There is `ϖ ∈ ℂ_[p]`
with `‖ϖ‖ = p ^ (-ρ_p)`, where `ρ_p = varpiValuation d p` is `1/(p-1)`, `1/(p²-1)`, `1/(2p-2)` for
`p` split, inert, ramified in `ℚ(√-d)`, such that `Y = T(ϖ z) / ϖ` is integral (`seriesToCp Y` is
`Y` as a series over `ℂ_[p]`), and `Y - Y ^ q ≡ z` and `Y ≡ ∑_{j ≥ 0} z ^ q ^ j` modulo
`piPrimeInt d = ιₚ π_p`, where `π_p` is `√-d` if `p = d` and `p` otherwise. -/
lemma exists_scaled_formalParam : ∃ (ϖ : ℂ_[p]) (Y : (valRingCp p)⟦X⟧),
    ‖ϖ‖ = (p : ℝ) ^ (-varpiValuation d p) ∧
    rescale ϖ C.formalParam = ϖ • seriesToCp Y ∧
    PowerSeries.C (piPrimeInt d) ∣ Y - Y ^ primeNorm d p - X ∧
    ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0 := by
  have hT₀ := C.constantCoeff_formalParam (p := p)
  have hq : 1 + (primeNorm d p - 1) = primeNorm d p :=
    Nat.add_sub_cancel' (one_lt_primeNorm d p).le
  -- Write `T(π z) = g(T)` with `g = π z + b₁ z ^ q + ⋯` and take `ϖ ^ (q - 1) = -π / b₁`.
  obtain ⟨g, hg, h_degree, hg₁, b₁, hb₁⟩ := C.exists_rescale_piPrime_formalParam_eq (p := p)
  set π : valRingCp p := piPrimeInt d
  have hπ : (π : ℂ_[p]) = ιₚ (piPrime d p) := coe_piPrimeInt d
  have hπ₀ : π ≠ 0 := by simp [← ZeroMemClass.coe_eq_zero, hπ, piPrime_ne_zero]
  have hπ_norm : ‖(π : ℂ_[p])‖ < 1 := by simpa only [hπ] using norm_piPrime_lt_one d
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : ℂ_[p], ϖ ^ (primeNorm d p - 1) = (π * -b₁⁻¹ : valRingCp p) :=
    IsAlgClosed.exists_pow_nat_eq _ (NeZero.pos (primeNorm d p - 1))
  have hϖ_norm : ‖ϖ‖ = (p : ℝ) ^ (-varpiValuation d p) :=
    norm_eq_rpow_neg_varpiValuation_of_pow_eq b₁⁻¹.isUnit.neg hϖ
  have hϖ₀ : ϖ ≠ 0 :=
    norm_pos_iff.1 (hϖ_norm.trans_gt (Real.rpow_pos_of_pos (mod_cast NeZero.pos p) _))
  obtain ⟨E, hE, h_scaled⟩ : ∃ E : (valRingCp p)⟦X⟧, X ^ 2 ∣ E ∧ rescale ϖ (seriesToCp g) =
      (ϖ * π) • seriesToCp (X - X ^ (1 + (primeNorm d p - 1)) + .C π * E) :=
    exists_rescale_eq_smul_X_sub_X_pow (NeZero.ne _) hπ₀ h_degree hg₁ (by rw [hq, hb₁]) hϖ
  rw [hq] at h_scaled
  -- The series `Y' = T(ϖ z) / ϖ` satisfies `Y'(π z) / π = Y' - Y' ^ q + π E(Y')`.
  set Y' : ℂ_[p]⟦X⟧ := ϖ⁻¹ • rescale ϖ C.formalParam with hY'
  have hY'₀ : constantCoeff Y' = 0 := by simp [hY', constantCoeff_rescale, hT₀]
  have hY'₁ : coeff 1 Y' = 1 := by simp [hY', coeff_rescale, coeff_one_formalParam, hϖ₀]
  have hTY : rescale ϖ C.formalParam = ϖ • Y' := (smul_inv_smul₀ hϖ₀ _).symm
  have h_eq : rescale (π : ℂ_[p]) Y' =
      (π : ℂ_[p]) • subst Y' (seriesToCp (X - X ^ primeNorm d p + .C π * E)) := by
    have hY'_subst : HasSubst Y' := .of_constantCoeff_zero' hY'₀
    calc rescale (π : ℂ_[p]) Y' = ϖ⁻¹ • rescale ϖ (rescale (π : ℂ_[p]) C.formalParam) := by
          rw [hY', rescale_smul, rescale_rescale, rescale_rescale, mul_comm]
      _ = ϖ⁻¹ • subst Y' (rescale ϖ (seriesToCp g)) := by
          rw [subst_rescale_eq_subst_smul Y' hY'_subst, ← hTY, ← rescale_subst hT₀, ← hg, hπ]
      _ = _ := by rw [h_scaled, subst_smul hY'_subst, mul_smul, inv_smul_smul₀ hϖ₀]
  obtain ⟨Y, hY, h_dvd⟩ : ∃ Y : (valRingCp p)⟦X⟧,
      seriesToCp Y = Y' ∧ .C π ∣ Y - Y ^ primeNorm d p - X :=
    exists_seriesToCp_eq_of_rescale_eq hπ₀ hπ_norm (one_lt_primeNorm d p) hE hY'₀ hY'₁ h_eq
  have hY₀ : constantCoeff Y = 0 := by simpa [← hY, constantCoeff_seriesToCp] using hY'₀
  refine ⟨ϖ, Y, hϖ_norm, by rw [hTY, hY], h_dvd, ?_⟩
  obtain ⟨e, he, hqe⟩ := exists_primeNorm_eq_pow d p
  rw [hqe] at h_dvd ⊢
  exact dvd_coeff_sub_of_C_dvd_sub_pow_sub_X not_isUnit_piPrimeInt (piPrimeInt_dvd_natCast d) he hY₀
    h_dvd

/-- Let `d` be a prime `≡ 7 mod 8` and `p` a prime with fixed `p`-adic place `ιₚ : ℂ → ℂ_p`. Suppose
`g` is an integral power series in `y`, the `p`-adic Taylor series of `C.translatedY` (that is,
`g ∈ C.integralSeriesRing`). Suppose also `‖ϖ‖ ≤ p ^ (-ρ_p)`, with `ρ_p = varpiValuation d p` equal
to `1/(p-1)`, `1/(p²-1)`, `1/(2p-2)` for `p` split, inert, ramified in `ℚ(√-d)`. Then `g(ϖ z)` has
integral coefficients (it lies in the range of `seriesToCp`). -/
lemma rescale_mem_range_seriesToCp {ϖ : ℂ_[p]} (hϖ : ‖ϖ‖ ≤ (p : ℝ) ^ (-varpiValuation d p))
    {g : ℂ_[p]⟦X⟧} (hg : g ∈ C.integralSeriesRing) : rescale ϖ g ∈ seriesToCp.range := by
  obtain ⟨ϖ₀, Y, hϖ₀ : ‖ϖ₀‖ = (p : ℝ) ^ (-varpiValuation d p),
    hY : rescale ϖ₀ C.formalParam = ϖ₀ • seriesToCp Y, -, -⟩ := C.exists_scaled_formalParam
  have h_le : (p : ℝ) ^ (-varpiValuation d p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (mod_cast (Fact.out : p.Prime).one_le) (neg_nonpos.2 (varpiValuation_nonneg d p))
  obtain ⟨f, rfl⟩ : ∃ f : (valRingCp p)⟦X⟧, g = subst C.formalParam (seriesToCp f) :=
    C.mem_integralSeriesRing_iff_exists_subst_formalParam.1 hg
  -- `g(ϖ₀ z)` is an integral series in `ϖ₀ Y`.
  have h_scaled (n : ℕ) : ‖coeff n (rescale ϖ₀ (subst C.formalParam (seriesToCp f)))‖ ≤ 1 := by
    have h_mem : rescale ϖ₀ C.formalParam ∈ integralBelow p (n + 1) := by
      refine mem_integralBelow.2 fun k _ ↦ ?_
      rw [hY, coeff_smul, norm_smul, hϖ₀, coeff_seriesToCp]
      exact (mul_le_of_le_one_left (norm_nonneg _) h_le).trans (coeff k Y).property
    rw [rescale_subst C.constantCoeff_formalParam]
    exact mem_integralBelow.1 (subst_seriesToCp_mem_integralBelow
      (by simp [constantCoeff_rescale, constantCoeff_formalParam]) h_mem f) n n.lt_succ_self
  refine mem_range_seriesToCp.2 fun n ↦ le_trans ?_ (h_scaled n)
  simp only [coeff_rescale, norm_mul, norm_pow, hϖ₀]
  gcongr

/-- If `g` is an integral series in `y`, the `p`-adic Taylor series of `C.translatedY` (that is,
`g ∈ C.integralSeriesRing`), then its coefficients in degrees below `q = primeNorm d p` are
integral. -/
lemma norm_coeff_le_one_of_lt {g : ℂ_[p]⟦X⟧} (hg : g ∈ C.integralSeriesRing) {n : ℕ}
    (hn : n < primeNorm d p) : ‖coeff n g‖ ≤ 1 := by
  -- `g` is an integral series in the formal parameter `T = z + O(z ^ q)`.
  obtain ⟨f, rfl⟩ := C.mem_integralSeriesRing_iff_exists_subst_formalParam.1 hg
  have h_mem : C.formalParam ∈ integralBelow p (primeNorm d p) := by
    refine mem_integralBelow.2 fun k hk ↦ ?_
    rcases k with _ | _ | k
    · simp [constantCoeff_formalParam]
    · simp [coeff_one_formalParam]
    · have h_mod : ¬k + 2 ≡ 1 [MOD primeNorm d p - 1] := fun h_mod ↦ by
        have := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' (by omega)).1 h_mod.symm)
        omega
      simp [formalParam, coeff_congruencePart, h_mod]
  exact mem_integralBelow.1
    (subst_seriesToCp_mem_integralBelow C.constantCoeff_formalParam h_mem f) n hn

end CMLattice

end New
