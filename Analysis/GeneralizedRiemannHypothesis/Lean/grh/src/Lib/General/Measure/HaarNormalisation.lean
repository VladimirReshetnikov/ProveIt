import Lib.Adelic.Hecke.Basic

/-!
# Uniqueness of Haar measure, integrals over subgroups and Gaussian normalisation of volumes

The file treats three topics of measure theory. Two additive Haar measures on a locally compact,
second countable group agree if some real function has integral 1 for both. Integrals over compact
or open subgroups are computed by translation invariance, orthogonality of characters and reduction
to finite sums. A normalisation of volumes by Gaussian integrals is defined. It holds for `ℝ` and
`ℂ` and passes to binary products and finite powers under σ-finiteness assumptions.

## Main definitions and results

* `New.addHaar_eq_of_integral_eq_one`: uniqueness of additive Haar measure, with the constant fixed
  by the integral of one test function.
* `New.setIntegral_char`: orthogonality for a multiplicative function over an open subgroup.
* `New.setIntegral_eq_finsum`: over a compact `M`, a function constant on the cosets of an open
  subgroup `L` integrates to `ν (L ∩ M)` times a finite sum over `M ⧸ (L ∩ M)`.
* `New.HasGaussianIntegral`: the Gaussian normalisation of a volume.
* `New.HasGaussianIntegral.pi`: the normalisation on a finite power.
* `New.lintegral_inv_add_rpow`: the integral of `(c + q x) ^ (-s)`, computed through the Gamma
  function.
-/

/-! ## Uniqueness of Haar measure -/

section HaarUnique

open MeasureTheory

/-- Let `μ` and `ν` be additive Haar measures on a locally compact, second countable group. If some
real function has integral 1 for both, then `μ = ν`. -/
lemma New.addHaar_eq_of_integral_eq_one {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ ν : Measure G} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {f : G → ℝ} (hν : ∫ x : G, f x ∂ν = 1) (hμ : ∫ x : G, f x ∂μ = 1) :
    μ = ν := by
  -- By uniqueness `μ = c • ν` for a constant `c`, and the two integrals give `c = 1`.
  obtain ⟨c, rfl⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, μ.isAddLeftInvariant_eq_smul ν⟩
  obtain rfl : c = 1 := by simpa [integral_smul_nnreal_measure, hν, NNReal.smul_def] using hμ
  exact one_smul _ ν

end HaarUnique

/-!
## Integrals over subgroups

Integrals over a subgroup `M` of a topological abelian group `V`, for a translation-invariant Borel
measure `ν`.
-/

section SubgroupIntegral

open MeasureTheory AddSubgroup Set

namespace New

variable {V X : Type*} [AddCommGroup V] [MeasurableSpace V] {ν : Measure V} [ν.IsAddLeftInvariant]
  {M L : AddSubgroup V} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [BorelSpace V]

/-- For a left-invariant measure `ν` and a subgroup `M`, the integral over `M` is unchanged by
translating the integrand by an element of `M`. -/
lemma setIntegral_add_left_eq_self_of_mem (F : V → X) {m : V} (hm : m ∈ M) :
    ∫ x : V in M, F (m + x) ∂ν = ∫ x : V in M, F x ∂ν := by
  -- Change variables by the translation `x ↦ m + x`, which preserves `ν` and maps `M` onto `M`.
  have h_preimage : (m + ·) ⁻¹' (M : Set V) = M := Set.ext fun x ↦ M.add_mem_cancel_left hm
  simpa [h_preimage] using (measurePreserving_add_left ν m).setIntegral_preimage_emb
    (measurableEmbedding_addLeft m) F M

open scoped Classical in
/-- Orthogonality: let `ν` be a left-invariant measure on `V` and `χ : V → ℂ` satisfy
`χ (x + y) = χ x * χ y`. The integral of `χ` over an open subgroup `M` is the measure of `M` (read
as `0` if infinite) when `χ = 1` on `M`, and `0` otherwise. -/
lemma setIntegral_char (hM : IsOpen (M : Set V)) {χ : V → ℂ}
    (h_add : ∀ x y : V, χ (x + y) = χ x * χ y) :
    ∫ x : V in M, χ x ∂ν = if ∀ x ∈ M, χ x = 1 then (ν.real M : ℂ) else 0 := by
  split_ifs with h_triv
  · simp [setIntegral_congr_fun hM.measurableSet h_triv]
  · -- Translating by `m ∈ M` multiplies the integral by `χ m` and leaves it unchanged,
    -- and some `χ m` is not `1`.
    obtain ⟨m, hm, hm_ne⟩ : ∃ m ∈ M, χ m ≠ 1 := by simpa using h_triv
    have h_mul : χ m * ∫ x : V in M, χ x ∂ν = ∫ x : V in M, χ x ∂ν := by
      simp only [← integral_const_mul, ← h_add, setIntegral_add_left_eq_self_of_mem χ hm]
    exact eq_zero_of_mul_eq_self_left hm_ne h_mul

/-- Let `M` be a compact and `L` an open subgroup of `V`, and `ν` a left-invariant measure that is
finite on compact sets. If `F` is constant on the cosets of `L ∩ M` in `M`, its integral over `M` is
`ν (L ∩ M)` times the sum of its values on these cosets; `q.out` is a chosen representative of the
coset `q`. -/
lemma setIntegral_eq_finsum [IsFiniteMeasureOnCompacts ν] [CompleteSpace X] [T2Space V]
    (hM : IsCompact (M : Set V)) (hL : IsOpen (L : Set V)) {F : V → X}
    (hF : ∀ x y : M, -(x : V) + y ∈ L → F y = F x) :
    ∫ x : V in M, F x ∂ν = ν.real (L ∩ M) • ∑ᶠ q : M ⧸ L.addSubgroupOf M, F q.out := by
  classical
  -- `M` is compact and `L` is open, so there are finitely many cosets.
  have : Fintype (M ⧸ L.addSubgroupOf M) := fintypeOfIndexNeZero (hM.relIndex_ne_zero_add hL)
  -- On `M`, `F` is the sum over the cosets `q` of the constant `F q.out` on `q.out + L`.
  let G (q : M ⧸ L.addSubgroupOf M) (x : V) : X := indicator L (fun _ ↦ F q.out) (-q.out + x)
  have h_sum : EqOn F (fun x : V ↦ ∑ q : M ⧸ L.addSubgroupOf M, G q x) M := by
    intro x hx
    let q₀ : M ⧸ L.addSubgroupOf M := QuotientAddGroup.mk ⟨x, hx⟩
    have h_coset (q : M ⧸ L.addSubgroupOf M) : -(q.out : V) + x ∈ L ↔ q = q₀ := by
      rw [← q.out_eq', QuotientAddGroup.eq]
      simp [mem_addSubgroupOf]
    simp [G, indicator, h_coset, hF q₀.out ⟨x, hx⟩ ((h_coset q₀).2 rfl)]
  have h_int (q : M ⧸ L.addSubgroupOf M) : IntegrableOn (G q) M ν :=
    (integrableOn_const hM.measure_ne_top).indicator (measurable_const_add _ hL.measurableSet)
  -- Translating by `-q.out ∈ M` moves the coset to `L` and keeps the integral over `M`.
  have h_integral (q : M ⧸ L.addSubgroupOf M) :
      ∫ x : V in M, G q x ∂ν = ν.real (L ∩ M) • F q.out := by
    rw [setIntegral_add_left_eq_self_of_mem (indicator L fun _ ↦ F q.out)
      (M.neg_mem (SetLike.coe_mem q.out))]
    simp [hL.measurableSet]
  rw [setIntegral_congr_fun hM.measurableSet h_sum, integral_finsetSum _ fun q _ ↦ h_int q]
  simp [h_integral, finsum_eq_sum_of_fintype, Finset.smul_sum]

end New

end SubgroupIntegral

/-!
## Volumes normalised by a Gaussian integral

A way to fix the normalisation of a volume without choosing a basis. For σ-finite volumes it passes
to binary products and finite powers, with the sum of the functions and the sum of the exponents.
-/

namespace New

open MeasureTheory Real GaussianFourier Finset Fintype

/-- If `f` is nonnegative almost everywhere and its Bochner integral is `v ≠ 0`, then its lower
Lebesgue integral is `v`. No integrability is assumed: it follows from `v ≠ 0`. -/
lemma lintegral_ofReal_eq_of_integral_eq {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {f : β → ℝ} {v : ℝ} (hv : ∫ x : β, f x ∂ν = v) (hv_ne : v ≠ 0) (hf : 0 ≤ᵐ[ν] f) :
    ∫⁻ x : β, ENNReal.ofReal (f x) ∂ν = ENNReal.ofReal v := by
  rw [← ofReal_integral_eq_lintegral_ofReal (.of_integral_ne_zero (hv.trans_ne hv_ne)) hf, hv]

/-- The Gamma integral as a lower integral: for positive `b`, `r` and `K`, the integral of
`K t ^ (b - 1) exp (-r t)` over `t > 0` is `K r ^ (-b) Γ(b)`. -/
lemma lintegral_const_mul_rpow_mul_exp_neg_mul_Ioi {b r K : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hK : 0 < K) :
    ∫⁻ t : ℝ in Set.Ioi 0, ENNReal.ofReal (K * (t ^ (b - 1) * rexp (-(r * t)))) =
      ENNReal.ofReal (K * ((1 / r) ^ b * Gamma b)) := by
  refine lintegral_ofReal_eq_of_integral_eq ?_ (by positivity)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) ↦ by positivity)
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi hb hr]

variable {V : Type} {W : Type} [MeasureSpace V] [MeasureSpace W]
  {q : V → ℝ} {q' : W → ℝ} {a b : ℝ} {ι : Type} [Fintype ι]
  [SigmaFinite (volume : Measure V)] [SFinite (volume : Measure W)]

/-- Gaussian normalisation of the volume on `V` for the real function `q` with exponent `a`: for
every `t > 0`, the integral of `exp (-t * q x)` over `V` equals `(π / t) ^ a`. -/
class HasGaussianIntegral (a : outParam ℝ) (q : outParam (V → ℝ)) : Prop where
  /-- For `t > 0`, the integral of `exp (-t * q x)` over `V` is `(π / t) ^ a`. -/
  integral_exp_eq {t : ℝ} : 0 < t → ∫ x : V, exp (-t * q x) = (π / t) ^ a

/-- Let the volume on `V` be σ-finite with `∫ exp (-t q) = (π / t) ^ a` for all `t > 0`, and let
`q ≥ 0` be measurable. For `c > 0`, `s > 0` and `a < s`, the lower integral of `(c + q) ^ (-s)` is
`π ^ a c ^ (a - s) Γ(s - a) / Γ(s)`. -/
lemma lintegral_inv_add_rpow [h : HasGaussianIntegral a q] {s c : ℝ} (hc : 0 < c) (ha : a < s)
    (hq_nonneg : ∀ x : V, 0 ≤ q x) (hs : 0 < s) (hq : Measurable q := by fun_prop) :
    ∫⁻ x : V, ENNReal.ofReal ((c + q x)⁻¹ ^ s) =
      ENNReal.ofReal (π ^ a / Gamma s * ((1 / c) ^ (s - a) * Gamma (s - a))) := by
  -- Write `(c + q x)⁻¹ ^ s` as the Gamma integral `Γ(s)⁻¹ ∫ t ^ (s - 1) exp (-(c + q x) t) dt`,
  -- swap the integrals, integrate in `x` by `HasGaussianIntegral.integral_exp_eq`, and read the
  -- result as a Gamma integral.
  let F (x : V) (t : ℝ) : ℝ := (Gamma s)⁻¹ * (t ^ (s - 1) * rexp (-((c + q x) * t)))
  have h_point (x : V) :
      ENNReal.ofReal ((c + q x)⁻¹ ^ s) = ∫⁻ t : ℝ in Set.Ioi 0, ENNReal.ofReal (F x t) := by
    have h_pos : 0 < c + q x := add_pos_of_pos_of_nonneg hc (hq_nonneg x)
    have h_cancel : (c + q x)⁻¹ ^ s = (Gamma s)⁻¹ * ((1 / (c + q x)) ^ s * Gamma s) := by
      field_simp
    rw [h_cancel, lintegral_const_mul_rpow_mul_exp_neg_mul_Ioi hs h_pos (by positivity)]
  have h_slice (t : ℝ) (ht : 0 < t) : ∫⁻ x : V, ENNReal.ofReal (F x t) =
      ENNReal.ofReal (π ^ a / Gamma s * (t ^ (s - a - 1) * rexp (-(c * t)))) := by
    refine lintegral_ofReal_eq_of_integral_eq ?_ (by positivity)
      (.of_forall fun x ↦ show 0 ≤ F x t by positivity)
    have h_split (x : V) :
        F x t = (Gamma s)⁻¹ * t ^ (s - 1) * rexp (-(c * t)) * rexp (-t * q x) := by
      simp only [F, mul_assoc, ← exp_add]
      ring_nf
    calc ∫ x : V, F x t
      _ = (Gamma s)⁻¹ * t ^ (s - 1) * rexp (-(c * t)) * (π / t) ^ a := by
        simp only [h_split, integral_const_mul, h.integral_exp_eq ht]
      _ = π ^ a / Gamma s * (t ^ (s - a - 1) * rexp (-(c * t))) := by
        rw [div_rpow pi_pos.le ht.le, sub_right_comm, rpow_sub ht (s - 1) a]
        ring
  rw [lintegral_congr h_point, lintegral_lintegral_swap (by fun_prop),
    setLIntegral_congr_fun measurableSet_Ioi h_slice,
    lintegral_const_mul_rpow_mul_exp_neg_mul_Ioi (sub_pos.2 ha) hc (by positivity)]

/-- The Gaussian integral on `ℝ`: the integral of `exp (-t x²)` is `(π / t) ^ (1 / 2)`. -/
instance : HasGaussianIntegral (1 / 2) fun x : ℝ ↦ x ^ 2 where
  integral_exp_eq {t} _ := by rw [integral_gaussian t, sqrt_eq_rpow]

/-- The Gaussian integral on `ℂ`: the integral of `exp (-t ‖z‖²)` is `π / t`. -/
instance : HasGaussianIntegral 1 fun z : ℂ ↦ ‖z‖ ^ 2 where
  integral_exp_eq ht := by simpa using integral_rexp_neg_mul_sq_norm (V := ℂ) ht

/-- If the volumes on `V` (σ-finite) and `W` (s-finite) satisfy `∫ exp (-t q) = (π / t) ^ a` and
`∫ exp (-t q') = (π / t) ^ b` for all `t > 0`, then the volume on `V × W` satisfies the same with
exponent `a + b` for the sum of `q` and `q'`. -/
instance [h : HasGaussianIntegral a q] [h' : HasGaussianIntegral b q'] :
    HasGaussianIntegral (a + b) fun x : V × W ↦ q x.1 + q' x.2 where
  integral_exp_eq {t} ht :=
    -- Fubini applies, since the Gaussian of the sum is a product.
    calc ∫ x : V × W, exp (-t * (q x.1 + q' x.2))
      _ = (∫ v : V, exp (-t * q v)) * ∫ w : W, exp (-t * q' w) := by
        simp only [mul_add, exp_add, Measure.volume_eq_prod, ← integral_prod_mul]
      _ = (π / t) ^ (a + b) := by
        rw [h.integral_exp_eq ht, h'.integral_exp_eq ht, rpow_add (by positivity)]

/-- If the volume on `V` is σ-finite and satisfies `∫ exp (-t q) = (π / t) ^ a` for all `t > 0`,
then the volume on `ι → V` satisfies the same with exponent `a * card ι` for `x ↦ ∑ i, q (x i)`. -/
instance HasGaussianIntegral.pi [h : HasGaussianIntegral a q] :
    HasGaussianIntegral (a * Fintype.card ι) fun x : ι → V ↦ ∑ i : ι, q (x i) where
  integral_exp_eq {t} ht :=
    calc ∫ x : ι → V, exp (-t * ∑ i : ι, q (x i))
      _ = ∫ x : ι → V, ∏ i : ι, exp (-t * q (x i)) := by simp only [mul_sum, exp_sum]
      _ = ((π / t) ^ a) ^ Fintype.card ι := by
        rw [integral_fintype_prod_volume_eq_pow fun v : V ↦ exp (-t * q v), h.integral_exp_eq ht]
      _ = (π / t) ^ (a * Fintype.card ι) := by rw [rpow_mul (by positivity), rpow_natCast]

end New
