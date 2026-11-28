import Lib.PadicHodge.Kisin.Bicommutant
import Lib.PadicHodge.Kisin.KummerChartExistence

/-!
# Bounded poles, φ-fixed elements of B_max, and ratios of periods fixed near 1

The period ring `B = B⁺[1/μ]` (`New.Period.Bmax`, `New.Period.BPlus`) lies inside `B_dR`, and `φ`
denotes its Frobenius. This file shows that bounded poles of the `φ^n y` control the denominators
of `y` in `μ`, and that a `φ`-fixed element of `B` lying in `B_dR⁺` is in `ℚ_[p]`. Using charts
(`New.Lift.Chart`), it shows that a ratio of two periods that is fixed by an open subgroup of `G_p`
lies in `W(𝔽_q)[1/p]` for some `q`.

## Main definitions and results

* `New.Period.pow_smul_mem_range_BPlus`: if the image of `φ^n(y)` in `B_dR` lies in
  `t^(−a)B_dR⁺` for every `n ≥ 0`, then `ν^a y` lies in the image of `B⁺` for every `ν` in `A_inf`
  divisible by `μ`.
* `New.Period.Bmax.exists_padic_eq_of_frobEnd_fixed`: kernel in the fundamental exact sequence: an
  element `y` of `B` with `φ(y) = y` whose image in `B_dR` lies in `B_dR⁺` belongs to `ℚ_[p]`.
* `New.Period.exists_pow_mul_eq_wittFq_mul_of_isChartOf`, `New.Period.Bmax.exists_witt_ratio`: a
  ratio of two periods that is fixed by an open subgroup of `G_p` lies in `W(𝔽_q)[1/p]` for some
  `q`, for a given chart and in general.

Notions from other files:
* `New.Period.BdRPlus`: the ξ-adic completion of B⁺, with fraction field `New.Period.BdR`.
* `New.Period.BPlus`, `New.Period.Bmax`: B⁺ = A_max[1/p] and B = B⁺[1/μ], μ = [ε] − 1.
* `New.Lift.Chart.bicommutant`: the S-algebra S_B of the y in B⁺ whose multiplication commutes with
  every S-linear endomorphism of B⁺ that keeps the image of A_max.

## Relation to the literature

Known; see `Lib.PadicHodge.Crystalline.Regularity` for sources.
-/

/-! ## Bounded poles and φ-fixed elements of B in B_dR⁺ -/

namespace New.Period

open Algebra IsScalarTower IsLocalization.Away algebraMap Function

variable {p : ℕ} [ThePrime p]

/-- Let y ∈ B, a ∈ ℕ, and let ν ∈ A_inf be divisible by μ. If the image of φ^n(y) in B_dR lies
in t^(−a)B_dR^+ for every n ≥ 0, then ν^a y lies in the image of B^+.

Here φ^n(y) is the action of `(ofAdd n, 1)` in `FrobGal`, and `hodgeFil (-a)` is t^(−a)B_dR^+. -/
lemma pow_smul_mem_range_BPlus (y : Bmax) (a : ℕ) {ν : Ainf} (hν : mu ∣ ν)
    (hy : ∀ n : ℕ, ↑((⟨Multiplicative.ofAdd n, 1⟩ : FrobGal) • y) ∈ hodgeFil (-a)) :
    ∃ c : BPlus, c = ν ^ a • y := by
  -- Write `ν = μ s` and `μ ^ N ν ^ a y = c` with `c` in `BPlus`. As long as `N > 0`, `μ` divides
  -- `c` and can be cancelled, so `N` goes down to `0`.
  obtain ⟨s, hs⟩ : ∃ s : Ainf, ν = mu * s := hν
  obtain ⟨N, c, hc⟩ : ∃ (N : ℕ) (c : BPlus),
      ν ^ a • y * algebraMap BPlus Bmax (mu : BPlus) ^ N = algebraMap BPlus Bmax c :=
    surj (mu : BPlus) (ν ^ a • y)
  induction N generalizing c with
  | zero => exact ⟨c, by simpa using hc.symm⟩
  | succ N ih =>
    obtain ⟨d, rfl⟩ : (mu : BPlus) ∣ c := by
      -- `μ` divides whatever has `θ (φ^n ·) = 0` for all `n`, in `Ainf` and hence in `BPlus`;
      -- and `θ (φ^n c) = 0` means `φ^n c ∈ hodgeFil 1`
      refine c.dvd_of_thetaBPlus_frobEnd_eq_zero mu_dvd_of_theta_frobEnd fun n ↦ ?_
      rw [← thetaBdR_algebraMap_BPlus, ← algebraMap_mem_hodgeFil_one_iff]
      set w : BdRPlus := ↑(frobEnd^[n] s ^ a) * ↑(frobEnd^[n] mu) ^ (a + (N + 1)) with hw
      -- apply `φ^n` to `hc` and map it to `BdR`
      have h_eq :
          (((frobEnd^[n] c : BPlus) : BdRPlus) : BdR) = ↑((⟨.ofAdd n, 1⟩ : FrobGal) • y) * ↑w := by
        have hc_frob : (((⟨.ofAdd n, 1⟩ : FrobGal) • algebraMap BPlus Bmax c : Bmax) : BdR) =
            (((⟨.ofAdd n, 1⟩ : FrobGal) •
              (ν ^ a • y * algebraMap BPlus Bmax (mu : BPlus) ^ (N + 1)) : Bmax) : BdR) := by
          rw [hc]
        simpa [hs, hw, smul_def, ← algebraMap_apply, FrobGal.smul_def, pow_add, mul_pow,
          mul_comm, mul_left_comm, mul_assoc] using hc_frob
      -- `ξ` divides `φ^n μ`, so `w ∈ hodgeFil (a + N + 1)`, while `φ^n y ∈ hodgeFil (-a)`
      have h_xi : xi ∣ frobEnd^[n] mu := theta_eq_zero_iff_xi_dvd.mp (theta_iterate_frobEnd_mu n)
      have hw_mem : (w : BdR) ∈ hodgeFil (a + (N + 1) : ℕ) :=
        algebraMap_mem_hodgeFil_iff_xi_pow_dvd.mpr
          ((pow_dvd_pow_of_dvd (map_dvd _ h_xi) _).mul_left _)
      simpa only [h_eq] using hodgeFil_anti (by lia) (mul_mem_hodgeFil (hy n) hw_mem)
    -- cancel one factor `μ` in `hc`
    refine ih d ((algebraMap_isUnit (mu : BPlus)).mul_left_cancel ?_)
    rw [← map_mul, ← hc]
    ring

/-- Kernel in the fundamental exact sequence: an element y of B with φ(y) = y whose image in
B_dR lies in B_dR^+ belongs to Q_p. -/
lemma Bmax.exists_padic_eq_of_frobEnd_fixed {y : Bmax} (hy : frobEnd y = y) {x : BdRPlus}
    (hx : (y : BdR) = x) :
    ∃ a : ℚ_[p], a = y := by
  -- All `φ^n y = y` lie in `hodgeFil 0`, so `y` comes from a `φ`-fixed `c` in `BPlus`. A multiple
  -- `p ^ m c` comes from `Amax`, so by contraction `p ^ (m + 1) c` comes from `Ainf`, where the
  -- fixed points of `φ` lie in `ℤ_[p]`.
  have h_mem (n : ℕ) :
      ↑((⟨Multiplicative.ofAdd n, 1⟩ : FrobGal) • y) ∈ hodgeFil (-((0 : ℕ) : ℤ)) := by
    simp [FrobGal.smul_def, iterate_fixed hy, hx]
  obtain ⟨c, rfl⟩ : ∃ c : BPlus, c = y := by
    simpa using pow_smul_mem_range_BPlus y 0 dvd_rfl h_mem
  have hc : frobEnd c = c := by simpa [injective_BPlus_Bmax.eq_iff] using hy
  obtain ⟨m, w, hw⟩ : ∃ (m : ℕ) (w : Amax), p ^ m * c = w := c.exists_p_pow_mul_eq_amax
  have h_amax : ∀ v ∈ ({p ^ m * c} : Set BPlus), v ∈ amaxImage :=
    fun v hv ↦ ⟨w, hw.symm.trans hv.symm⟩
  have h_frob : ∀ v ∈ ({p ^ m * c} : Set BPlus),
      ∃ w ∈ ({p ^ m * c} : Set BPlus), xi ^ 0 • v = (1 : Ainf) • frobEnd w := by
    simp [hc]
  obtain ⟨a, ha⟩ : ∃ a : Ainf, a = p ^ 1 * (p ^ m * c) :=
    exists_Ainf_eq_of_contraction {p ^ m * c} 0 1 h_amax h_frob _ rfl
  have ha_fixed : frobEnd a = a := (coe_inj _ BPlus).mp (by simp [← frobEnd_algebraMap, ha, hc])
  obtain ⟨b, rfl⟩ : ∃ b : ℤ_[p], algebraMap ℤ_[p] Ainf b = a :=
    exists_algebraMap_eq_of_frobenius_eq a (by rwa [← frobEnd_eq_frobenius])
  refine ⟨b / (p * p ^ m), (coe_inj _ BdR).mp ?_⟩
  -- after clearing the denominator this is the image of `ha` in `BdR`
  simpa [field, algebraMap_apply _ ℚ_[p] BdR b, NeZero.ne, ← algebraMap_apply] using
    congrArg (algebraMap BPlus BdR) ha

end New.Period

/-!
## Regularity of the period ring B

A chart (`New.Lift.Chart`) is a map `W(𝔽_q)⟦X⟧ → A_inf` with image `S = c.S`, sending `X` to
`z = c.z`. For `j : Γ → G_p`, `c.IsChartOf j` says that every `g` in `G_p` that fixes `θ(S)`
pointwise lies in `j Γ`. `c.extendToBPlus f` extends an `S`-linear map `f` of `A_inf` to `B⁺`,
linearly over `c.bicommutant`. `New.Period.localFieldOf Γ` is the subfield of `Q̄_p` fixed by `j Γ`,
and `New.Lift.WittFq f` is `W(𝔽_{p^f})`.
-/

namespace New

open Period BPlus BdRPlus Lift Polynomial IsLocalization IsScalarTower Algebra IsSeparable
  algebraMap

variable {p : ℕ} [ThePrime p] {Γ : Type} [Group Γ] [𝒥 : OverGp Γ p] {c : Chart}

/-- Newton's iteration: if `x` is a root of a separable polynomial over `K` and lies in the image
of `T` modulo `π`, then it lies in the image of `T` modulo every power of `π`. -/
lemma exists_pow_dvd_sub_of_separable {K T R : Type*} [Field K] [CommRing T] [CommRing R]
    [Algebra K T] [Algebra K R] [Algebra T R] [IsScalarTower K T R] {P : K[X]} (hP : P.Separable)
    {x π : R} (hx : aeval x P = 0) {t : T} (ht : π ∣ algebraMap T R t - x) (m : ℕ) :
    ∃ s : T, π ^ m ∣ algebraMap T R s - x := by
  -- with `g P' ≡ 1` modulo `P`, the polynomial `F = X - g P` has `F x = x` and `F' x = 0`
  obtain ⟨f₀, g, h_bezout⟩ : ∃ f₀ g : K[X], f₀ * P + g * derivative P = 1 := hP
  let F : K[X] := X - g * P
  have h_gP' : aeval x g * aeval x (derivative P) = 1 := by
    simpa [hx] using congrArg (aeval x) h_bezout
  -- each step squares the modulus, so prove the claim for `π ^ 2 ^ n`
  suffices h_two_pow : ∀ n : ℕ, ∃ s : T, π ^ 2 ^ n ∣ algebraMap T R s - x from
    (h_two_pow m).imp fun s ↦ (pow_dvd_pow π m.lt_two_pow_self.le).trans
  intro n
  induction n with
  | zero => exact ⟨t, by simpa using ht⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    -- by Taylor's formula `F s - x` is a multiple of `(s - x) ^ 2`
    obtain ⟨r, hr⟩ := (F.map (algebraMap K R)).binomExpansion x (algebraMap T R s - x)
    have h_taylor : algebraMap T R (aeval s F) - x = r * (algebraMap T R s - x) ^ 2 := by
      simp_all [aeval_algebraMap_apply, F]
    refine ⟨aeval s F, ?_⟩
    rw [h_taylor, pow_succ, pow_mul]
    exact (pow_dvd_pow_of_dvd hs 2).mul_left r

/-- Let `c` be a chart for `toGp` (`hc`): `c` is a Λ-algebra map Λ[[X]] → A_inf sending X to a
Teichmüller lift z, and every g in G_p fixing Λ pointwise and fixing θ(z) lies in the image of
`toGp`. Let `a l` be finitely many elements of the field fixed by `toGp Γ`, `y l ∈ B⁺`, and `f` a
`c.S`-linear endomorphism of `A_inf`, with chosen `c.S`-linear extension `c.extendToBPlus f` to
`B⁺`. Then `∑ l, a l * y l` divides `∑ l, a l * c.extendToBPlus f (y l)` in `B_dR⁺`. In particular
the second sum vanishes if the first does. -/
lemma Lift.Chart.IsChartOf.dvd_extendToBPlus (hc : c.IsChartOf 𝒥.toGp) {ι : Type*} [Fintype ι]
    (a : ι → PadicAlgCl p) (ha : ∀ l : ι, a l ∈ localFieldOf Γ) (f : Ainf →ₗ[c.S] Ainf)
    (y : ι → BPlus) :
    ∑ l : ι, a l * algebraMap BPlus BdRPlus (y l) ∣
      ∑ l : ι, (a l : BdRPlus) * c.extendToBPlus f (y l) := by
  -- Approximate each `a l` modulo `ξ ^ m` by an element of `c.bicommutant`, over which
  -- `c.extendToBPlus f` is linear: every `ξ ^ m` that divides the first sum then divides the
  -- second, and `BdRPlus` is a DVR with uniformiser `ξ`.
  -- `T` is `c.bicommutant` as a `ℚ_[p]`-subalgebra (`ℤ_[p]`-linear maps on `BPlus` are
  -- `ℚ_[p]`-linear).
  have h_scalar (r : ℚ_[p]) : algebraMap ℚ_[p] BPlus r ∈ c.bicommutant := fun G _ ↦
    LinearMap.ext
      ((linearMap_compatibleSMul (nonZeroDivisors ℤ_[p]) ..).map_smul (G.restrictScalars ℤ_[p]) r)
  let T : Subalgebra ℚ_[p] BPlus := ⟨c.bicommutant.toSubsemiring, h_scalar⟩
  have h_approx (m : ℕ) (l : ι) : ∃ t : T, (xi : BdRPlus) ^ m ∣ t - a l := by
    -- by Galois theory `a l = θ t` with `t` in `T`: what fixes `θ` of `c.S` lies in `toGp Γ`
    have ha_fixed (g : Gp p)
        (hg : ∀ n : ℕ, ∀ x ∈ (c.thetaPhiInvS n).range, x ∈ T.map thetaBPlus → g • x = x) :
        g (a l) = a l := by
      have h_fix (s : c.S) : g • c.thetaPhiInvS 0 s = c.thetaPhiInvS 0 s :=
        hg 0 _ ⟨s, rfl⟩ ⟨_, Chart.ainfToBPlus_mem_bicommutant _, thetaBPlus_ainf _⟩
      have h_const : FixesLambda c.f g := fun b ↦ by
        simpa [smul_algebraMap_wittFq_eq_iff, thetaPhiInv, ← coe_wittToQpBar] using
          h_fix ⟨_, c.S.algebraMap_mem b⟩
      have h_range : g ∈ 𝒥.toGp.range := hc g ⟨h_const, Subtype.ext (h_fix c.z)⟩
      exact ha l ⟨g, h_range⟩
    obtain ⟨t, ht, h_theta⟩ : (a l : ℂ_[p]) ∈ T.map thetaBPlus :=
      c.mem_of_fixed_thetaPhiInvS ha_fixed
    -- so `ξ ∣ t - a l`, which Newton's iteration improves to `ξ ^ m`
    have h_xi_dvd : (xi : BdRPlus) ∣ algebraMap T BdRPlus ⟨t, ht⟩ - a l := by
      simpa [← thetaBdR_eq_zero_iff, sub_eq_zero]
    exact exists_pow_dvd_sub_of_separable (isSeparable ℚ_[p] (a l))
      (by simp [aeval_algebraMap_apply]) h_xi_dvd m
  choose t ht using h_approx
  -- divisibility of `∑ a l * y l` by `ξ ^ m` can be read off in `BPlus`, with `t m l` for `a l`
  -- and `c.E`, an associate of `ξ` that lies in `c.S`, for `ξ`
  have h_iff (m : ℕ) (y : ι → BPlus) :
      algebraMap Ainf BPlus c.E ^ m ∣ ∑ l, (t m l : BPlus) * y l ↔
        (xi : BdRPlus) ^ m ∣ ∑ l, (a l : BdRPlus) * algebraMap BPlus BdRPlus (y l) := by
    have h_sum : (xi : BdRPlus) ^ m ∣
        ∑ l, (((t m l : BPlus) : BdRPlus) - a l) * algebraMap BPlus BdRPlus (y l) :=
      Finset.dvd_sum fun l _ ↦ (ht m l).mul_right _
    calc _ ↔ algebraMap Ainf BPlus xi ^ m ∣ ∑ l, (t m l : BPlus) * y l :=
          (c.associated_E_xi.map _).pow_pow.dvd_iff_dvd_left
      _ ↔ (xi : BdRPlus) ^ m ∣ algebraMap BPlus BdRPlus (∑ l, (t m l : BPlus) * y l) :=
          xi_pow_dvd_iff.symm
      _ ↔ _ := dvd_iff_dvd_of_dvd_sub (by simpa [sub_mul, Finset.sum_sub_distrib] using h_sum)
  -- `c.extendToBPlus f` is linear over `c.bicommutant`, which contains `c.E` and the `t m l`
  have h_pow (m : ℕ) :
      (xi : BdRPlus) ^ m ∣ ∑ l, (a l : BdRPlus) * algebraMap BPlus BdRPlus (y l) →
        (xi : BdRPlus) ^ m ∣
          ∑ l, (a l : BdRPlus) * algebraMap BPlus BdRPlus (c.extendToBPlus f (y l)) := by
    rw [← h_iff m y, ← h_iff m fun l ↦ c.extendToBPlus f (y l)]
    rintro ⟨u, hu⟩
    refine ⟨c.extendToBPlus f u, ?_⟩
    simpa [c.extendToBPlus_mul, pow_mem] using congrArg (c.extendToBPlus f) hu
  -- in a DVR, divisibility is a comparison of valuations, tested on the powers of `ξ`
  simpa [← IsDiscreteValuationRing.addVal_le_iff_dvd, prime_xi.irreducible,
    ENat.forall_natCast_le_iff_le] using h_pow

/-- If a nonzero `x` algebraic over the field `K ⊆ R` equals `z * v` with `z` in `R` and `v`
integral over `R`, then `z` is a unit of `R`. -/
lemma isUnit_of_isIntegral_eq_mul {K R L : Type*} [Field K] [CommRing R] [Field L] [Algebra K R]
    [Algebra R L] [Algebra K L] [IsScalarTower K R L] [FaithfulSMul R L] {x v : L} {z : R}
    (hx : IsIntegral K x) (hx₀ : x ≠ 0) (hv : IsIntegral R v) (hx_eq : x = algebraMap R L z * v) :
    IsUnit z := by
  -- `z` has the inverse `x⁻¹ * v` in the integral closure, and integral extensions reflect units
  have h_faithful : FaithfulSMul R (integralClosure R L) := .tower_bot R _ L
  refine .of_map (algebraMap R (integralClosure R L)) z
    (.of_mul_eq_one ⟨x⁻¹ * v, hx.inv.tower_top.mul hv⟩ (Subtype.ext ?_))
  simpa [mul_left_comm, inv_mul_eq_one₀ hx₀] using hx_eq

/-- Let `c` be a chart for `j = 𝒥.toGp`, let `a` lie in the field fixed by `j Γ`, and let
`B, C ∈ B⁺` satisfy `B = a C` in `B_dR`. Then the `i`-th extended coordinates of the chart satisfy
the same relation: `extendedCoord i B = a * extendedCoord i C` in `B_dR`. -/
lemma Lift.Chart.IsChartOf.extendedCoord_eq_mul_of_eq_mul (hc : c.IsChartOf 𝒥.toGp)
    {a : PadicAlgCl p} (ha : a ∈ localFieldOf Γ) {B C : BPlus}
    (hBC : algebraMap BPlus BdR B = algebraMap (PadicAlgCl p) BdR a * algebraMap BPlus BdR C)
    (i : c.adicBasis.Index) :
    algebraMap BPlus BdR (c.extendedCoord i B) =
      algebraMap (PadicAlgCl p) BdR a * algebraMap BPlus BdR (c.extendedCoord i C) := by
  -- `B - a C` divides `extendedCoord i B - a extendedCoord i C` in `B_dR⁺`, and it is zero
  obtain ⟨q, h_coord⟩ := hc.dvd_extendToBPlus ![1, -a] (by simpa using ha)
    (Algebra.linearMap c.S Ainf ∘ₗ c.adicBasis.coord i) ![B, C]
  have h_coord_BdR : algebraMap BPlus BdR (c.extendedCoord i B) -
        algebraMap (PadicAlgCl p) BdR a * algebraMap BPlus BdR (c.extendedCoord i C) =
      (algebraMap BPlus BdR B - algebraMap (PadicAlgCl p) BdR a * algebraMap BPlus BdR C) * q := by
    simpa [← coe_inj _ BdR, ← IsScalarTower.algebraMap_apply, sub_eq_add_neg] using h_coord
  rwa [hBC, sub_self, zero_mul, sub_eq_zero] at h_coord_BdR

/-- Let `b, b' ∈ B` and `α ∈ B_dR` with `b = α b'` in `B_dR`, and let `w₀, w₁ ∈ W(𝔽_{p^f})` with
`w₁ ≠ 0` and `α w₁ = w₀`. Then `p ^ r b = w b'` for some `r` and some `w ∈ W(𝔽_{p^f})`. -/
lemma Period.exists_pow_mul_eq_wittFq_mul_of_mul_eq {f : ℕ+} {b b' : Bmax} {α : BdR}
    (hab : algebraMap Bmax BdR b = α * algebraMap Bmax BdR b') {w₀ w₁ : WittFq f} (hw₁ : w₁ ≠ 0)
    (h_mul : α * algebraMap Ainf BdR (algebraMap (WittFq f) Ainf w₁) =
      algebraMap Ainf BdR (algebraMap (WittFq f) Ainf w₀)) :
    ∃ r : ℕ, ∃ w : WittFq f, p ^ r * b = (w : Ainf) * b' := by
  -- with `w₁ = p ^ r * u` for a unit `u`, `h_mul` gives `p ^ r * α = u⁻¹ * w₀`
  obtain ⟨r, u, rfl⟩ : ∃ (r : ℕ) (u : (WittFq f)ˣ), w₁ = p ^ r * u :=
    w₁.exists_eq_pow_p_mul' hw₁
  have hα : (p : BdR) ^ r * α =
      algebraMap Ainf BdR (algebraMap (WittFq f) Ainf (↑u⁻¹ * w₀)) := by
    rw [map_mul, map_mul, ← h_mul, mul_left_comm, ← map_mul, ← map_mul,
      mul_left_comm (↑u⁻¹ : WittFq f), u.inv_mul]
    simp [mul_comm]
  refine ⟨r, ↑u⁻¹ * w₀, (coe_inj _ BdR).mp ?_⟩
  simpa [← IsScalarTower.algebraMap_apply, hab, ← mul_assoc] using
    congrArg (fun x : BdR ↦ x * algebraMap Bmax BdR b') hα

/-- Let `γ 0, γ 1` lie in `c.bicommutant`, not both divisible by `z = c.z`, with `γ 0 = a γ 1` in
`B_dR` for some `a ∈ Q̄_p`. Here `c.bicommutant` is the ring S_B of elements of `B⁺` commuting with
every `c.S`-linear map of `B⁺` that keeps the image of A_max, and `z` is the image of `X` under the
chart. Then `a w₁ = w₀` in `B_dR` for some `w₀, w₁ ∈ W(𝔽_{p^f})`, `f = c.f`, with `w₁ ≠ 0`. -/
lemma Lift.Chart.exists_wittFq_mul_eq_of_eq_mul {a : PadicAlgCl p} {γ : Fin 2 → BPlus}
    (hγ_mem : ∀ l : Fin 2, γ l ∈ c.bicommutant)
    (h_not_dvd : ¬(fun _ : Fin 2 ↦ Chart.ainfToBPlus c.z : Fin 2 → BPlus) ∣ γ)
    (hγa : algebraMap BPlus BdR (γ 0) =
      algebraMap (PadicAlgCl p) BdR a * algebraMap BPlus BdR (γ 1)) :
    ∃ w₀ w₁ : WittFq c.f, w₁ ≠ 0 ∧
      (a : BdR) * algebraMap Ainf BdR (algebraMap (WittFq c.f) Ainf w₁) =
        algebraMap Ainf BdR (algebraMap (WittFq c.f) Ainf w₀) := by
  -- reduce modulo `z`: `p ^ m * γ l = w l + z * u l` with `w l` in `WittFq c.f`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ l : Fin 2, ∃ w : WittFq c.f, ∃ u ∈ c.bicommutant,
      p ^ m * γ l =
        Chart.ainfToBPlus (algebraMap (WittFq c.f) Ainf w) + Chart.ainfToBPlus c.z * u :=
    (Filter.eventually_all.mpr fun l ↦ c.eventually_exists_pow_mul_eq_add_z_mul (hγ_mem l)).exists
  choose w u hu_mem h_dec using hm
  have hw_int (v : WittFq c.f) : IsIntegral ℚ_[p] ((v : Ainf) : BdR) :=
    (IsIntegral.of_finite ℤ_[p] _).algebraMap.algebraMap.tower_top
  have ha_int : IsIntegral ℚ_[p] (a : BdR) := (isIntegral ℚ_[p] a).algebraMap
  -- `a w 1 - w 0` is algebraic over `ℚ_[p]` and, by `hγa` and `h_dec`, a multiple of `z`;
  -- if it were not zero, `z` would be a unit of `BPlus` and would divide `γ`
  have h_aw : (a : BdR) * (w 1 : Ainf) = (w 0 : Ainf) := by
    by_contra h_ne
    -- `w 0 + z u 0 = p ^ m γ 0 = a p ^ m γ 1 = a (w 1 + z u 1)`
    have h_dec_BdR (l : Fin 2) : (p : BdR) ^ m * (γ l : BdR) =
        ((w l : Ainf) : BdR) + ((c.z : Ainf) : BdR) * (u l : BdR) := by
      simpa [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap BPlus BdR) (h_dec l)
    have h_eq : (a : BdR) * ((w 1 : Ainf) : BdR) - ((w 0 : Ainf) : BdR) =
        ((c.z : Ainf) : BdR) * ((u 0 : BdR) - (u 1 : BdR) * (a : BdR)) := by
      linear_combination h_dec_BdR 0 - (a : BdR) * h_dec_BdR 1 - (p : BdR) ^ m * hγa
    have h_alg : IsIntegral ℚ_[p] ((a : BdR) * (w 1 : Ainf) - (w 0 : Ainf)) :=
      (ha_int.mul (hw_int _)).sub (hw_int _)
    have h_int : IsIntegral BPlus ((u 0 : BdR) - u 1 • (a : BdR)) :=
      isIntegral_algebraMap.sub (ha_int.tower_top.smul (u 1))
    have hz_unit : IsUnit (Chart.ainfToBPlus c.z : BPlus) :=
      isUnit_of_isIntegral_eq_mul h_alg (sub_ne_zero.mpr h_ne) h_int
        (by simpa [smul_def, ← IsScalarTower.algebraMap_apply] using h_eq)
    exact h_not_dvd (Pi.isUnit_iff.mpr fun _ ↦ hz_unit).dvd
  -- `w 1 ≠ 0`: otherwise `w 0 = 0` too, and `z` would divide `p ^ m * γ l`, hence `γ`
  refine ⟨w 0, w 1, fun hw₁_zero ↦ h_not_dvd ?_, h_aw⟩
  have hw₀_zero : algebraMap (WittFq c.f) Ainf (w 0) = 0 := by simpa [hw₁_zero] using h_aw.symm
  have h_pγ : (fun _ : Fin 2 ↦ (p : BPlus) ^ m) * γ = (fun _ ↦ Chart.ainfToBPlus c.z) * u := by
    simp [funext_iff, h_dec, hw₀_zero, hw₁_zero]
  have h_unit : IsUnit fun _ : Fin 2 ↦ (p : BPlus) ^ m := Pi.isUnit_iff.mpr fun _ ↦ isUnit_p.pow m
  exact h_unit.dvd_mul_left.mp ⟨u, h_pγ⟩

/-- Let `j = 𝒥.toGp : Γ → G_p` have open image, and let `c` be a chart for j (`c.IsChartOf`: every g
that fixes θ(S) pointwise lies in j Γ), S the ring of the chart over W(F_{p^f}), f = `c.f`. If b,
b' ∈ B, b' ≠ 0 and g(b)b' = b·g(b') for all g in Γ, then p^m b = wb' for some m and some
w ∈ W(F_{p^f}).

Part of Fontaine's theorem on Galois invariants of the fraction field of the crystalline period
ring: only the nontrivial inclusion, with denominators cleared. -/
lemma Period.exists_pow_mul_eq_wittFq_mul_of_isChartOf (hc : c.IsChartOf 𝒥.toGp) {b b' : Bmax}
    (hb' : b' ≠ 0) (h_ratio : ∀ g : Γ, b' * 𝒥.toGp g • b = toGp g • b' * b) :
    ∃ m : ℕ, ∃ w : WittFq c.f, p ^ m * b = (w : Ainf) * b' := by
  -- The quotient `b / b'` in `BdR` is fixed by `toGp Γ`, so it is some `a` in `localFieldOf Γ`
  -- (the invariants of `BdR` under an open subgroup). A coordinate of the chart turns
  -- `b = a b'` into a relation in `c.bicommutant`, which is then reduced modulo `z = c.z`.
  obtain ⟨a, ha, hab⟩ : ∃ a ∈ localFieldOf Γ,
      algebraMap Bmax BdR b = algebraMap (PadicAlgCl p) BdR a * algebraMap Bmax BdR b' := by
    have h_fixed (g : Γ) :
        𝒥.toGp g • ((b : BdR) / b') - (b : BdR) / b' ∈ (⊥ : Submodule BdRPlus BdR) := by
      have h_ne : toGp g • b' ≠ 0 := by simpa [smul_eq_zero_iff_eq] using hb'
      simp_all [smul_div₀', ← map_mul, field, mul_comm]
    obtain ⟨⟨a, ha⟩, h_eq⟩ := BdR.exists_sub_mem_of_smul_sub_mem Γ ⊥ h_fixed
    exact ⟨a, ha, by simpa [sub_eq_zero, div_eq_iff, hb'] using h_eq⟩
  -- clear denominators: `B = b d` and `C = b' d` lie in `BPlus` for a power `d` of `μ`
  obtain ⟨B, C, d, hB, hC⟩ : ∃ B C : BPlus, ∃ d : Submonoid.powers (mu : BPlus),
      b * algebraMap BPlus Bmax d = algebraMap BPlus Bmax B ∧
        b' * algebraMap BPlus Bmax d = algebraMap BPlus Bmax C :=
    surj₂ (.powers (mu : BPlus)) _ b b'
  have hBC : algebraMap BPlus BdR B =
      algebraMap (PadicAlgCl p) BdR a * algebraMap BPlus BdR C := by
    rw [IsScalarTower.algebraMap_apply BPlus Bmax BdR B,
      IsScalarTower.algebraMap_apply BPlus Bmax BdR C, ← hB, ← hC, map_mul, map_mul, hab, mul_assoc]
  -- some coordinate of `C` is not zero, as `C` is the `p`-adic limit of its coordinate expansions
  obtain ⟨i, hi⟩ : ∃ i : c.adicBasis.Index, c.extendedCoord i C ≠ 0 := by
    by_contra! h_zero
    have hC_zero : C = 0 := eq_zero_of_p_pow_amaxImage fun m ↦ by
      simpa [h_zero] using (c.eventually_approx_sum_extendedCoord C m).exists
    -- then `b' d = 0` with `d` a unit, so `b' = 0`
    rw [hC_zero, map_zero, (IsLocalization.map_units Bmax d).mul_left_eq_zero] at hC
    exact hb' hC
  -- the `i`-th coordinates of `B`, `C` are `z ^ n * γ`, with `γ 0`, `γ 1` not both divisible by `z`
  obtain ⟨n, γ, hγ, h_not_dvd⟩ := exists_eq_pow_mul_of_not_forall_dvd
    (fun _ ↦ Chart.ainfToBPlus c.z) (c.extendedCoord i ∘ ![B, C])
    fun h_dvd ↦ hi (c.eq_zero_of_z_pow_dvd fun n ↦ pi_dvd_iff.mp (h_dvd n) 1)
  replace hγ (l : Fin 2) : c.extendedCoord i (![B, C] l) = Chart.ainfToBPlus c.z ^ n * γ l :=
    congrFun hγ l
  have hzn : (Chart.ainfToBPlus c.z : BPlus) ^ n ≠ 0 :=
    left_ne_zero_of_mul ((hγ 1).symm.trans_ne hi)
  have hγ_mem (l : Fin 2) : γ l ∈ c.bicommutant := by
    refine c.mem_bicommutant_of_mul (by bound) hzn ?_
    simpa only [← hγ l] using c.extendedCoord_mem_bicommutant i (![B, C] l)
  -- as `B = a C`, the `i`-th coordinates satisfy `z ^ n γ 0 = a z ^ n γ 1`; cancel `z ^ n`
  have h_coord : algebraMap BPlus BdR (Chart.ainfToBPlus c.z ^ n * γ 0) =
      algebraMap (PadicAlgCl p) BdR a *
        algebraMap BPlus BdR (Chart.ainfToBPlus c.z ^ n * γ 1) := by
    rw [← hγ, ← hγ]
    exact hc.extendedCoord_eq_mul_of_eq_mul ha hBC i
  rw [map_mul, map_mul, mul_left_comm, mul_right_inj' (by simpa using hzn)] at h_coord
  -- reduce `p ^ m γ l` modulo `z`: `a w₁ = w₀` with `w₀, w₁` in `WittFq c.f`, `w₁ ≠ 0`
  obtain ⟨w₀, w₁, hw₁, h_mul⟩ := Chart.exists_wittFq_mul_eq_of_eq_mul hγ_mem h_not_dvd h_coord
  exact exists_pow_mul_eq_wittFq_mul_of_mul_eq hab hw₁ h_mul

/-- If a, b ∈ B, b ≠ 0 and g(a)b = a·g(b) for all g near 1 in G_p, then p^n a = wb for some n, some
f and some w ∈ W(F_{p^f}).

A form of Fontaine's computation of the Galois invariants of the fraction field of the crystalline
period ring: a quotient a/b fixed by all g near 1 lies in W(F_{p^f})[1/p] for some unspecified
degree f. -/
lemma Period.Bmax.exists_witt_ratio {a b : Bmax} (hb : b ≠ 0)
    (h_ratio : ∀ᶠ g : Gp p in nhds 1, b * g • a = g • b * a) :
    ∃ (f : ℕ+) (n : ℕ), ∃ w : WittFq f, p ^ n * a = (w : Ainf) * b := by
  -- The relation holds on an open subgroup `U`; apply `exists_pow_mul_eq_wittFq_mul_of_isChartOf`
  -- to a chart for `U`.
  obtain ⟨U, hU⟩ : ∃ U : OpenSubgroup (Gp p), (U : Set (Gp p)) ⊆ {g | b * g • a = g • b * a} :=
    NonarchimedeanGroup.is_nonarchimedean _ h_ratio
  let instU : OverGp U.toSubgroup p := ⟨U.toSubgroup.subtype, ⟨by simpa using U.isOpen⟩⟩
  obtain ⟨k, -⟩ := exists_kummerChart U.toSubgroup
  exact ⟨_, exists_pow_mul_eq_wittFq_mul_of_isChartOf k.chart_isChartOf hb fun g ↦ hU g.property⟩

end New
