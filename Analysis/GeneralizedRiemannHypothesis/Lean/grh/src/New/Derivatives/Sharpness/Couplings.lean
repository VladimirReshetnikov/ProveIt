import New.Derivatives.Sharpness.LeastValuation

/-!
# Least valuations along couplings

Throughout, `v` is the valuation of `ℂ_[p]` with `‖x‖ = p ^ (-v x)`, a series is integral if its
coefficients lie in the valuation ring `valRingCp p`, and `seriesToCp` views an integral series as a
series over `ℂ_[p]`.

## Main definitions and results

* `New.IsCouplingFamily`: each selected coupling `z_τ ^ p ^ e τ * z_(τ⁺)` has `e τ` odd and has
  strictly the lowest exponent among such couplings of selected places with the same partner.
* `New.powerDegree`, `New.partnerDegree`: the degrees `ν'` and `ν''` of the two parts of a product
  of couplings, with their values at a place and their total degrees.
* `New.pairExponent`, `New.couplingSubst`: the exponent of `z' ^ ν' * z'' ^ ν''`, and the
  substitution `z_0 = δ_0 z' + z''`, `z_c = δ_c z'`.
* `New.IsCouplingFamily.norm_coeff_pairExponent`: the valuation of the coefficient of
  `z' ^ ν' * z'' ^ ν''` in `F(z' + z'') ∏_(c ≠ 0) F(δ_c z')` for `F = W exp (κ Ξ)`, where `κ` is a
  scalar of negative valuation.
* `New.CMLattice.leastValLE_six_of_isCouplingFamily`: at an inert prime `p > 2` the least valuation
  `val₆` on six copies satisfies `val₆(ν) ≤ -|j|` and `v(ν'! ν''!) + val₆(ν) ≤ γ_p |ν| - |j|`, where
  `ν = ν' + ν''` and `γ_p = gammaPrime d p = 1 / (p - 1) - varpiValuation d p`.

The variable `z'` that is raised to the power `p ^ e` is separated from the variable `z''` that
occurs linearly; the term in which every derivative in `z''` brings down `κ` dominates.

Notions from other files:
* `couplingSum S pr l` is the series `Ξ = ∑ l a b • Γ_a ^ p ^ b` over `a ∈ S` and `b : ℕ`, where
  `Γ_a` is the sum of the couplings `z_τ ^ p ^ a * z_(pr a τ)` over all `τ`.
* `copySubst a` substitutes `z ↦ ∑ a_k z_k` in copies `z_k` of the variables.
* `C : CMLattice d` is a lattice with multiplication by the integers of `ℚ(√-d)` and a chosen point
  `t` of order two; `C.θ` is the twisted translate by `t` of its sigma function, normalized to `1`
  at `0`, and `C.thetaProd μ m = ∏ θ(μ_i z) ^ m i`, read over `ℂ_[p]` through the embedding of `ℂ`
  that `PadicPlace p` fixes.
* `C.LeastValLE μ m n ν r` says `val_n(ν) ≤ r` for the least valuation `val_n(ν)` of a coefficient
  of degree `ν` in a product `∏ (H_c Θ)(z_c)` over `n` copies, where `Θ = C.thetaProd μ m` and the
  `H_c` run through the ring `C.multiSeriesRing μ`.
-/

/-! ## Families of couplings -/

namespace New

section families

variable {Φ : Type}

/-- The couplings `z_τ ^ p ^ e τ * z_(τ⁺)`, `τ ∈ Φ₀`, `τ⁺ = pr (e τ) τ`, have `e τ` odd, and each
has strictly the lowest exponent among the couplings `z_τ₁ ^ p ^ e' * z_(τ⁺)` with `τ₁ ∈ Φ₀`,
`e'` odd and `pr e' τ₁ = τ⁺`. Here `pr e τ` is the partner of the place `τ` for the exponent `e`. -/
structure IsCouplingFamily (pr : ℕ → Φ → Φ) (Φ₀ : Finset Φ) (e : Φ → ℕ) : Prop where
  /-- The exponents are odd. -/
  odd : ∀ τ ∈ Φ₀, Odd (e τ)
  /-- For `τ, τ₁ ∈ Φ₀` and odd `e' ≤ e τ`, the equation `pr e' τ₁ = τ⁺` holds only for `τ₁ = τ`,
  `e' = e τ`. -/
  eq_of_partner_eq : ∀ τ ∈ Φ₀, ∀ τ₁ ∈ Φ₀, ∀ e' ≤ e τ, Odd e' →
    pr e' τ₁ = pr (e τ) τ → τ₁ = τ ∧ e' = e τ

/-- The degree `ν'` of the monomial `∏ z_τ ^ (p ^ e τ * j τ)` over `τ ∈ Φ₀`. -/
noncomputable def powerDegree (p : ℕ) (Φ₀ : Finset Φ) (e j : Φ → ℕ) : Φ × Unit →₀ ℕ :=
  ∑ τ ∈ Φ₀, .single (τ, ()) (p ^ e τ * j τ)

/-- The degree `ν''` of the monomial `∏ z_(τ⁺) ^ j τ` over `τ ∈ Φ₀`, where `τ⁺ = pr (e τ) τ`. -/
noncomputable def partnerDegree (pr : ℕ → Φ → Φ) (Φ₀ : Finset Φ) (e j : Φ → ℕ) :
    Φ × Unit →₀ ℕ :=
  ∑ τ ∈ Φ₀, .single (pr (e τ) τ, ()) (j τ)

lemma powerDegree_apply_of_mem {p : ℕ} {Φ₀ : Finset Φ} {e j : Φ → ℕ} {τ : Φ} (hτ : τ ∈ Φ₀) :
    powerDegree p Φ₀ e j (τ, ()) = p ^ e τ * j τ := by
  classical simp [powerDegree, Finsupp.finsetSum_apply, Finsupp.single_apply, hτ]

lemma powerDegree_apply_of_notMem {p : ℕ} {Φ₀ : Finset Φ} {e j : Φ → ℕ} {τ : Φ} (hτ : τ ∉ Φ₀) :
    powerDegree p Φ₀ e j (τ, ()) = 0 := by
  classical simp [powerDegree, Finsupp.finsetSum_apply, Finsupp.single_apply, hτ]

lemma partnerDegree_apply {pr : ℕ → Φ → Φ} {Φ₀ : Finset Φ} {e j : Φ → ℕ} [DecidableEq Φ] (t : Φ) :
    partnerDegree pr Φ₀ e j (t, ()) = ∑ τ ∈ Φ₀ with pr (e τ) τ = t, j τ := by
  simp [partnerDegree, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_filter]

lemma degree_powerDegree {p : ℕ} {Φ₀ : Finset Φ} {e j : Φ → ℕ} :
    (powerDegree p Φ₀ e j).degree = ∑ τ ∈ Φ₀, p ^ e τ * j τ := by
  simp only [powerDegree, map_sum, Finsupp.degree_single]

lemma degree_partnerDegree {pr : ℕ → Φ → Φ} {Φ₀ : Finset Φ} {e j : Φ → ℕ} :
    (partnerDegree pr Φ₀ e j).degree = ∑ τ ∈ Φ₀, j τ := by
  simp only [partnerDegree, map_sum, Finsupp.degree_single]

end families

end New

/-! ## The coefficient of a product of couplings in a product of copies -/

open MvPowerSeries Finset Nat

namespace New

section steps
open IsLocalRing

variable {p : ℕ} [Fact p.Prime] {X Y : Type}

/-- For integral series `W`, `Ξ` with `W` a unit and `Ξ(0) = 0`, and for any scalar `κ ∈ ℂ_[p]`, the
logarithmic derivative of `W exp (κ Ξ)` in the variable `x` is `κ ∂Ξ + B` with `B = ∂W / W`
integral. Here `expSubst a` is the series `exp a` and `seriesToCp` views an integral series as a
series over `ℂ_[p]`. -/
lemma exists_pderiv_mul_expSubst {W Ξ : MvPowerSeries X (valRingCp p)} (hW : IsUnit W)
    (hΞ : Ξ.constantCoeff = 0) (κ : ℂ_[p]) (x : X) : ∃ B : MvPowerSeries X (valRingCp p),
    pderiv x (seriesToCp W * expSubst (κ • seriesToCp Ξ)) =
      (κ • seriesToCp (pderiv x Ξ) + seriesToCp B) *
        (seriesToCp W * expSubst (κ • seriesToCp Ξ)) := by
  obtain ⟨B, hB⟩ : W ∣ pderiv x W := hW.dvd
  -- the chain rule for the exponential series
  have h_exp : pderiv x (expSubst (κ • seriesToCp Ξ)) =
      expSubst (κ • seriesToCp Ξ) * κ • seriesToCp (pderiv x Ξ) := by
    simp [hΞ, PowerSeries.subst, pderiv_subst, hasSubst_of_constantCoeff_zero, ← map_pderiv,
      ← PowerSeries.derivative.eq_def, PowerSeries.derivative_exp, smul_eq_C_mul]
  refine ⟨B, ?_⟩
  rw [Derivation.leibniz, h_exp, ← map_pderiv, hB, map_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- Let `κ ∈ ℂ_[p]` have norm greater than `1`, and let `∂` be the derivative in the variable `y`.
If `∂G = (κ A + B) G` with `A`, `B` integral, then for integral `g` we have `∂(g G) = κ g' G` with
`g'` integral and congruent to `g A` modulo the maximal ideal. -/
lemma exists_pderiv_mul_eq_smul {κ : ℂ_[p]} (hκ : 1 < ‖κ‖) {G : MvPowerSeries Y ℂ_[p]}
    {A B : MvPowerSeries Y (valRingCp p)} {y : Y}
    (hG : pderiv y G = (κ • seriesToCp A + seriesToCp B) * G)
    (g : MvPowerSeries Y (valRingCp p)) : ∃ g' : MvPowerSeries Y (valRingCp p),
    pderiv y (seriesToCp g * G) = κ • (seriesToCp g' * G) ∧
      g'.map (residue (valRingCp p)) =
        g.map (residue (valRingCp p)) * A.map (residue (valRingCp p)) := by
  -- `g' = g A + κ⁻¹ (∂g + g B)`, and `κ⁻¹` lies in the maximal ideal
  let κInv : valRingCp p := ⟨κ⁻¹, (norm_inv κ).trans_le (inv_le_one_of_one_le₀ hκ.le)⟩
  have h_residue : residue (valRingCp p) κInv = 0 := by
    simp [residue_eq_zero_iff, mem_nonunits_iff, isUnit_integer_iff_norm_eq_one, κInv, hκ.ne']
  have h_cancel : C κ * seriesToCp (C κInv) = (1 : MvPowerSeries Y ℂ_[p]) := by
    simp [κInv, ← map_mul, norm_pos_iff.1 (one_pos.trans hκ)]
  refine ⟨g * A + C κInv * (pderiv y g + g * B), ?_, by simp [h_residue]⟩
  simp only [Derivation.leibniz, hG, smul_eq_mul, smul_eq_C_mul, map_add, map_mul, map_pderiv]
  linear_combination
    -(pderiv y (seriesToCp g) + seriesToCp g * seriesToCp B) * G * h_cancel

/-- Let `κ ∈ ℂ_[p]` have norm greater than `1`. If `∂_(t i) G = (κ A_i + B_i) G` with `A_i`, `B_i`
integral, then `(∏_(i ∈ T) ∂_(t i)) G = κ ^ #T g G` with `g` integral and congruent to `∏ A_i`
modulo the maximal ideal. The identity is stated after applying each differential operator `f(∂)`
and evaluating at `0`: `jet ℂ_[p] f G` is `f(∂) G (0)`. -/
lemma exists_jet_mul_prod_X {κ : ℂ_[p]} (hκ : 1 < ‖κ‖) {G : MvPowerSeries Y ℂ_[p]} {ι : Type}
    {t : ι → Y} {A : ι → MvPowerSeries Y (valRingCp p)}
    (hG : ∀ i : ι, ∃ B : MvPowerSeries Y (valRingCp p),
      pderiv (t i) G = (κ • seriesToCp (A i) + seriesToCp B) * G)
    (T : Finset ι) :
    ∃ g : MvPowerSeries Y (valRingCp p),
      g.map (residue (valRingCp p)) = ∏ i ∈ T, (A i).map (residue (valRingCp p)) ∧
      ∀ f : MvPolynomial Y ℂ_[p],
        jet ℂ_[p] (f * ∏ i ∈ T, .X (t i)) G = κ ^ #T * jet ℂ_[p] f (seriesToCp g * G) := by
  induction T using cons_induction with
  | empty => exact ⟨1, by simp, by simp⟩
  | cons i T hi ih =>
    obtain ⟨g, hg_res, hg_jet⟩ := ih
    obtain ⟨B, hB⟩ := hG i
    obtain ⟨g', hg'_deriv, hg'_res⟩ := exists_pderiv_mul_eq_smul hκ hB g
    refine ⟨g', by rw [hg'_res, hg_res, prod_cons, mul_comm], fun f ↦ ?_⟩
    rw [prod_cons, ← mul_assoc, hg_jet, jet_mul_X, hg'_deriv, map_smul, card_cons, pow_succ,
      smul_eq_mul, mul_assoc]

/-- The exponent of the monomial `z' ^ ν' * z'' ^ ν''` in two copies of the variables. -/
noncomputable def pairExponent (ν' ν'' : X →₀ ℕ) : X × Fin 2 →₀ ℕ :=
  ν'.mapDomain (fun x : X ↦ (x, 0)) + ν''.mapDomain fun x : X ↦ (x, 1)

/-- Identifying the two copies of the variables sends `z' ^ ν' * z'' ^ ν''` to `z ^ (ν' + ν'')`. -/
lemma mapDomain_fst_pairExponent (ν' ν'' : X →₀ ℕ) :
    (pairExponent ν' ν'').mapDomain Prod.fst = ν' + ν'' := by
  simp [pairExponent, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp]

/-- The product of the factorials of the entries of `pairExponent ν' ν''`, the exponent of
`z' ^ ν' * z'' ^ ν''`, is `(∏_x (ν' x)!) * (∏_x (ν'' x)!)`, computed in `ℂ_[p]`. -/
lemma prod_factorial_pairExponent [Fintype X] (ν' ν'' : X →₀ ℕ) :
    ((pairExponent ν' ν'').prod fun (_ : X × Fin 2) (n : ℕ) ↦ (n ! : ℂ_[p])) =
      (∏ x : X, ((ν' x)! : ℂ_[p])) * ∏ x : X, ((ν'' x)! : ℂ_[p]) := by
  have h_apply (ν : X →₀ ℕ) (k k' : Fin 2) (x : X) :
      ν.mapDomain (fun y : X ↦ (y, k)) (x, k') = if k = k' then ν x else 0 := by
    rcases eq_or_ne k k' with rfl | hk
    · simp [ Finsupp.mapDomain_apply_of_injective (Prod.mk_left_injective k)]
    · simp [Finsupp.mapDomain_of_notMem_range, hk]
  simp [Finsupp.prod_fintype, Fintype.prod_prod_type, pairExponent, h_apply, prod_mul_distrib]

end steps

section couplings
open IsLocalRing

variable {p : ℕ} [Fact p.Prime] {Φ : Type} [Fintype Φ]

open Classical in
/-- Let `Ξ = ∑ l a b • Γ_a ^ p ^ b` be the coupling sum over odd `a`. Let `τ ∈ Φ₀` for a coupling
family (`e τ₁` is odd on `Φ₀`, and no other pair of an odd `a ≤ e τ` and `τ₁ ∈ Φ₀` has
`pr a τ₁ = τ⁺ = pr (e τ) τ`). Put `z_τ₁ = 0` for `τ₁ ∉ Φ₀` and reduce modulo the maximal ideal. Then
`Ξ_τ = ∂Ξ / ∂z_(τ⁺)` agrees with `l (e τ) 0 • z_τ ^ p ^ e τ` in all total degrees up to
`p ^ e τ`. -/
lemma IsCouplingFamily.isLowestTerm_pderiv_couplingSum {pr : ℕ → Φ → Φ} {Φ₀ : Finset Φ}
    {e : Φ → ℕ} {l : ℕ → ℕ → valRingCp p} (he : IsCouplingFamily pr Φ₀ e) {τ : Φ} (hτ : τ ∈ Φ₀) :
    IsLowestTerm 1 (rescale (fun x : Φ × Unit ↦ if x.1 ∈ Φ₀ then 1 else 0)
        ((pderiv (pr (e τ) τ, ()) (couplingSum {a : ℕ | Odd a} pr l)).map
          (residue (valRingCp p))))
      (.single (τ, ()) (p ^ e τ)) (residue (valRingCp p) (l (e τ) 0)) := by
  have hp : 1 < p := Fact.out (p := p.Prime).one_lt
  have h_zero : 0 ∉ {a : ℕ | Odd a} := by simp
  intro d hd
  rw [coeff_rescale, coeff_map]
  by_cases hd_eq : d = .single (τ, ()) (p ^ e τ)
  · simp [hd_eq, residue_coeff_pderiv_couplingSum h_zero (he.odd τ hτ) (τ, ()), hτ]
  -- Any other term is `z_τ₁ ^ p ^ a` with `a ≤ e τ` and the same partner, so `τ₁ ∉ Φ₀`.
  rw [coeff_monomial_ne hd_eq]
  by_contra h_ne
  obtain ⟨a, ha_odd, ⟨τ₁, ⟨⟩⟩, h_pair, rfl⟩ : ∃ a : ℕ, Odd a ∧ ∃ x : Φ × Unit,
      (pr a x.1, x.2) = (pr (e τ) τ, ()) ∧ d = .single x (p ^ a) :=
    exists_eq_single_of_residue_coeff_pderiv_ne_zero h_zero (right_ne_zero_of_mul h_ne)
  have h_le : a ≤ e τ := by simpa [Finsupp.weight_single, pow_le_pow_iff_right₀ hp] using hd
  have hτ₁ : τ₁ ∈ Φ₀ := by_contra fun h ↦ by simp [h, (one_pos.trans hp).ne'] at h_ne
  obtain ⟨rfl, rfl⟩ : τ₁ = τ ∧ a = e τ :=
    he.eq_of_partner_eq τ hτ τ₁ hτ₁ a h_le ha_odd (congrArg Prod.fst h_pair)
  exact hd_eq rfl

/-- A series with constant term `1` has lowest term `1 = 1 z ^ 0` for the total degree:
`IsLowestTerm w f m c` says that, in `w`-weight at most that of `m`, the coefficients of `f` are
those of `c z ^ m`, here with all weights `1`, `m = 0` and `c = 1`. -/
lemma isLowestTerm_zero_one {X R : Type} [Fintype X] [CommRing R] {f : MvPowerSeries X R}
    (hf : f.constantCoeff = 1) : IsLowestTerm 1 f 0 1 := by
  intro d hd
  obtain rfl : d = 0 := by
    simpa [Finsupp.degree_eq_weight_one, ← Pi.one_def, ← Finsupp.degree_eq_zero_iff] using hd
  simp [hf]

/-- Let `Ξ = ∑ l a b • Γ_a ^ p ^ b` be the coupling sum over odd `a`, where `Γ_a` is the sum of all
`z_τ ^ p ^ a * z_(pr a τ)`, with units `l a 0`, and let `Ξ_τ = ∂Ξ / ∂z_(τ⁺)`, `τ⁺ = pr (e τ) τ`, for
`τ` in a coupling family `Φ₀` (each `z_τ ^ p ^ e τ * z_(τ⁺)` has `e τ` odd and strictly lowest
degree among the `z_τ₁ ^ p ^ a * z_(τ⁺)` with `τ₁ ∈ Φ₀`, `a` odd and `pr a τ₁ = τ⁺`). If
`g ≡ ∏ Ξ_τ ^ j τ` modulo the maximal ideal and `U` has constant term `1`, then the coefficient of
`z ^ ν'` in `g U` is a unit, where `ν' = powerDegree p Φ₀ e j` is the degree of
`∏ z_τ ^ (p ^ e τ * j τ)`. -/
lemma IsCouplingFamily.norm_coeff_powerDegree {pr : ℕ → Φ → Φ} {Φ₀ : Finset Φ} {e : Φ → ℕ}
    {l : ℕ → ℕ → valRingCp p} (he : IsCouplingFamily pr Φ₀ e)
    (hl : ∀ a : ℕ, Odd a → IsUnit (l a 0)) {j : Φ → ℕ}
    {g U : MvPowerSeries (Φ × Unit) (valRingCp p)}
    (hg : g.map (residue (valRingCp p)) = ∏ τ ∈ Φ₀,
      (pderiv (pr (e τ) τ, ()) (couplingSum {a : ℕ | Odd a} pr l)).map
        (residue (valRingCp p)) ^ j τ)
    (hU : U.constantCoeff = 1) :
    ‖coeff (powerDegree p Φ₀ e j) (seriesToCp (g * U))‖ = 1 := by
  classical
  -- After reducing and putting `z_τ₁ = 0` for `τ₁ ∉ Φ₀` (the map `Z`), the lowest term of `g U` is
  -- `lead * z ^ ν'` with `lead ≠ 0`.
  let Z := rescale (R := ResidueField (valRingCp p)) fun x : Φ × Unit ↦ if x.1 ∈ Φ₀ then 1 else 0
  let lead : ResidueField (valRingCp p) := ∏ τ ∈ Φ₀, residue (valRingCp p) (l (e τ) 0) ^ j τ
  have h_lead : lead ≠ 0 := prod_ne_zero_iff.2 fun τ hτ ↦
    pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).2 (hl (e τ) (he.odd τ hτ)))
  have hg_low :
      IsLowestTerm 1 (Z (g.map (residue (valRingCp p)))) (powerDegree p Φ₀ e j) lead := by
    rw [hg, map_prod]
    refine IsLowestTerm.prod fun τ hτ ↦ ?_
    simpa [Z, mul_comm] using (he.isLowestTerm_pderiv_couplingSum (l := l) hτ).pow (j τ)
  have h_coeff :
      coeff (powerDegree p Φ₀ e j) (Z ((g * U).map (residue (valRingCp p)))) = lead := by
    have hU_low : IsLowestTerm 1 (Z (U.map (residue (valRingCp p)))) 0 1 :=
      isLowestTerm_zero_one (by simp [← coeff_zero_eq_constantCoeff_apply, Z, hU])
    rw [map_mul, map_mul, hg_low.mul hU_low _ (by simp), add_zero, mul_one, coeff_monomial_same]
  rw [coeff_rescale, coeff_map] at h_coeff
  rw [coeff_map, Subring.coe_subtype, ← isUnit_integer_iff_norm_eq_one]
  exact (residue_ne_zero_iff_isUnit _).1 (right_ne_zero_of_mul (h_coeff.trans_ne h_lead))

/-- The coefficients of the substitution `z_0 = δ_0 z' + z''`, `z_c = δ_c z'` for `c ≠ 0`, in two
copies `z'`, `z''` of the variables. -/
noncomputable def couplingSubst {R : Type} [CommRing R] {n : ℕ} (δ : Fin (n + 1) → R)
    (c : Fin (n + 1)) : Fin 2 → R :=
  ![δ c, if c = 0 then 1 else 0]

/-- The coefficients of `couplingSubst δ` are integral if the `δ_c` are. -/
lemma norm_couplingSubst_le_one {n : ℕ} {δ : Fin (n + 1) → ℂ_[p]}
    (hδ : ∀ c : Fin (n + 1), ‖δ c‖ ≤ 1) (c : Fin (n + 1)) (k : Fin 2) :
    ‖couplingSubst δ c k‖ ≤ 1 := by
  fin_cases k <;> simp [couplingSubst, hδ, apply_ite (‖·‖), ite_le_one]

/-- Let `δ 0 = 1` and let `G = ∏_c copySubst (couplingSubst δ c) F`, that is,
`G(z', z'') = F(z' + z'') ∏_(c ≠ 0) F(δ_c z')` in two copies `z'`, `z''` of the variables. Only the
first factor involves `z''`, so if `∂_x F = L F`, then the derivative of `G` in `z''_x` is
`L(z' + z'') G`. -/
lemma pderiv_prod_copySubst_couplingSubst {X R : Type} [Fintype X] [CommRing R] {n : ℕ}
    {δ : Fin (n + 1) → R} (hδ : δ 0 = 1) {F L : MvPowerSeries X R} {x : X}
    (hF : pderiv x F = L * F) :
    pderiv (x, 1) (∏ c : Fin (n + 1), copySubst (couplingSubst δ c) F) =
      copySubst 1 L * ∏ c : Fin (n + 1), copySubst (couplingSubst δ c) F := by
  have h_first : couplingSubst δ 0 = 1 := by
    simp [funext_iff, Fin.forall_fin_two, couplingSubst, hδ]
  have h_rest : pderiv (x, 1) (∏ c : Fin n, copySubst (couplingSubst δ c.succ) F) = 0 :=
    prod_induction _ (pderiv (x, 1) · = 0)
      (fun G G' hG hG' ↦ by simp [Derivation.leibniz, hG, hG']) (by simp)
      fun c _ ↦ by simp [pderiv_copySubst, couplingSubst]
  have h_deriv : pderiv (x, (1 : Fin 2)) (copySubst 1 F) = copySubst 1 L * copySubst 1 F := by
    simp [pderiv_copySubst, hF]
  rw [Fin.prod_univ_succ, Derivation.leibniz, h_rest, h_first, h_deriv, smul_zero, zero_add,
    smul_eq_mul, mul_comm, mul_assoc]

/-- Scaling the variables by `ϖ` in each factor of `∏ F(∑ A c k z_k)` (product over `c`) multiplies
the coefficient of `z ^ γ` by `ϖ ^ γ.degree`, the total degree of `γ`. -/
lemma coeff_prod_copySubst_rescale {X K I R : Type} [Fintype X] [Fintype K] [Fintype I]
    [CommRing R] (A : I → K → R) (F : MvPowerSeries X R) (ϖ : R) (γ : X × K →₀ ℕ) :
    coeff γ (∏ c : I, copySubst (A c) (F.rescale fun _ : X ↦ ϖ)) =
      ϖ ^ γ.degree * coeff γ (∏ c : I, copySubst (A c) F) := by
  simp only [← rescale_copySubst, ← map_prod, coeff_rescale]
  rw [Finsupp.prod_fintype _ _ (by simp), prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]

omit [Fintype Φ] in
/-- The monomial `z' ^ ν'` times the product, over `τ ∈ Φ₀`, of `j τ` copies of `z''_(τ⁺)`, where
`τ⁺ = pr (e τ) τ`, is `z' ^ ν' * z'' ^ ν''` with `ν'' = partnerDegree pr Φ₀ e j`. -/
lemma monomial_mul_prod_X_partner {R : Type} [CommRing R] (pr : ℕ → Φ → Φ) (Φ₀ : Finset Φ)
    (e j : Φ → ℕ) (ν' : Φ × Unit →₀ ℕ) :
    MvPolynomial.monomial (ν'.mapDomain fun x : Φ × Unit ↦ (x, 0)) (1 : R) *
        ∏ i ∈ Φ₀.sigma fun τ : Φ ↦ range (j τ), .X ((pr (e i.1) i.1, ()), (1 : Fin 2)) =
      .monomial (pairExponent ν' (partnerDegree pr Φ₀ e j)) 1 := by
  simp [pairExponent, partnerDegree, prod_sigma, MvPolynomial.X_pow_eq_monomial,
    Finsupp.mapDomain_finsetSum, ← MvPolynomial.monomial_sum_one]

/-- Let `κ ∈ ℂ_[p]` have norm greater than `1`, let `F = W exp (κ Ξ)` with `W`, `Ξ` integral, `W` a
unit and `Ξ(0) = 0`, let `δ 0 = 1` and let `G = F(z' + z'') ∏_(c ≠ 0) F(δ_c z')` in two copies `z'`,
`z''` of the variables. Differentiating `G` in the variables `z''_(t i)`, `i ∈ T`, gives
`κ ^ #T g G` with `g` integral and `g(z', 0) ≡ ∏ ∂_(t i) Ξ` modulo the maximal ideal. -/
lemma exists_jet_prod_copySubst_couplingSubst {X ι : Type} [Fintype X] {κ : ℂ_[p]} (hκ : 1 < ‖κ‖)
    {W Ξ : MvPowerSeries X (valRingCp p)} (hW : IsUnit W) (hΞ : Ξ.constantCoeff = 0)
    {F : MvPowerSeries X ℂ_[p]} (hF : F = seriesToCp W * expSubst (κ • seriesToCp Ξ))
    {n : ℕ} {δ : Fin (n + 1) → ℂ_[p]} (hδ : δ 0 = 1) {G : MvPowerSeries (X × Fin 2) ℂ_[p]}
    (hG : G = ∏ c : Fin (n + 1), copySubst (couplingSubst δ c) F) (t : ι → X) (T : Finset ι) :
    ∃ g : MvPowerSeries (X × Fin 2) (valRingCp p),
      (killCompl (Function.Embedding.sectL X 0) g).map (residue (valRingCp p)) =
        ∏ i ∈ T, (pderiv (t i) Ξ).map (residue (valRingCp p)) ∧
      ∀ f : MvPolynomial (X × Fin 2) ℂ_[p],
        jet ℂ_[p] (f * ∏ i ∈ T, .X (t i, 1)) G = κ ^ #T * jet ℂ_[p] f (seriesToCp g * G) := by
  have h_log (i : ι) : ∃ B : MvPowerSeries (X × Fin 2) (valRingCp p), pderiv (t i, 1) G =
      (κ • seriesToCp (copySubst 1 (pderiv (t i) Ξ)) + seriesToCp B) * G := by
    obtain ⟨B, hB⟩ := exists_pderiv_mul_expSubst hW hΞ κ (t i)
    rw [← hF] at hB
    refine ⟨copySubst 1 B, ?_⟩
    simp [hG, pderiv_prod_copySubst_couplingSubst hδ hB, map_copySubst, Pi.one_def]
  obtain ⟨g, hg_res, hg_jet⟩ := exists_jet_mul_prod_X hκ h_log T
  exact ⟨g, by simp [← killCompl_map, hg_res, map_copySubst, killCompl_copySubst, ← Pi.one_def],
    hg_jet⟩

/-- Let `Ξ = ∑ l a b • Γ_a ^ p ^ b` be the coupling sum over odd `a`, where `Γ_a` is the sum of all
`z_τ ^ p ^ a * z_(pr a τ)`, and let `ν' = powerDegree p Φ₀ e j`, `ν'' = partnerDegree pr Φ₀ e j` be
the degrees of `∏ z_τ ^ (p ^ e τ * j τ)` and `∏ z_(τ⁺) ^ j τ`, `τ⁺ = pr (e τ) τ`, for a coupling
family (odd `e τ`, each coupling `z_τ ^ p ^ e τ * z_(τ⁺)`, `τ ∈ Φ₀`, of strictly lowest degree among
the `z_τ₁ ^ p ^ a * z_(τ⁺)` with `τ₁ ∈ Φ₀`, `a` odd and `pr a τ₁ = τ⁺`). Let `F = W exp (κ Ξ)` over
`ℂ_[p]`, with `W` integral and a unit, `l a 0` a unit for odd `a`, and `κ ∈ ℂ_[p]` of negative
valuation `v(κ)`. Let `δ 0 = 1` and let `∏_c F(δ_c z) = U` be integral with constant term `1`. Then
the coefficient of `z' ^ ν' * z'' ^ ν''` in the product `G = F(z' + z'') ∏_(c ≠ 0) F(δ_c z')` given
by `couplingSubst δ` has valuation `|j| v(κ) - v(ν''!)`, where `|j| = ∑ j τ` and
`ν''! = ∏ (ν'' x)!`. -/
lemma IsCouplingFamily.norm_coeff_pairExponent {pr : ℕ → Φ → Φ} {Φ₀ : Finset Φ} {e : Φ → ℕ}
    {l : ℕ → ℕ → valRingCp p} (he : IsCouplingFamily pr Φ₀ e)
    (hl : ∀ a : ℕ, Odd a → IsUnit (l a 0)) {κ : ℂ_[p]} (hκ : 1 < ‖κ‖)
    {W U : MvPowerSeries (Φ × Unit) (valRingCp p)} (hW : IsUnit W) (hU : U.constantCoeff = 1)
    {F : MvPowerSeries (Φ × Unit) ℂ_[p]}
    (hF : F = seriesToCp W * expSubst (κ • seriesToCp (couplingSum {a : ℕ | Odd a} pr l)))
    {n : ℕ} {δ : Fin (n + 1) → ℂ_[p]} (hδ : δ 0 = 1)
    (h_prod : ∏ c : Fin (n + 1), F.rescale (fun _ : Φ × Unit ↦ δ c) = seriesToCp U) (j : Φ → ℕ) :
    ‖∏ x : Φ × Unit, ((partnerDegree pr Φ₀ e j x)! : ℂ_[p])‖ *
        ‖coeff (pairExponent (powerDegree p Φ₀ e j) (partnerDegree pr Φ₀ e j))
          (∏ c : Fin (n + 1), copySubst (couplingSubst δ c) F)‖ =
      ‖κ‖ ^ ∑ τ ∈ Φ₀, j τ := by
  classical
  -- Differentiating `G` in `z''` gives `κ ^ |j| g G` with `g ≡ ∏ (∂Ξ / ∂z_(τ⁺)) ^ j τ` at
  -- `z'' = 0`, where `G = U`; the coefficient of `z' ^ ν'` in `g U` is a unit.
  set ν' : Φ × Unit →₀ ℕ := powerDegree p Φ₀ e j
  set ν'' : Φ × Unit →₀ ℕ := partnerDegree pr Φ₀ e j
  set G : MvPowerSeries ((Φ × Unit) × Fin 2) ℂ_[p] :=
    ∏ c : Fin (n + 1), copySubst (couplingSubst δ c) F with hG
  -- `ν'₀` is the exponent of `z' ^ ν'` in the two copies of the variables.
  set ν'₀ : (Φ × Unit) × Fin 2 →₀ ℕ := ν'.mapDomain fun x : Φ × Unit ↦ (x, 0) with hν'₀
  -- Step 1: the derivatives in `z''`, taken `j τ` times at each `τ⁺`.
  obtain ⟨g, hg_res, hg_jet⟩ := exists_jet_prod_copySubst_couplingSubst hκ hW
    constantCoeff_couplingSum hF hδ hG (fun i : Σ _ : Φ, ℕ ↦ (pr (e i.1) i.1, ()))
    (Φ₀.sigma fun τ : Φ ↦ range (j τ))
  have h_jet : jet ℂ_[p] (.monomial (pairExponent ν' ν'') 1) G =
      κ ^ (∑ τ ∈ Φ₀, j τ) * jet ℂ_[p] (.monomial ν'₀ 1) (seriesToCp g * G) := by
    simp only [← monomial_mul_prod_X_partner pr Φ₀ e j ν', hg_jet, card_sigma, card_range, ν'',
      hν'₀]
  -- Step 2: put `z'' = 0`.
  let ι : Φ × Unit ↪ (Φ × Unit) × Fin 2 := Function.Embedding.sectL (Φ × Unit) 0
  have hG_zero : killCompl ι G = seriesToCp U := by
    simp [G, ι, killCompl_copySubst, couplingSubst, ← h_prod]
  have hg_zero : (killCompl ι g).map (residue (valRingCp p)) = ∏ τ ∈ Φ₀,
      (pderiv (pr (e τ) τ, ()) (couplingSum {a : ℕ | Odd a} pr l)).map
        (residue (valRingCp p)) ^ j τ := by
    simp only [ι, hg_res, prod_sigma, prod_const, card_range]
  have h_unit : ‖coeff ν'₀ (seriesToCp g * G)‖ = 1 := by
    rw [show ν'₀ = ν'.embDomain ι from (Finsupp.embDomain_eq_mapDomain ι ν').symm,
      ← coeff_killCompl, map_mul, hG_zero, killCompl_map, ← map_mul,
      he.norm_coeff_powerDegree hl hg_zero hU]
  -- Step 3: pass from jets to coefficients and divide by `ν'!`.
  have h_fact : (ν'₀.prod fun (_ : (Φ × Unit) × Fin 2) (n : ℕ) ↦ (n ! : ℂ_[p])) =
      ∏ x : Φ × Unit, ((ν' x)! : ℂ_[p]) := by
    simp [hν'₀, Finsupp.prod_mapDomain_index_inj (Prod.mk_left_injective _), Finsupp.prod_fintype]
  rw [jet_monomial, jet_monomial, prod_factorial_pairExponent, h_fact] at h_jet
  have h_div : (∏ x : Φ × Unit, ((ν'' x)! : ℂ_[p])) * coeff (pairExponent ν' ν'') G =
      κ ^ (∑ τ ∈ Φ₀, j τ) * coeff ν'₀ (seriesToCp g * G) :=
    mul_left_cancel₀ (prod_ne_zero_iff.2 fun x _ ↦ cast_ne_zero.2 (factorial_ne_zero (ν' x)))
      (by linear_combination h_jet)
  rw [← norm_mul, h_div, norm_mul, h_unit, mul_one, norm_pow]

end couplings

namespace CMLattice

variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime]

/-- Let `d` be a prime `≡ 7 mod 8` (the class `PrimeSevenModEight d`). At a prime `p` inert in
`ℚ(√-d)` (that is, `(p / d) = -1`), `ρ_p (p + 1) = 1 / (p - 1)` for
`ρ_p = varpiValuation d p = 1 / (p² - 1)`. -/
lemma varpiValuation_mul_add_one_of_inert (h_inert : chiK d p = -1) :
    varpiValuation d p * (p + 1) = 1 / (p - 1) := by
  have hp : (1 : ℝ) < p := mod_cast Fact.out (p := p.Prime).one_lt
  rw [varpiValuation_of_inert h_inert, show (p : ℝ) ^ 2 - 1 = (p - 1) * (p + 1) by ring]
  field_simp [sub_ne_zero.2 hp.ne']

/-- Let `d` be a prime `≡ 7 mod 8` and let the prime `p` be inert in `ℚ(√-d)`, that is, the Legendre
symbol `chiK d p = (p / d)` is `-1`. If `v(ϖ) = ρ_p = varpiValuation d p = 1 / (p² - 1)`, then
`ϖ ^ (p + 1) / p` has valuation `1 / (p - 1) - 1`. -/
lemma norm_pow_div_of_inert {ϖ : ℂ_[p]} (h_inert : chiK d p = -1)
    (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p)) :
    ‖ϖ ^ (p + 1) / p‖ = p ^ (1 - 1 / (p - 1) : ℝ) := by
  have hp_pos : (0 : ℝ) < p := cast_pos.2 (Fact.out : p.Prime).pos
  have h_exponent : -varpiValuation d p * (p + 1 : ℕ) = -(1 / (p - 1) : ℝ) := by
    rw [neg_mul, cast_add_one, varpiValuation_mul_add_one_of_inert h_inert]
  calc ‖ϖ ^ (p + 1) / p‖ = (p : ℝ) ^ (-varpiValuation d p * (p + 1 : ℕ)) * p := by
        rw [norm_div, norm_pow, hϖ, norm_p_eq_inv, div_inv_eq_mul, Real.rpow_mul_natCast hp_pos.le]
    _ = p ^ (1 - 1 / (p - 1) : ℝ) := by
        rw [h_exponent, ← Real.rpow_add_one hp_pos.ne', neg_add_eq_sub]

/-- Let `d` be a prime `≡ 7 mod 8` and let the prime `p > 2` be inert in `ℚ(√-d)`. If `ϖ ∈ ℂ_[p]`
has valuation `ρ_p = varpiValuation d p = 1 / (p² - 1)`, then `ϖ ^ (p + 1) / p` has negative
valuation, that is, norm greater than `1`. -/
lemma one_lt_norm_pow_div_of_inert {ϖ : ℂ_[p]} (h_inert : chiK d p = -1)
    (hp : 2 < p) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p)) : 1 < ‖ϖ ^ (p + 1) / p‖ := by
  have hp_two : (2 : ℝ) < p := mod_cast hp
  rw [norm_pow_div_of_inert h_inert hϖ]
  refine Real.one_lt_rpow (by linarith) (sub_pos.2 ?_)
  rw [div_lt_one (by linarith)]
  linarith

omit [PrimeSevenModEight d] in
/-- Let `C : CMLattice d` be a CM lattice, let `θ` be the series over `ℂ_[p]` of its normalized
theta function `C.θ`, and suppose that `Θ = C.thetaProd μ m = ∏ θ(μ_i z) ^ m i` has the exponential
factorization `Θ(ϖ z) = W exp (κ Ξ)` with scalars `ϖ`, `κ ∈ ℂ_[p]`, integral series `W`, `Ξ` and
`Ξ(0) = 0`. Then `W` is a unit, since its constant term is `Θ(0) = 1`. -/
lemma isUnit_of_rescale_thetaProd_eq [PadicPlace p] {J X : Type} [Fintype J] [Fintype X]
    {μ : J → X → ℂ_[p]} {m : J → ℕ} {ϖ κ : ℂ_[p]} {W Ξ : MvPowerSeries X (valRingCp p)}
    (hΞ : Ξ.constantCoeff = 0)
    (hW : (C.thetaProd μ m).rescale (fun _ : X ↦ ϖ) = seriesToCp W * expSubst (κ • seriesToCp Ξ)) :
    IsUnit W := by
  have h_const : (W.constantCoeff : ℂ_[p]) = 1 := by
    simpa [constantCoeff_thetaProd, constantCoeff_subst_of_constantCoeff_eq_zero, hΞ] using
      (congrArg (coeff 0) hW).symm
  rw [isUnit_iff_constantCoeff, isUnit_integer_iff_norm_eq_one, h_const, norm_one]

/-- Let `C` be a CM lattice for a prime `d ≡ 7 mod 8`, let the linear forms `μ` be integral, let
`Θ = C.thetaProd μ m = ∏ θ(μ_i z) ^ m i`, where `θ` is the series over `ℂ_[p]` of the normalized
theta function `C.θ` (`PadicPlace p` fixes an embedding of `ℂ` in `ℂ_[p]`), and let `v(ϖ) ≥ ρ_p`,
where `ρ_p = varpiValuation d p` is `1 / (p - 1)`, `1 / (p² - 1)`, `1 / (2 p - 2)` for `p` split,
inert, ramified in `ℚ(√-d)`. There are six integral `δ_c` with `δ 0 = 1` such that `∏ Θ(δ_c ϖ z)`
is integral with constant term `1`. -/
lemma exists_prod_rescale_rescale_thetaProd_eq [PadicPlace p] {J X : Type} [Fintype J]
    [Fintype X] {μ : J → X → ℂ_[p]} (m : J → ℕ) {ϖ : ℂ_[p]}
    (hμ : ∀ (i : J) (x : X), ‖μ i x‖ ≤ 1) (hϖ : ‖ϖ‖ ≤ p ^ (-varpiValuation d p)) :
    ∃ (δ : Fin 6 → ℂ_[p]) (U : MvPowerSeries X (valRingCp p)),
      δ 0 = 1 ∧ (∀ c : Fin 6, ‖δ c‖ ≤ 1) ∧ U.constantCoeff = 1 ∧
      ∏ c : Fin 6, ((C.thetaProd μ m).rescale fun _ : X ↦ ϖ).rescale (fun _ : X ↦ δ c) =
        seriesToCp U := by
  -- the product lies in `C.multiSeriesRing μ`, whose rescaled series are integral
  obtain ⟨δ, hδ, h_mem, -, h_const⟩ : ∃ δ : Fin 6 → ℤ_[p], δ 0 = 1 ∧
      C.scaledThetaProd μ m δ ∈ C.multiSeriesRing μ ∧
      (∃ V ∈ C.multiSeriesRing μ, C.scaledThetaProd μ m δ * V = 1) ∧
      constantCoeff (C.scaledThetaProd μ m δ) = 1 := C.exists_scaledThetaProd_mem_mul_eq_one μ m
  obtain ⟨U, hU : seriesToCp U = (C.scaledThetaProd μ m δ).rescale fun _ : X ↦ ϖ⟩ :=
    C.rescale_mem_range_seriesToCp_of_mem_multiSeriesRing hμ hϖ h_mem
  have hU_const : (U.constantCoeff : ℂ_[p]) = 1 := by simpa [h_const] using congrArg (coeff 0) hU
  refine ⟨fun c ↦ algebraMap ℚ_[p] ℂ_[p] (δ c), U, by simp [hδ], fun c ↦ ?_,
    Subtype.ext hU_const, ?_⟩
  · simpa using (δ c).norm_le_one
  · simp only [hU, scaledThetaProd, map_prod, rescale_rescale, mul_comm]

/-- Let `C` be a CM lattice for a prime `d ≡ 7 mod 8`, and let `θ`, `y` be the series over `ℂ_[p]`
of the normalized theta function `C.θ` and of the function `C.translatedY` of `℘` and `℘'` at
`z + t`. Let `Θ = C.thetaProd μ m = ∏ θ(μ_i z) ^ m i` for integral linear forms `μ_i`. The ring
`C.multiSeriesRing μ` consists of the integral series in the `y(μ_i z)`.

Let `p > 2` be inert, and let `Θ` have the normal form `Θ(ϖ z) = W exp (ϖ ^ (p + 1) / p * ∑ l a b •
Γ_a ^ p ^ b)` with `W` integral, `a` odd in the sum, `Γ_a` the sum of all
`z_τ ^ p ^ a * z_(pr a τ)`, `v(ϖ) = ρ_p = varpiValuation d p` and with `l a 0` a unit for odd `a`.
For a coupling family (odd `e τ`, each coupling `z_τ ^ p ^ e τ * z_(τ⁺)`, `τ ∈ Φ₀`,
`τ⁺ = pr (e τ) τ`, of strictly lowest degree among the `z_τ₁ ^ p ^ a * z_(τ⁺)` with `τ₁ ∈ Φ₀`, `a`
odd and `pr a τ₁ = τ⁺`) let `ν = ν' + ν''` be the degree of `∏ (z_τ ^ p ^ e τ * z_(τ⁺)) ^ j τ`, with
`ν' = powerDegree p Φ₀ e j` and `ν'' = partnerDegree pr Φ₀ e j`. Let `val₆(ν)` be the least
valuation of a coefficient of degree `ν` in a product `∏ (H_c Θ)(z_c)` over six copies, with
`H_c ∈ C.multiSeriesRing μ`. Then `v(ν''!) + val₆(ν) ≤ |j| / (p - 1) - |j| - ρ_p |ν|` with
`|j| = ∑ j τ` and `ν''! = ∏ (ν'' x)!`. -/
lemma leastValLE_partnerDegree_of_isCouplingFamily [PadicPlace p] {J Φ : Type}
    [Fintype J] [Fintype Φ] {μ : J → Φ × Unit → ℂ_[p]} {m : J → ℕ} {pr : ℕ → Φ → Φ} {ϖ : ℂ_[p]}
    {l : ℕ → ℕ → valRingCp p} {Φ₀ : Finset Φ} {e : Φ → ℕ} (h_inert : chiK d p = -1) (hp : 2 < p)
    (hμ : ∀ (i : J) (x : Φ × Unit), ‖μ i x‖ ≤ 1) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hl : ∀ a : ℕ, Odd a → IsUnit (l a 0))
    (hΘ : HasNormalForm (partnerExponents d p) pr ϖ l (C.thetaProd μ m))
    (he : IsCouplingFamily pr Φ₀ e) (j : Φ → ℕ) :
    C.LeastValLE μ m 6 (powerDegree p Φ₀ e j + partnerDegree pr Φ₀ e j)
      ((∑ τ ∈ Φ₀, (j τ : ℝ)) / (p - 1) - ∑ τ ∈ Φ₀, (j τ : ℝ) -
        varpiValuation d p * (powerDegree p Φ₀ e j + partnerDegree pr Φ₀ e j).degree -
        ∑ x : Φ × Unit, (padicValNat p (partnerDegree pr Φ₀ e j x)! : ℝ)) := by
  classical
  -- Substitute `z_0 = z' + z''` and `z_c = δ_c z'` in `∏ Θ(z_c)` and scale by `ϖ`; the coefficient
  -- of `z' ^ ν' * z'' ^ ν''` is given by `norm_coeff_pairExponent`.
  set ν' : Φ × Unit →₀ ℕ := powerDegree p Φ₀ e j
  set ν'' : Φ × Unit →₀ ℕ := partnerDegree pr Φ₀ e j
  set ρ : ℝ := varpiValuation d p
  have hp_pos : (0 : ℝ) < p := by positivity
  rw [partnerExponents_of_inert h_inert] at hΘ
  obtain ⟨W, hW : (C.thetaProd μ m).rescale (fun _ : Φ × Unit ↦ ϖ) = seriesToCp W *
      expSubst ((ϖ ^ (p + 1) / p) • seriesToCp (couplingSum {a : ℕ | Odd a} pr l))⟩ := hΘ
  have hW_unit : IsUnit W := C.isUnit_of_rescale_thetaProd_eq constantCoeff_couplingSum hW
  have h_norm : ‖ϖ ^ (p + 1) / p‖ = p ^ (1 - 1 / (p - 1) : ℝ) :=
    norm_pow_div_of_inert h_inert hϖ
  -- The coefficient for the scaled series `Θ(ϖ z)`, with `∏ Θ(δ_c ϖ z) = U` integral.
  obtain ⟨δ, U, hδ_zero, hδ_le, hU_const, h_prod⟩ :
      ∃ (δ : Fin 6 → ℂ_[p]) (U : MvPowerSeries (Φ × Unit) (valRingCp p)),
        δ 0 = 1 ∧ (∀ c : Fin 6, ‖δ c‖ ≤ 1) ∧ U.constantCoeff = 1 ∧
        ∏ c : Fin 6, ((C.thetaProd μ m).rescale fun _ ↦ ϖ).rescale (fun _ ↦ δ c) = seriesToCp U :=
    C.exists_prod_rescale_rescale_thetaProd_eq m hμ hϖ.le
  have h_scaled : ‖∏ x : Φ × Unit, ((ν'' x)! : ℂ_[p])‖ * ‖coeff (pairExponent ν' ν'')
      (∏ c : Fin 6, copySubst (couplingSubst δ c) ((C.thetaProd μ m).rescale fun _ ↦ ϖ))‖ =
        ‖ϖ ^ (p + 1) / p‖ ^ ∑ τ ∈ Φ₀, j τ :=
    he.norm_coeff_pairExponent hl (one_lt_norm_pow_div_of_inert h_inert hp hϖ)
      hW_unit hU_const hW hδ_zero h_prod j
  -- Undoing the scaling by `ϖ` lowers the valuation by `ρ_p |ν|`.
  set G : MvPowerSeries ((Φ × Unit) × Fin 2) ℂ_[p] :=
    ∏ c : Fin 6, copySubst (couplingSubst δ c) (C.thetaProd μ m) with hG
  set valFact : ℝ := ∑ x : Φ × Unit, (padicValNat p (ν'' x)! : ℝ) with h_valFact
  set sumJ : ℝ := ∑ τ ∈ Φ₀, (j τ : ℝ) with h_sumJ
  have h_degree : (pairExponent ν' ν'').degree = (ν' + ν'').degree := by
    rw [← mapDomain_fst_pairExponent, Finsupp.degree_mapDomain]
  have h_fact : ‖∏ x : Φ × Unit, ((ν'' x)! : ℂ_[p])‖ = p ^ (-valFact) := by
    simp [h_valFact, norm_natCast_eq_inv_pow_padicValNat, factorial_ne_zero,
      Real.rpow_neg hp_pos.le, ← cast_sum, prod_pow_eq_pow_sum]
  have h_rpow : p ^ (-valFact + -ρ * (ν' + ν'').degree) * ‖coeff (pairExponent ν' ν'') G‖ =
      p ^ ((1 - 1 / (p - 1)) * sumJ) := by
    rw [coeff_prod_copySubst_rescale, norm_mul, norm_pow, h_degree, h_fact, hϖ, h_norm] at h_scaled
    rw [Real.rpow_add hp_pos, Real.rpow_mul_natCast hp_pos.le, mul_assoc, h_scaled, h_sumJ,
      ← cast_sum, Real.rpow_mul_natCast hp_pos.le]
  -- Solve for the norm of the coefficient.
  rw [mul_comm, ← eq_div_iff (by positivity), ← Real.rpow_sub hp_pos] at h_rpow
  -- The substitution is integral, so this coefficient bounds `val₆(ν)`.
  have h_le : (p : ℝ) ^ (-(sumJ / (p - 1) - sumJ - ρ * (ν' + ν'').degree - valFact)) ≤
      ‖coeff (pairExponent ν' ν'') (∏ c, copySubst (couplingSubst δ c) (1 * C.thetaProd μ m))‖ := by
    simp only [one_mul, ← hG, h_rpow]
    exact le_of_eq (by ring_nf)
  simpa only [mapDomain_fst_pairExponent] using
    leastValLE_of_copySubst (norm_couplingSubst_le_one hδ_le) (fun _ ↦ one_mem _) h_le

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
/-- Couplings. Let `C` be a CM lattice for a prime `d ≡ 7 mod 8`, let `θ` be the series over `ℂ_[p]`
of its normalized theta function `C.θ`, let `p > 2` be inert in `ℚ(√-d)`, let the linear forms `μ`
be integral, and let the theta product `Θ = C.thetaProd μ m = ∏ θ(μ_i z) ^ m i` have the normal form
`Θ(ϖ z) = W exp (ϖ ^ (p + 1) / p * ∑ l a b • Γ_a ^ p ^ b)` with `W` integral, `a` odd in the sum,
`Γ_a` the sum of all `z_τ ^ p ^ a * z_(pr a τ)`, `v(ϖ) = ρ_p = varpiValuation d p` and `l a 0` a
unit for odd `a`. For a coupling family (odd `e τ`, each coupling `z_τ ^ p ^ e τ * z_(τ⁺)`,
`τ ∈ Φ₀`, `τ⁺ = pr (e τ) τ`, of strictly lowest degree among those with the partner `τ⁺`) let `ν'`
and `ν''` be the degrees of `∏ z_τ ^ (p ^ e τ * j τ)` and `∏ z_(τ⁺) ^ j τ`, and `ν = ν' + ν''`. Let
`val₆(ν)` be the least valuation of a coefficient of degree `ν` in a product `∏ (H_c Θ)(z_c)` over
six copies, with `H_c` in the ring `C.multiSeriesRing μ` of integral series in the `y(μ_i z)`, where
`y` is the series of `C.translatedY`. Then `val₆(ν) ≤ -|j|` and
`v(ν'! ν''!) + val₆(ν) ≤ γ_p |ν| - |j|`, where `|j| = ∑ j τ` and
`γ_p = gammaPrime d p = 1 / (p - 1) - ρ_p = p / (p² - 1)`. -/
lemma leastValLE_six_of_isCouplingFamily [PadicPlace p] {J Φ : Type}
    [Fintype J] [Fintype Φ] {μ : J → Φ × Unit → ℂ_[p]} {m : J → ℕ} {pr : ℕ → Φ → Φ} {ϖ : ℂ_[p]}
    {l : ℕ → ℕ → valRingCp p} {Φ₀ : Finset Φ} {e : Φ → ℕ} (h_inert : chiK d p = -1) (hp : 2 < p)
    (hμ : ∀ (i : J) (x : Φ × Unit), ‖μ i x‖ ≤ 1) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hl : ∀ a : ℕ, Odd a → IsUnit (l a 0))
    (hΘ : HasNormalForm (partnerExponents d p) pr ϖ l (C.thetaProd μ m))
    (he : IsCouplingFamily pr Φ₀ e) (j : Φ → ℕ) :
    C.LeastValLE μ m 6 (powerDegree p Φ₀ e j + partnerDegree pr Φ₀ e j) (-∑ τ ∈ Φ₀, (j τ : ℝ)) ∧
    C.LeastValLE μ m 6 (powerDegree p Φ₀ e j + partnerDegree pr Φ₀ e j)
      (gammaPrime d p * (powerDegree p Φ₀ e j + partnerDegree pr Φ₀ e j).degree -
        ∑ τ ∈ Φ₀, (j τ : ℝ) -
        ∑ x : Φ × Unit, (padicValNat p (powerDegree p Φ₀ e j x)! : ℝ) -
        ∑ x : Φ × Unit, (padicValNat p (partnerDegree pr Φ₀ e j x)! : ℝ)) := by
  set ν' : Φ × Unit →₀ ℕ := powerDegree p Φ₀ e j
  set ν'' : Φ × Unit →₀ ℕ := partnerDegree pr Φ₀ e j
  set ρ : ℝ := varpiValuation d p
  set sumJ : ℝ := ∑ τ ∈ Φ₀, (j τ : ℝ) with h_sumJ
  have h_val : C.LeastValLE μ m 6 (ν' + ν'') (sumJ / (p - 1) - sumJ - ρ * (ν' + ν'').degree -
      ∑ x : Φ × Unit, (padicValNat p (ν'' x)! : ℝ)) :=
    C.leastValLE_partnerDegree_of_isCouplingFamily h_inert hp hμ hϖ hl hΘ he j
  have h_degree : ((ν' + ν'').degree : ℝ) = ν'.degree + sumJ := by
    simp [ν'', sumJ, degree_partnerDegree]
  refine ⟨h_val.mono ?_, h_val.mono ?_⟩
  · -- `|ν| ≥ (p + 1) |j|` and `ρ_p (p + 1) = 1 / (p - 1)`
    have h_power : p * sumJ ≤ ν'.degree := by
      rw [degree_powerDegree, cast_sum, h_sumJ, mul_sum]
      exact sum_le_sum fun τ hτ ↦
        mod_cast Nat.mul_le_mul_right (j τ) (le_self_pow (he.odd τ hτ).pos.ne' p)
    have h_scale : sumJ / (p - 1) ≤ ρ * (ν' + ν'').degree := by
      rw [h_degree, ← one_div_mul_eq_div, ← varpiValuation_mul_add_one_of_inert h_inert, mul_assoc,
        _root_.add_one_mul]
      exact mul_le_mul_of_nonneg_left (add_le_add_left h_power _) (varpiValuation_nonneg d p)
    linarith [show 0 ≤ ∑ x : Φ × Unit, (padicValNat p (ν'' x)! : ℝ) by positivity]
  · -- `v(ν'!) ≤ |ν'| / (p - 1)` and `|ν| = |ν'| + |j|`
    have h_legendre : ∑ x : Φ × Unit, (padicValNat p (ν' x)! : ℝ) ≤ ν'.degree / (p - 1) := by
      rw [Finsupp.degree_eq_sum, cast_sum, Finset.sum_div]
      exact sum_le_sum fun x _ ↦ (padicValNat_factorial_mem_Icc (Nat.lt_pow_self (by lia))).2
    rw [gammaPrime, sub_mul, one_div_mul_eq_div, h_degree, add_div]
    linarith

end CMLattice

end New
