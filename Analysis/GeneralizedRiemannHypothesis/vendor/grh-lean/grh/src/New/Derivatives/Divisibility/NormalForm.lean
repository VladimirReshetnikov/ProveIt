import Lib.General.Algebra.SeriesBounds
import Lib.General.Algebra.SeriesCongruences
import Lib.General.NumberTheory.PadicLimitsValuation

/-!
# Couplings and the normal form

* `New.coupling`, `New.couplingSum`, `New.HasNormalForm`: the couplings `Γ_e` and the normal form
  `F(ϖ z) = W exp (c_ϖ Ξ)` with `W` integral, `c_ϖ = ϖ ^ (p + 1) / p` and
  `Ξ = ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`, for any rule that assigns partners to places.
* `New.HasNormalForm.rescale`: the normal form is kept, with other numbers `λ_{e j}`, under
  `z ↦ α z` with `α` integral; so its existence depends only on the valuation of `ϖ`
  (`New.HasNormalForm.exists_of_norm_eq`).
* `New.HasNormalForm.norm_coeff_subst_le_one`: if `F` has the normal form and `Z` is integral
  without constant term, then `F(ϖ Z)` is integral in degrees at most `B` if the couplings `Γ_e(Z)`
  with `e ∈ S`, `e ≤ log_p B` are divisible by some `π` with `‖c_ϖ π‖ ≤ p ^ (-1 / (p - 1))`.
* `New.HasNormalForm.of_dvd_sub`: it is enough to know the exponent modulo such a `π`.
* `New.dvd_pderiv_couplingSum_sub`: the derivatives of `Ξ` modulo `p`, if `0 ∉ S`. They are not
  needed for the divisibility bound, only for its sharpness.

## Notation

* `valRingCp p` is the valuation ring `𝒪` of `ℂ_[p]`; a series over it is called integral.
* `seriesToCp W` is the series `W` over `𝒪`, seen as a series over `ℂ_[p]`.
* `expSubst g` is the series `exp g`, for `g` without constant term.
* The variables `z_x` are indexed by pairs `x = (τ, i)` in `Φ × c`, for finite types `Φ` and `c`;
  the elements `τ` of `Φ` are called places.
-/

open MvPowerSeries WithPiTopology IsLocalRing

namespace New

variable {p : ℕ} [Fact p.Prime] {Φ c : Type} [Fintype Φ] [Fintype c]

/-- The coupling `Γ_e = ∑ z_(τ,i) ^ p ^ e * z_(τ',i)`, summed over all `(τ, i) : Φ × c`, where
`τ' = pr e τ` is the partner of `τ`. -/
noncomputable def coupling (pr : ℕ → Φ → Φ) (e : ℕ) : MvPowerSeries (Φ × c) (valRingCp p) :=
  ∑ x : Φ × c, X x ^ p ^ e * X (pr e x.1, x.2)

/-- The series `Ξ = ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`, where `λ_{e j} = l e j` and `Γ_e` is the
coupling for the partner rule `pr`. -/
noncomputable def couplingSum (S : Set ℕ) (pr : ℕ → Φ → Φ) (l : ℕ → ℕ → valRingCp p) :
    MvPowerSeries (Φ × c) (valRingCp p) :=
  ∑' x : S × ℕ, l x.1 x.2 • coupling pr x.1 ^ p ^ x.2

/-- `F` has the normal form with the given numbers `ϖ` and `λ_{e j} = l e j`:
`F(ϖ z) = W exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j)` with `W` integral and
`c_ϖ = ϖ ^ (p + 1) / p`. -/
def HasNormalForm (S : Set ℕ) (pr : ℕ → Φ → Φ) (ϖ : ℂ_[p]) (l : ℕ → ℕ → valRingCp p)
    (F : MvPowerSeries (Φ × c) ℂ_[p]) : Prop :=
  ∃ W : MvPowerSeries (Φ × c) (valRingCp p),
    F.rescale (fun _ : Φ × c ↦ ϖ) =
      seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • seriesToCp (couplingSum S pr l))

variable {S : Set ℕ} {pr : ℕ → Φ → Φ} {ϖ : ℂ_[p]} {l : ℕ → ℕ → valRingCp p}
  {F : MvPowerSeries (Φ × c) ℂ_[p]}

/-- A substitution `Z` that is allowed (`HasSubst Z`) commutes with the exponential:
`(exp g)(Z) = exp (g(Z))` if `g(0) = 0`. -/
lemma subst_expSubst {σ τ : Type} {g : MvPowerSeries σ ℂ_[p]} (hg : constantCoeff g = 0)
    {Z : σ → MvPowerSeries τ ℂ_[p]} (hZ : HasSubst Z) :
    (expSubst g).subst Z = expSubst (g.subst Z) :=
  subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg).const hZ _

/-- The coupling after a substitution: `Γ_e(Z) = ∑ Z_(τ,i) ^ p ^ e * Z_(pr e τ, i)`. -/
lemma subst_coupling {τ : Type} {Z : Φ × c → MvPowerSeries τ (valRingCp p)} (hZ : HasSubst Z)
    (e : ℕ) : (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)).subst Z =
      ∑ x : Φ × c, Z x ^ p ^ e * Z (pr e x.1, x.2) := by
  simp only [coupling, ← coe_substAlgHom hZ, map_sum, map_mul, map_pow, substAlgHom_X]

/-- The coupling `Γ_e` is homogeneous of degree `p ^ e + 1`. -/
lemma rescale_coupling (α : valRingCp p) (e : ℕ) :
    rescale (fun _ : Φ × c ↦ α) (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)) =
      α ^ (p ^ e + 1) • coupling pr e := by
  rw [rescale_eq_subst, subst_coupling (HasSubst.smul_X _), coupling, Finset.smul_sum]
  simp only [Pi.smul_apply', smul_pow, smul_mul_smul_comm, pow_succ]

/-- The coupling `Γ_e` has order at least `p ^ e + 1`. -/
lemma le_order_coupling (e : ℕ) :
    ((p ^ e + 1 : ℕ) : ℕ∞) ≤ (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)).order := by
  refine le_order fun d hd ↦ ?_
  rw [coupling, map_sum]
  refine Finset.sum_eq_zero fun x _ ↦ coeff_of_lt_order (hd.trans_le ?_)
  grw [← le_order_mul, ← le_order_pow_of_constantCoeff_eq_zero _ (constantCoeff_X x),
    ← one_le_order_iff_constCoeff_eq_zero.2 (constantCoeff_X _), Nat.cast_succ]

/-- The sum `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j` that defines `couplingSum S pr l` converges, as the
orders of its terms tend to infinity. -/
lemma hasSum_couplingSum :
    HasSum (fun x : S × ℕ ↦ l x.1 x.2 • coupling pr x.1 ^ p ^ x.2)
      (couplingSum S pr l : MvPowerSeries (Φ × c) (valRingCp p)) :=
  (summable_smul_pow_pow (Fact.out : p.Prime).one_lt le_order_coupling S l).hasSum

/-- The series `couplingSum S pr l = ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j` has no constant term. -/
lemma constantCoeff_couplingSum :
    constantCoeff (couplingSum S pr l : MvPowerSeries (Φ × c) (valRingCp p)) = 0 := by
  refine ((hasSum_couplingSum (S := S) (pr := pr) (l := l)).map constantCoeff
    (continuous_constantCoeff _)).unique ?_
  simp [Function.comp_def, coupling, (Fact.out : p.Prime).ne_zero]

/-- A substitution of series `Z_x` without constant term into
`couplingSum S pr l = ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`, where `λ_{e j} = l e j` and
`Γ_e = coupling pr e`, may be carried out term by term. -/
lemma hasSum_subst_couplingSum {τ : Type} {Z : Φ × c → MvPowerSeries τ (valRingCp p)}
    (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) :
    HasSum (fun x : S × ℕ ↦ l x.1 x.2 • (coupling (p := p) pr x.1).subst Z ^ p ^ x.2)
      ((couplingSum S pr l).subst Z) := by
  have h_subst : HasSubst Z := hasSubst_of_constantCoeff_zero hZ
  simpa only [Function.comp_def, coe_substAlgHom, subst_smul h_subst, subst_pow h_subst] using
    (hasSum_couplingSum (S := S) (pr := pr) (l := l)).map (substAlgHom h_subst)
      (by simpa only [coe_substAlgHom] using continuous_subst_of_constantCoeff_eq_zero hZ)

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. As `Γ_e` is
homogeneous of degree `p ^ e + 1`, the series `Ξ(α z)` is the same sum with `λ_{e j}` multiplied by
`α ^ ((p ^ e + 1) p ^ j)`. -/
lemma rescale_couplingSum (α : valRingCp p) :
    rescale (fun _ : Φ × c ↦ α) (couplingSum S pr l : MvPowerSeries (Φ × c) (valRingCp p)) =
      couplingSum S pr fun e j : ℕ ↦ α ^ ((p ^ e + 1) * p ^ j) * l e j := by
  let Z : Φ × c → MvPowerSeries (Φ × c) (valRingCp p) := (fun _ : Φ × c ↦ α) • X
  have h_term (x : S × ℕ) : l x.1 x.2 • (coupling (p := p) pr x.1).subst Z ^ p ^ x.2 =
      (α ^ ((p ^ (x.1 : ℕ) + 1) * p ^ x.2) * l x.1 x.2) • coupling pr x.1 ^ p ^ x.2 := by
    rw [← rescale_eq_subst, rescale_coupling, smul_pow, smul_smul, ← pow_mul, mul_comm (l _ _)]
  rw [rescale_eq_subst]
  refine (hasSum_subst_couplingSum (Z := Z) fun x ↦ by simp [Z]).unique ?_
  simpa only [h_term] using hasSum_couplingSum (l := fun e j ↦ α ^ ((p ^ e + 1) * p ^ j) * l e j)

/-- If `‖a π‖ ≤ p ^ (-1 / (p - 1))` and the integral series `G` has no constant term and
coefficients divisible by `π` in degrees at most `B`, then `exp (a G)` is integral in these
degrees. -/
lemma norm_coeff_expSubst_smul_le_one {τ : Type} {a : ℂ_[p]} {π : valRingCp p}
    (hπ : ‖a * π‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) {G : MvPowerSeries τ (valRingCp p)}
    (hG : constantCoeff G = 0) {B : ℕ} (h_dvd : ∀ d : τ →₀ ℕ, d.degree ≤ B → π ∣ coeff d G)
    {m : τ →₀ ℕ} (hm : m.degree ≤ B) : ‖coeff m (expSubst (a • seriesToCp G))‖ ≤ 1 := by
  refine norm_coeff_expSubst_le_one (by simp [hG]) (fun d hd ↦ ?_) hm
  calc ‖coeff d (a • seriesToCp G)‖ = ‖a * (coeff d G : valRingCp p)‖ := rfl
    _ ≤ p ^ (-(1 / (p - 1)) : ℝ) := by
      grw [← hπ, norm_mul, norm_mul, dvd_iff_norm_le.1 (h_dvd d hd)]

/-- To prove that `F` has the normal form `F(ϖ z) = W exp (c_ϖ Ξ₀)`, where `W` is integral,
`c_ϖ = ϖ ^ (p + 1) / p` and `Ξ₀ = couplingSum S pr l`, it is enough to know the exponent modulo a
`π` with `‖c_ϖ π‖ ≤ p ^ (-1 / (p - 1))`: it suffices that `F(ϖ z) = W exp (c_ϖ Ξ)` with `W`, `Ξ`
integral, `Ξ(0) = 0` and `Ξ ≡ Ξ₀` modulo `π`. -/
lemma HasNormalForm.of_dvd_sub {π : valRingCp p}
    (hπ : ‖ϖ ^ (p + 1) / p * π‖ ≤ p ^ (-(1 / (p - 1)) : ℝ))
    {W Ξ : MvPowerSeries (Φ × c) (valRingCp p)} (hΞ : constantCoeff Ξ = 0)
    (h_dvd : C π ∣ Ξ - couplingSum S pr l)
    (hF : F.rescale (fun _ : Φ × c ↦ ϖ) =
      seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • seriesToCp Ξ)) :
    HasNormalForm S pr ϖ l F := by
  -- The exponential `V` of `c_ϖ` times the difference `G` is integral and is moved into `W`.
  let a : ℂ_[p] := ϖ ^ (p + 1) / p
  set G : MvPowerSeries (Φ × c) (valRingCp p) := Ξ - couplingSum S pr l with hG
  have hG_zero : constantCoeff G = 0 := by simp [hG, hΞ, constantCoeff_couplingSum]
  have h_int (d : Φ × c →₀ ℕ) : ‖coeff d (expSubst (a • seriesToCp G))‖ ≤ 1 :=
    norm_coeff_expSubst_smul_le_one hπ hG_zero
      (fun d' _ ↦ C_dvd_iff_forall_dvd_coeff.1 h_dvd d') le_rfl
  obtain ⟨V, hV⟩ : ∃ V : MvPowerSeries (Φ × c) (valRingCp p),
      seriesToCp V = expSubst (a • seriesToCp G) := ⟨fun d ↦ ⟨_, h_int d⟩, rfl⟩
  have h_exp : expSubst (a • seriesToCp Ξ) =
      seriesToCp V * expSubst (a • seriesToCp (couplingSum S pr l)) := by
    rw [hV, ← expSubst_add _ (by simp [hG_zero]) (by simp [constantCoeff_couplingSum]), ← smul_add,
      ← map_add, hG, sub_add_cancel]
  exact ⟨W * V, by rw [hF, h_exp, map_mul seriesToCp W V, mul_assoc]⟩

/-- Let `F` have the normal form `F(ϖ z) = W exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j)` with `W`
integral. If the series `Z_x` are integral without constant term, then `F(ϖ Z)` is an integral
series times `exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e(Z) ^ p ^ j)`. -/
lemma HasNormalForm.exists_subst_eq_mul_expSubst (hF : HasNormalForm S pr ϖ l F) {τ : Type}
    {Z : Φ × c → MvPowerSeries τ (valRingCp p)} (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) :
    ∃ W : MvPowerSeries τ (valRingCp p),
      F.subst (fun x : Φ × c ↦ ϖ • seriesToCp (Z x)) =
        seriesToCp W *
          expSubst ((ϖ ^ (p + 1) / p) • seriesToCp ((couplingSum S pr l).subst Z)) := by
  obtain ⟨W, hW⟩ := hF
  have hZ_subst : HasSubst Z := hasSubst_of_constantCoeff_zero hZ
  have h_subst : HasSubst fun x : Φ × c ↦ seriesToCp (Z x) := hZ_subst.map _
  have h_rescale : F.subst (fun x : Φ × c ↦ ϖ • seriesToCp (Z x)) =
      (F.rescale fun _ ↦ ϖ).subst fun x : Φ × c ↦ seriesToCp (Z x) := by
    rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X _) h_subst]
    simp only [Pi.smul_apply', subst_smul h_subst, subst_X h_subst]
  refine ⟨W.subst Z, ?_⟩
  rw [h_rescale, hW, subst_mul h_subst, subst_expSubst (by simp [constantCoeff_couplingSum])
    h_subst, subst_smul h_subst, map_subst hZ_subst, map_subst hZ_subst]

/-- Let `F` have the normal form `F(ϖ z) = W exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j)` with `W`
integral. Then, for integral `α`, the series `F(α z)` has the normal form with the same `ϖ` and with
`λ_{e j}` multiplied by `α ^ ((p ^ e + 1) p ^ j)`. -/
lemma HasNormalForm.rescale (hF : HasNormalForm S pr ϖ l F) (α : valRingCp p) :
    HasNormalForm S pr ϖ (fun e j : ℕ ↦ α ^ ((p ^ e + 1) * p ^ j) * l e j)
      (F.rescale fun _ : Φ × c ↦ (α : ℂ_[p])) := by
  let Z : Φ × c → MvPowerSeries (Φ × c) (valRingCp p) := (fun _ : Φ × c ↦ α) • X
  have h_subst : (F.rescale fun _ ↦ (α : ℂ_[p])).rescale (fun _ ↦ ϖ) =
      F.subst fun x : Φ × c ↦ ϖ • seriesToCp (Z x) := by
    rw [rescale_rescale, rescale_eq_subst]
    congr! with x
    simp [Z, smul_smul, mul_comm]
  unfold HasNormalForm
  rw [h_subst, ← rescale_couplingSum, rescale_eq_subst _ (couplingSum S pr l)]
  exact hF.exists_subst_eq_mul_expSubst fun x ↦ by simp [Z]

/-- Let `F` have the normal form `F(ϖ z) = W exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j)` with `W`
integral. The existence of such a form depends only on the valuation of `ϖ`: if `ϖ ≠ 0` and
`‖ϖ'‖ = ‖ϖ‖`, then `F` has it for `ϖ'`, with other numbers `λ'_{e j} = l' e j` in place of the
`λ_{e j}`. -/
lemma HasNormalForm.exists_of_norm_eq (hF : HasNormalForm S pr ϖ l F) (hϖ : ϖ ≠ 0) {ϖ' : ℂ_[p]}
    (h_norm : ‖ϖ'‖ = ‖ϖ‖) : ∃ l' : ℕ → ℕ → valRingCp p, HasNormalForm S pr ϖ' l' F := by
  -- Scale by the unit `ϖ' / ϖ`, and move the unit `c_ϖ / c_ϖ'` into the numbers `λ_{e j}`.
  have hϖ' : ϖ' ≠ 0 := by rwa [← norm_ne_zero_iff, h_norm, norm_ne_zero_iff]
  let α : valRingCp p := ⟨ϖ' / ϖ, (norm_div ϖ' ϖ).trans_le (by simp [h_norm, hϖ])⟩
  let β : valRingCp p := ⟨ϖ / ϖ', (norm_div ϖ ϖ').trans_le (by simp [h_norm, hϖ])⟩
  let l₁ (e j : ℕ) : valRingCp p := α ^ ((p ^ e + 1) * p ^ j) * l e j
  have h_sum : (couplingSum S pr fun e j ↦ β ^ (p + 1) * l₁ e j :
      MvPowerSeries (Φ × c) (valRingCp p)) = β ^ (p + 1) • couplingSum S pr l₁ :=
    hasSum_couplingSum.unique <| by
      simpa only [mul_smul, smul_eq_C_mul] using hasSum_couplingSum.mul_left (C (β ^ (p + 1)))
  have h_scale : (fun _ : Φ × c ↦ ϖ') = (fun _ ↦ (α : ℂ_[p])) * fun _ ↦ ϖ :=
    funext fun _ ↦ (div_mul_cancel₀ ϖ' hϖ).symm
  have h_const : ϖ' ^ (p + 1) / p * (β ^ (p + 1) : valRingCp p) = ϖ ^ (p + 1) / p := by
    simp [β, div_mul_eq_mul_div, ← mul_pow, mul_div_cancel₀ ϖ hϖ']
  obtain ⟨W, hW⟩ : HasNormalForm S pr ϖ l₁ (F.rescale fun _ ↦ (α : ℂ_[p])) := hF.rescale α
  refine ⟨fun e j ↦ β ^ (p + 1) * l₁ e j, W, ?_⟩
  rw [h_sum, seriesToCp_smul, smul_smul, h_const, ← hW, rescale_rescale, h_scale]

/-- Let `Γ_e = coupling pr e` be the coupling `∑ z_(τ,i) ^ p ^ e * z_(pr e τ, i)`, homogeneous of
degree `p ^ e + 1`. A substitution of series `Z_x` without constant term does not lower orders, so
`Γ_e(Z) ^ p ^ j` has order at least `p ^ e + 1`. -/
lemma le_order_subst_coupling_pow {τ : Type} {Z : Φ × c → MvPowerSeries τ (valRingCp p)}
    (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) (e j : ℕ) :
    ((p ^ e + 1 : ℕ) : ℕ∞) ≤ ((coupling (p := p) pr e).subst Z ^ p ^ j).order := by
  calc ((p ^ e + 1 : ℕ) : ℕ∞) ≤ (coupling (p := p) (c := c) pr e).order := le_order_coupling e
    _ ≤ ((coupling (p := p) pr e).subst Z).order := by
      grw [← le_order_subst (hasSubst_of_constantCoeff_zero hZ),
        ← le_iInf fun x ↦ one_le_order_iff_constCoeff_eq_zero.2 (hZ x), one_mul]
    _ ≤ ((coupling (p := p) pr e).subst Z ^ p ^ j).order := by
      grw [← le_order_pow, ← Nat.one_le_pow j p (Fact.out : p.Prime).pos, one_nsmul]

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. If the series
`Z_x` have no constant term and `π` divides `Γ_e(Z)` for all `e ∈ S` with `e ≤ log_p B`, then `π`
divides the coefficients of `Ξ(Z)` in degrees at most `B`. -/
lemma dvd_coeff_subst_couplingSum {π : valRingCp p} {τ : Type}
    {Z : Φ × c → MvPowerSeries τ (valRingCp p)} (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) {B : ℕ}
    (hΓ : ∀ e ∈ S, e ≤ p.log B →
      C π ∣ (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)).subst Z)
    {d : τ →₀ ℕ} (hd : d.degree ≤ B) : π ∣ coeff d ((couplingSum S pr l).subst Z) := by
  have hp : p.Prime := Fact.out
  refine dvd_of_hasSum (hasSum_iff_hasSum_coeff.1 (hasSum_subst_couplingSum hZ) d) ?_
  rintro ⟨⟨e, he⟩, j⟩
  set G : MvPowerSeries τ (valRingCp p) := (coupling (p := p) pr e).subst Z ^ p ^ j
  suffices h_dvd : π ∣ coeff d G by simpa only [coeff_smul] using h_dvd.mul_left (l e j)
  obtain h_le | h_lt := le_or_gt e (p.log B)
  · exact C_dvd_iff_forall_dvd_coeff.1 ((hΓ e he h_le).pow (pow_ne_zero j hp.ne_zero)) d
  · have h_deg : d.degree < p ^ e + 1 :=
      (hd.trans_lt (Nat.lt_pow_of_log_lt hp.one_lt h_lt)).trans (Nat.lt_succ_self _)
    rw [coeff_of_lt_order ((Nat.cast_lt.2 h_deg).trans_le (le_order_subst_coupling_pow hZ e j))]
    exact dvd_zero π

/-- Let `F` have the normal form `F(ϖ z) = W exp (c_ϖ ∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j)`. Let
`‖c_ϖ π‖ ≤ p ^ (-1 / (p - 1))`, and let the series `Z_x` be integral without constant term, with `π`
dividing `Γ_e(Z)` for all `e ∈ S` with `e ≤ log_p B`. Then the coefficients of `F(ϖ Z)` in degrees
at most `B` have norm at most `1`. -/
lemma HasNormalForm.norm_coeff_subst_le_one (hF : HasNormalForm S pr ϖ l F) {π : valRingCp p}
    (hπ : ‖ϖ ^ (p + 1) / p * π‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) {τ : Type}
    {Z : Φ × c → MvPowerSeries τ (valRingCp p)} (hZ : ∀ x : Φ × c, constantCoeff (Z x) = 0) {B : ℕ}
    (hΓ : ∀ e ∈ S, e ≤ p.log B →
      C π ∣ (coupling pr e : MvPowerSeries (Φ × c) (valRingCp p)).subst Z)
    {m : τ →₀ ℕ} (hm : m.degree ≤ B) :
    ‖coeff m (F.subst fun x : Φ × c ↦ ϖ • seriesToCp (Z x))‖ ≤ 1 := by
  classical
  set Ξ : MvPowerSeries τ (valRingCp p) := (couplingSum S pr l).subst Z
  have h_zero : constantCoeff Ξ = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hZ) hZ constantCoeff_couplingSum
  have h_exp (d : τ →₀ ℕ) (hd : d.degree ≤ B) :
      ‖coeff d (expSubst ((ϖ ^ (p + 1) / p) • seriesToCp Ξ))‖ ≤ 1 :=
    norm_coeff_expSubst_smul_le_one hπ h_zero
      (fun _ hd' ↦ dvd_coeff_subst_couplingSum hZ hΓ hd') hd
  obtain ⟨W, hW⟩ : ∃ W : MvPowerSeries τ (valRingCp p),
      F.subst (fun x : Φ × c ↦ ϖ • seriesToCp (Z x)) =
        seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • seriesToCp Ξ) :=
          hF.exists_subst_eq_mul_expSubst hZ
  rw [hW, coeff_mul]
  refine sum_mem (S := valRingCp p) fun ⟨d₁, d₂⟩ hd ↦ ?_
  have h_le : d₂ ≤ m := le_of_add_le_right (Finset.HasAntidiagonal.mem_antidiagonal.1 hd).le
  exact mul_mem (coeff d₁ W).property (h_exp d₂ ((Finsupp.degree_mono h_le).trans hm))

variable [DecidableEq Φ] [DecidableEq c]

open Classical in
/-- The sum of the powers `z_x ^ p ^ e` over the `x = (τ, i)` whose partner `(pr e τ, i)` in the
coupling `Γ_e` is `y`. -/
noncomputable def partnerPowerSum (pr : ℕ → Φ → Φ) (e : ℕ) (y : Φ × c) :
    MvPowerSeries (Φ × c) (valRingCp p) :=
  ∑ x : Φ × c with (pr e x.1, x.2) = y, X x ^ p ^ e

/-- The derivatives of a `p ^ e`-th power vanish modulo `p`, for `e > 0`. -/
lemma dvd_pderiv_pow_pow {σ : Type} (G : MvPowerSeries σ (valRingCp p)) {e : ℕ} (he : e ≠ 0)
    (y : σ) : C (p : valRingCp p) ∣ pderiv y (G ^ p ^ e) := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, Nat.cast_pow, map_natCast]
  exact (dvd_pow_self _ he).mul_right _

/-- For `e > 0`, only the linear factors of the coupling
`Γ_e = coupling pr e = ∑_{(τ, i)} z_(τ,i) ^ p ^ e * z_(pr e τ, i)` have a derivative modulo `p`:
`∂Γ_e / ∂z_y` is congruent to `partnerPowerSum pr e y`, the sum of the `z_x ^ p ^ e` over the
`x = (τ, i)` whose partner `(pr e τ, i)` is `y`. -/
lemma dvd_pderiv_coupling_sub {e : ℕ} (he : e ≠ 0) (y : Φ × c) :
    C (p : valRingCp p) ∣ pderiv y (coupling pr e) - partnerPowerSum pr e y := by
  classical
  rw [coupling, map_sum, partnerPowerSum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun x _ ↦ ?_
  have h_linear : X x ^ p ^ e * pderiv y (X (pr e x.1, x.2)) =
      if (pr e x.1, x.2) = y then X (R := valRingCp p) x ^ p ^ e else 0 := by
        simp [pderiv_X, Pi.single_apply]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h_linear, add_sub_cancel_left]
  exact (dvd_pderiv_pow_pow (X x) he y).mul_left _

/-- If `y` is the partner of `x` for `e`, then `z_x ^ p ^ e` has coefficient `1` in
`partnerPowerSum pr e y`. -/
lemma coeff_partnerPowerSum_self (e : ℕ) (x : Φ × c) :
    coeff (.single x (p ^ e)) (partnerPowerSum (p := p) pr e (pr e x.1, x.2)) = 1 := by
  classical
  simp [partnerPowerSum, coeff_X_pow,
    Finsupp.single_left_inj (pow_ne_zero e (Fact.out : p.Prime).ne_zero)]

/-- The only monomials of `partnerPowerSum pr e y` are the `z_x ^ p ^ e` with `y` the partner of
`x` for `e`. -/
lemma exists_single_of_coeff_partnerPowerSum_ne_zero {e : ℕ} {y : Φ × c} {d : Φ × c →₀ ℕ}
    (h_ne : coeff d (partnerPowerSum (p := p) pr e y) ≠ 0) :
    ∃ x : Φ × c, (pr e x.1, x.2) = y ∧ d = .single x (p ^ e) := by
  classical
  rw [partnerPowerSum, map_sum] at h_ne
  obtain ⟨x, hx, h_coeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_ne
  exact ⟨x, (Finset.mem_filter.1 hx).2, by simpa [coeff_X_pow] using h_coeff⟩

/-- The series `partnerPowerSum pr e y` has order at least `p ^ e`. -/
lemma le_order_partnerPowerSum (e : ℕ) (y : Φ × c) :
    ((p ^ e : ℕ) : ℕ∞) ≤ (partnerPowerSum (p := p) pr e y).order := by
  refine le_order fun d hd ↦ by_contra fun h_ne ↦ ?_
  obtain ⟨x, -, rfl⟩ := exists_single_of_coeff_partnerPowerSum_ne_zero h_ne
  simp at hd

/-- The sum `∑_{e ∈ S} λ_{e 0} * partnerPowerSum pr e y`, where `λ_{e 0} = l e 0` and
`partnerPowerSum pr e y` is the sum of the `z_x ^ p ^ e` over the `x = (τ, i)` with partner
`(pr e τ, i) = y`, converges, as the term `e` has order at least `p ^ e`. -/
lemma summable_smul_partnerPowerSum (y : Φ × c) :
    Summable fun e : S ↦ l e 0 • partnerPowerSum (p := p) pr e y := by
  refine summable_of_finite_order_le fun n ↦ ?_
  refine ((Set.finite_Iic n).preimage Subtype.val_injective.injOn).subset fun e he ↦ ?_
  have h_le : ((p ^ (e : ℕ) : ℕ) : ℕ∞) ≤ n :=
    ((le_order_partnerPowerSum e y).trans le_order_smul).trans he
  exact (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le.trans (Nat.cast_le.1 h_le)

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. If `0 ∉ S`, then
modulo `p` only the linear factors in the terms `j = 0` count in the derivatives:
`∂Ξ / ∂z_y ≡ ∑_{e ∈ S} λ_{e 0} * partnerPowerSum pr e y`. -/
lemma dvd_pderiv_couplingSum_sub (hS : 0 ∉ S) (y : Φ × c) :
    C (p : valRingCp p) ∣
      pderiv y (couplingSum S pr l) - ∑' e : S, l e 0 • partnerPowerSum pr e y := by
  have h_deriv :
      HasSum (fun x : S × ℕ ↦ pderiv y (l x.1 x.2 • coupling pr x.1 ^ p ^ x.2))
        (pderiv y (couplingSum S pr l)) :=
    hasSum_couplingSum.map (pderiv y).toLinearMap (continuous_pderiv y)
  -- The second sum, written over the pairs `(e, j)` with zero terms for `j > 0`.
  have h_main : HasSum (fun x : S × ℕ ↦ if x.2 = 0 then l x.1 0 • partnerPowerSum pr x.1 y else 0)
      (∑' e : S, l e 0 • partnerPowerSum (p := p) pr e y) := by
    refine ((Prod.mk_left_injective 0).hasSum_iff fun x hx ↦ ite_eq_right fun hj : x.2 = 0 ↦
      hx ⟨x.1, Prod.ext rfl hj.symm⟩).1 ?_
    simpa [Function.comp_def] using (summable_smul_partnerPowerSum y).hasSum
  refine C_dvd_of_hasSum (h_deriv.sub h_main) ?_
  rintro ⟨⟨e, he⟩, _ | j⟩
  · simpa [← smul_sub, smul_eq_C_mul, ← mul_sub] using
      (dvd_pderiv_coupling_sub (ne_of_mem_of_not_mem he hS) y).mul_left (C (l e 0))
  · rw [ite_eq_right j.succ_ne_zero, sub_zero, Derivation.map_smul, smul_eq_C_mul]
    exact (dvd_pderiv_pow_pow _ j.succ_ne_zero y).mul_left _

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. If `0 ∉ S`, then
modulo the maximal ideal of `valRingCp p` the coefficients of `∂Ξ / ∂z_y` are those of
`∑_{e ∈ S} λ_{e 0} * partnerPowerSum pr e y`. -/
lemma residue_coeff_pderiv_couplingSum_eq (hS : 0 ∉ S) (y : Φ × c) (d : Φ × c →₀ ℕ) :
    residue (valRingCp p) (coeff d (pderiv y (couplingSum S pr l))) =
      residue (valRingCp p) (∑' e : S, l e 0 * coeff d (partnerPowerSum pr e y)) := by
  have h_sum : ∑' e : S, l e 0 * coeff d (partnerPowerSum pr e y) =
      coeff d (∑' e : S, l e 0 • partnerPowerSum pr e y) :=
    (hasSum_iff_hasSum_coeff.1 (summable_smul_partnerPowerSum y).hasSum d).tsum_eq
  obtain ⟨a, ha⟩ : (p : valRingCp p) ∣ coeff d (pderiv y (couplingSum S pr l)) -
      ∑' e : S, l e 0 * coeff d (partnerPowerSum pr e y) := by
    simpa only [h_sum, ← map_sub] using
      C_dvd_iff_forall_dvd_coeff.1 (dvd_pderiv_couplingSum_sub hS y) d
  rw [sub_eq_iff_eq_add'] at ha
  simp only [ha, map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. Let `0 ∉ S` and
`e ∈ S`, and let `y = (pr e τ, i)` be the partner of `x = (τ, i)` for `e`. Modulo the maximal ideal
of `valRingCp p`, the coefficient of the one monomial `z_x ^ p ^ e` in `∂Ξ / ∂z_y` is `λ_{e 0}`. -/
lemma residue_coeff_pderiv_couplingSum (hS : 0 ∉ S) {e : ℕ} (he : e ∈ S) (x : Φ × c) :
    residue (valRingCp p)
        (coeff (.single x (p ^ e)) (pderiv (pr e x.1, x.2) (couplingSum S pr l))) =
      residue (valRingCp p) (l e 0) := by
  have h_zero (e' : S) (h_ne : e' ≠ ⟨e, he⟩) :
      coeff (.single x (p ^ e)) (partnerPowerSum (p := p) pr e' (pr e x.1, x.2)) = 0 := by
    by_contra h_ne_zero
    obtain ⟨x', -, h_eq⟩ := exists_single_of_coeff_partnerPowerSum_ne_zero h_ne_zero
    have h_pow : p ^ (e' : ℕ) = p ^ e := by
      rw [← Finsupp.degree_single x (p ^ e), h_eq, Finsupp.degree_single]
    exact h_ne (Subtype.ext (Nat.pow_right_injective (Fact.out : p.Prime).two_le h_pow))
  rw [residue_coeff_pderiv_couplingSum_eq hS, tsum_eq_single ⟨e, he⟩ fun e' h_ne ↦ by
    simp [h_zero e' h_ne], coeff_partnerPowerSum_self, mul_one]

/-- Let `Ξ = couplingSum S pr l` be the series `∑_{e ∈ S} ∑_j λ_{e j} Γ_e ^ p ^ j`. If `0 ∉ S`, then
modulo the maximal ideal of `𝒪 = valRingCp p` the series `∂Ξ / ∂z_y` has only monomials
`z_x ^ p ^ e` with `e ∈ S` and `y = (pr e τ, i)` the partner of `x = (τ, i)` for `e`. -/
lemma exists_eq_single_of_residue_coeff_pderiv_ne_zero (hS : 0 ∉ S) {y : Φ × c} {d : Φ × c →₀ ℕ}
    (h_ne : residue (valRingCp p) (coeff d (pderiv y (couplingSum S pr l))) ≠ 0) :
    ∃ e ∈ S, ∃ x : Φ × c, (pr e x.1, x.2) = y ∧ d = .single x (p ^ e) := by
  by_contra h_none
  have h_zero (e : S) : coeff d (partnerPowerSum (p := p) pr e y) = 0 :=
    by_contra fun he ↦ h_none ⟨e, e.property, exists_single_of_coeff_partnerPowerSum_ne_zero he⟩
  simp [residue_coeff_pderiv_couplingSum_eq hS, h_zero] at h_ne

end New
