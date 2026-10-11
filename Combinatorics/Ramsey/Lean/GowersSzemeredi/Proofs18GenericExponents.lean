import GowersSzemeredi.Proofs18GenericDensity

/-! The width exponents of the single-piece step in any dimension are
polynomially small in `X = 2/α` (Notes L.7a, F3c).

For the standard parameters `GenParams.std V D k K p μ₀`, with `V ≤ 2^(2^μV)`,
`p ≤ 2^(2^μK)`, `D ≤ 2^μD` and `ρ = rhoDeg k μD μ₀`:
* `uCount_scale_le`: `uCount V D γ θ s ≤ X^(2^(max μ₀ c + 1 + μD))` when
  `s⁻¹ ≤ X^(2^c)` and `γ⁻¹, θ⁻¹ ≤ X^(2^fixDeg)`;
* `nestC_genC_anti`: the nested densities decrease, so every level of the
  nest sits above `ρ₁`;
* `Eloc_inv_le`: the localization exponent satisfies
  `Eloc⁻¹ ≤ X^(2^(expDeg + 3))`, with
  `expDeg = max (ρ + 2μD + 9) (max (ρ + μD + k + 7) (μK + 2))`.

The dominant factor is the retiling exponent `familyRecExp k p QM`, whose
inverse is `QM^(2^(k+2))`: it adds `k + 2` to the log-degree of `QM`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The uniform count at any scale -/

theorem uCount_scale_le {X V γ θ s : Real} {D μV μD μ0 c : Nat} (hX : 2 ≤ X) (hV : 1 ≤ V)
    (hVμ : V ≤ 2 ^ (2 ^ μV)) {k : Nat} (hμ0 : max μV (fixDeg k) + 2 ≤ μ0)
    (hg : 0 < γ) (hg1 : γ ≤ 1) (hgi : γ⁻¹ ≤ X ^ (2 ^ fixDeg k))
    (ht : 0 < θ) (ht1 : θ ≤ 1) (hti : θ⁻¹ ≤ X ^ (2 ^ fixDeg k))
    (hs : 0 < s) (hs1 : s ≤ 1) (hsi : s⁻¹ ≤ X ^ (2 ^ c)) (hD : D ≤ 2 ^ μD) :
    uCount V D γ θ s ≤ X ^ (2 ^ (max μ0 c + 1 + μD)) := by
  rw [uCount_eq hV D hg hg1 ht ht1 hs hs1]
  have hval : uniformBase V 1 θ γ s = 4 * V * γ⁻¹ * θ⁻¹ * s⁻¹ := by
    unfold uniformBase; field_simp; ring
  rw [hval]
  set m := max μV (fixDeg k)
  have h7 : 7 ≤ m := le_trans (Nat.le_add_left 7 _) (le_max_right μV (fixDeg k))
  have h4 : (4 : Real) ≤ X ^ (2 ^ m) := pw_const hX (by
    have : 2 ≤ 2 ^ m := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc (4 : Real) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 ^ m) := pow_le_pow_right₀ (by norm_num) this)
  have hV' : V ≤ X ^ (2 ^ m) := pw_mono hX (pw_const hX hVμ) (le_max_left _ _)
  have hg' : γ⁻¹ ≤ X ^ (2 ^ m) := pw_mono hX hgi (le_max_right _ _)
  have ht' : θ⁻¹ ≤ X ^ (2 ^ m) := pw_mono hX hti (le_max_right _ _)
  have h1 := pw_mul hX (by norm_num) (by linarith) h4 hV'
  have h2 := pw_mul hX (inv_pos.mpr hg).le (inv_pos.mpr ht).le hg' ht'
  have h3 := pw_mul hX (by positivity) (by positivity) h1 h2
  have hc0 : 4 * V * γ⁻¹ * θ⁻¹ ≤ X ^ (2 ^ μ0) := by
    rw [show 4 * V * γ⁻¹ * θ⁻¹ = 4 * V * (γ⁻¹ * θ⁻¹) by ring]
    exact pw_mono hX h3 (by omega)
  have h5 := pw_mul' hX (by positivity) (inv_pos.mpr hs).le hc0 hsi
  exact pw_pow hX (by positivity) h5 hD

/-! ### The nest decreases -/

theorem genC_le_self {X : Real} (hX : 1 ≤ X) {a b : Nat} (hb : 1 ≤ b) (c : Real → Real) (k : Nat)
    {t : Real} (ht : 0 < t) (ht1 : t ≤ 1) : genC X a b c k t ≤ t := by
  rw [genC_eq ht ht1]
  have hXa : 1 ≤ X ^ a := one_le_pow₀ hX
  calc (X ^ a)⁻¹ * t ^ b ≤ 1 * t ^ 1 :=
        mul_le_mul (inv_le_one_of_one_le₀ hXa) (pow_le_pow_of_le_one ht.le ht1 hb)
          (pow_nonneg ht.le _) zero_le_one
    _ = t := by ring

theorem nestC_genC_anti {X : Real} (hX : 1 ≤ X) {a b : Nat} (hb : 1 ≤ b) (c : Real → Real)
    (k : Nat) {t : Real} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∀ i r, i ≤ r → nestC (fun _ => genC X a b c k) r t ≤ nestC (fun _ => genC X a b c k) i t := by
  intro i r hir
  induction hir with
  | refl => exact le_rfl
  | step _ ih =>
    refine le_trans ?_ ih
    obtain ⟨h0, h1⟩ := nestC_pos_le (c := fun _ => genC X a b c k)
      (fun _ => genC_pos_le hX a b c k) _ t ht ht1
    exact genC_le_self hX hb c k h0 h1

theorem genNestExp_inv_le {E : Real → Real} {k : Nat} {C : Real → Real} {t M : Real}
    (hM : 1 ≤ M) (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1)
    (hC : ∀ u, 0 < u → u ≤ 1 → 0 < C u ∧ C u ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∀ r, (∀ i, i < r → (lwE E k (nestC (fun _ => C) i t))⁻¹ ≤ M) →
      (genNestExp E k C r t)⁻¹ ≤ M ^ r := by
  intro r
  induction r with
  | zero => intro _; simp [genNestExp]
  | succ r ih =>
    intro hfac
    obtain ⟨n0, -, -, -⟩ := genNest_facts hE k hC r t ht ht1
    obtain ⟨c0, c1⟩ := nestC_pos_le (c := fun _ => C) (fun _ => hC) r t ht ht1
    obtain ⟨l0, -⟩ := lwE_pos_le hE k c0 c1
    show (genNestExp E k C r t * lwE E k (nestC (fun _ => C) r t))⁻¹ ≤ M ^ (r + 1)
    rw [mul_inv, pow_succ]
    exact mul_le_mul (ih fun i hi => hfac i (by omega)) (hfac r (by omega))
      (inv_pos.mpr l0).le (pow_nonneg (le_trans zero_le_one hM) _)

namespace GenParams

variable {alpha : Real}

/-- The log-degree of the width exponents. -/
def expDeg (k μD μ0 μK : Nat) : Nat :=
  max (rhoDeg k μD μ0 + 2 * μD + 9) (max (rhoDeg k μD μ0 + μD + k + 7) (μK + 2))

/-- `c(θ_S)` for the base density: the first half of `dens_step`. -/
theorem cS_step {X : Real} (hX : 2 ≤ X) {c : Real → Real} {a0 b0 : Nat}
    (hc : RecipPowerLB X c a0 b0) {θ : Real} {m μa μb : Nat} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθi : θ⁻¹ ≤ X ^ (2 ^ m)) (ha0 : a0 ≤ 2 ^ μa) (hb0 : b0 ≤ 2 ^ μb) (hμa : μa ≤ m) :
    0 < c θ ∧ c θ ≤ 1 ∧ (c θ)⁻¹ ≤ X ^ (2 ^ (m + μb + 1)) := by
  have hX1 : (1 : Real) ≤ X := by linarith
  obtain ⟨hc0, hc1, hci⟩ := hc.apply_le hX1 hθ0 hθ1 hθi
  refine ⟨hc0, hc1, hci.trans (pow_le_pow_right₀ hX1 ?_)⟩
  have h1 : 2 ^ m * b0 ≤ 2 ^ m * 2 ^ μb := Nat.mul_le_mul_left _ hb0
  have h2 : 2 ^ m * 2 ^ μb = 2 ^ (m + μb) := by rw [← pow_add]
  have h3 : 2 ^ μa ≤ 2 ^ (m + μb) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (m + μb + 1) = 2 * 2 ^ (m + μb) := by rw [pow_succ]; ring
  omega

/-- `(α/2)⁻¹ = X`. -/
theorem half_inv_le (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (alpha / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  rw [inv_div]; exact pw_X (two_div_ge_two ha ha2) _

/-- **One level of the nested width exponent.** -/
theorem lw_level_inv_le {V : Real} {D k μV μD μ0 ρ : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) (hD : D ≤ 2 ^ μD)
    {u : Real} (hu0 : 0 < u) (hu1 : u ≤ 1) (hui : u⁻¹ ≤ (2 / alpha) ^ (2 ^ ρ))
    (hρ : fixDeg k + 1 ≤ ρ) (hρ0 : μ0 ≤ ρ) :
    (lwE (uExp V D (alpha / 2) (globalBudget alpha (alpha / 2) k)) k u)⁻¹ ≤
      (2 / alpha) ^ (2 ^ (ρ + μD + 3)) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds k ha ha2
  have hk1 : k + 1 ≤ ρ := by
    have : k + 1 ≤ 2 ^ (k + 5) := by have := Nat.lt_two_pow_self (n := k + 5); omega
    unfold fixDeg at hρ; omega
  have hkρ : k + 1 ≤ 2 ^ ρ := hk1.trans Nat.lt_two_pow_self.le
  have hs0 : 0 < u / 2 ^ (k + 1) := by positivity
  have hs1 : u / 2 ^ (k + 1) ≤ 1 := (div_le_self hu0.le (one_le_pow₀ (by norm_num))).trans hu1
  have hsi : (u / 2 ^ (k + 1))⁻¹ ≤ (2 / alpha) ^ (2 ^ (ρ + 1)) := by
    rw [inv_div, div_eq_mul_inv]
    have h2k : (2 : Real) ^ (k + 1) ≤ (2 / alpha) ^ (2 ^ ρ) :=
      (pow_le_pow_left₀ (by norm_num) hX _).trans (pw_natpow hX hkρ)
    exact pw_mul hX (by positivity) (inv_pos.mpr hu0).le h2k hui
  have hcount := uCount_scale_le (c := ρ + 1) hX hV hVμ hμ0 (half_pos ha) (by linarith)
    (half_inv_le k ha ha2) hB0 hB1 hBi hs0 hs1 hsi hD
  have hmax : max μ0 (ρ + 1) = ρ + 1 := max_eq_right (by omega)
  rw [hmax] at hcount
  have h4k : (4 : Real) ^ k ≤ (2 / alpha) ^ (2 ^ (ρ + 1 + 1 + μD)) := by
    have h4 : (4 : Real) ≤ (2 / alpha) ^ 2 := by nlinarith
    refine (pow_le_pow_left₀ (by norm_num) h4 k).trans ?_
    rw [← pow_mul]
    refine pw_natpow hX ?_
    have h1 : 2 * k ≤ 2 ^ (k + 1) := by
      have := Nat.lt_two_pow_self (n := k); rw [pow_succ]; omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  show ((uCount V D (alpha / 2) (globalBudget alpha (alpha / 2) k) (u / 2 ^ (k + 1)))⁻¹ / 4 ^ k)⁻¹ ≤ _
  rw [inv_div, div_inv_eq_mul]
  have := pw_mul hX (by positivity) (le_trans zero_le_one (one_le_uCount _ _ _ _ _)) h4k hcount
  exact pw_mono hX this (by omega)

/-- **The nested width exponent.** -/
theorem nestExp_inv_le {V : Real} {D k K p μV μD μ0 : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV)) (hμ0 : max μV (fixDeg k) + 2 ≤ μ0)
    (hD : D ≤ 2 ^ μD) (hkD : k + 1 ≤ D) (hk0 : k ≤ 2 ^ μ0) :
    ((std V D k K p μ0).NestExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + μD + 3 + k)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hρ1 : μD + μ0 + 3 ≤ rhoDeg k μD μ0 := by
    unfold rhoDeg; have := le_max_left (μD + μ0 + 2) (fixDeg k); omega
  have hρ2 : fixDeg k + 1 ≤ rhoDeg k μD μ0 := by
    unfold rhoDeg; have := le_max_right (μD + μ0 + 2) (fixDeg k); omega
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hC : ∀ u, 0 < u → u ≤ 1 →
      0 < (std V D k K p μ0).C alpha u ∧ (std V D k K p μ0).C alpha u ≤ 1 :=
    genC_pos_le hX1 _ _ _ _
  have hEw : ∀ s, 0 < s → s ≤ 1 →
      0 < (std V D k K p μ0).Ew alpha s ∧ (std V D k K p μ0).Ew alpha s ≤ 1 :=
    fun s _ _ => uExp_pos_le _ _ _ _ s
  obtain ⟨hr0, -⟩ : 0 < (std V D k K p μ0).Rho1 alpha ∧ (std V D k K p μ0).Rho1 alpha ≤ 1 :=
    nestC_pos_le (c := fun _ => (std V D k K p μ0).C alpha) (fun _ => hC) _ _ ht0 ht1
  have hri := rho1_inv_le (V := V) (K := K) (p := p) ha ha2 hD hkD hk0
  have hb1 : 1 ≤ (std V D k K p μ0).b := by show 1 ≤ D + 1 + k; omega
  have hlev : ∀ i, i < 2 ^ k - 1 →
      (lwE ((std V D k K p μ0).Ew alpha) k
        (nestC (fun _ => (std V D k K p μ0).C alpha) i ((std V D k K p μ0).T2 alpha)))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + μD + 3)) := by
    intro i hi
    obtain ⟨u0, u1⟩ := nestC_pos_le (c := fun _ => (std V D k K p μ0).C alpha) (fun _ => hC) i _
      ht0 ht1
    have hu := nestC_genC_anti (a := (std V D k K p μ0).a) hX1 hb1 ((std V D k K p μ0).baseC alpha) k
      ht0 ht1 i _ hi.le
    have hui := (inv_anti₀ hr0 hu).trans hri
    exact lw_level_inv_le ha ha2 hV hVμ hμ0 hD u0 u1 hui hρ2 (by omega)
  have h := genNestExp_inv_le (one_le_pw hX _) hEw hC ht0 ht1 (2 ^ k - 1) hlev
  exact h.trans (pw_pow hX (by positivity) le_rfl (Nat.sub_le _ _))

/-- `⌊Q⌋ + 1 ≤ X^(2^(m+1))` for `1 ≤ Q ≤ X^(2^m)`. -/
theorem floor_succ_le_pw {X Q : Real} {m : Nat} (hX : 2 ≤ X) (hQ1 : 1 ≤ Q) (hQ : Q ≤ X ^ (2 ^ m)) :
    ((⌊Q⌋₊ : Nat) : Real) + 1 ≤ X ^ (2 ^ (m + 1)) := by
  have hfl : ((⌊Q⌋₊ : Nat) : Real) ≤ Q := Nat.floor_le (le_trans zero_le_one hQ1)
  have h2 : (2 : Real) ≤ X ^ (2 ^ m) := hX.trans (pw_X hX _)
  have h3 := pw_mul hX (by norm_num) (le_trans zero_le_one hQ1) h2 hQ
  have h4 : ((⌊Q⌋₊ : Nat) : Real) + 1 ≤ 2 * Q := by linarith
  exact h4.trans h3

/-- `(familyRecExp k p q / 2)⁻¹ = 4 p (q+1)^(2·2^(k+1))`. -/
theorem half_familyRecExp_inv (k p q : Nat) :
    (familyRecExp k p q / 2)⁻¹ = 4 * ((p : Real) * ((q : Real) + 1) ^ (2 * 2 ^ (k + 1))) := by
  unfold familyRecExp
  rw [inv_div, div_inv_eq_mul]
  push_cast
  ring

/-- **`Em`, `QM` and `Bexp`.** -/
theorem spectrum_exps_inv_le {V : Real} {D k K p μV μD μ0 μK : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) (hD : D ≤ 2 ^ μD) (hkD : k + 1 ≤ D) (hk0 : k ≤ 2 ^ μ0)
    (hpμ : p ≤ 2 ^ (2 ^ μK)) :
    ((std V D k K p μ0).Em alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + μD + 2)) ∧
      ((std V D k K p μ0).QM alpha : Real) + 1 ≤ (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + μD + 3)) ∧
      ((std V D k K p μ0).Bexp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ expDeg k μD μ0 μK) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  have hρ1 : μD + μ0 + 3 ≤ rhoDeg k μD μ0 := by
    unfold rhoDeg; have := le_max_left (μD + μ0 + 2) (fixDeg k); omega
  have hM2 : rhoDeg k μD μ0 + μD + k + 7 ≤ expDeg k μD μ0 μK := by
    unfold expDeg; exact (le_max_left _ _).trans (le_max_right _ _)
  have hM3 : μK + 2 ≤ expDeg k μD μ0 μK := by
    unfold expDeg; exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds k ha ha2
  obtain ⟨hd0, hd1, hdi⟩ := delta_gen_bounds k ha ha2
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hC : ∀ u, 0 < u → u ≤ 1 →
      0 < (std V D k K p μ0).C alpha u ∧ (std V D k K p μ0).C alpha u ≤ 1 :=
    genC_pos_le hX1 _ _ _ _
  obtain ⟨hr0, hr1⟩ : 0 < (std V D k K p μ0).Rho1 alpha ∧ (std V D k K p μ0).Rho1 alpha ≤ 1 :=
    nestC_pos_le (c := fun _ => (std V D k K p μ0).C alpha) (fun _ => hC) _ _ ht0 ht1
  have hri : ((std V D k K p μ0).Rho1 alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ rhoDeg k μD μ0) :=
    rho1_inv_le ha ha2 hD hkD hk0
  have hq0 : 0 < (std V D k K p μ0).Rho1 alpha / 2 / 2 := by linarith
  have hq1 : (std V D k K p μ0).Rho1 alpha / 2 / 2 ≤ 1 := by linarith
  have hqi : ((std V D k K p μ0).Rho1 alpha / 2 / 2)⁻¹ ≤
      (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + 1)) := by
    rw [show ((std V D k K p μ0).Rho1 alpha / 2 / 2)⁻¹ = 4 * ((std V D k K p μ0).Rho1 alpha)⁻¹ by
      field_simp; ring]
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ rhoDeg k μD μ0) := pw_const hX (by
      have : 2 ≤ 2 ^ rhoDeg k μD μ0 := le_trans (by norm_num : 2 ≤ 2 ^ 1)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
      calc (4 : Real) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ rhoDeg k μD μ0) := pow_le_pow_right₀ (by norm_num) this)
    exact pw_mul hX (by norm_num) (inv_pos.mpr hr0).le h4 hri
  have hQ := uCount_scale_le (c := rhoDeg k μD μ0 + 1) hX hV hVμ hμ0 hd0 hd1 hdi hB0 hB1 hBi
    hq0 hq1 hqi hD
  rw [max_eq_right (show μ0 ≤ rhoDeg k μD μ0 + 1 by omega)] at hQ
  -- the spectrum count `Qmax`
  have hQv : singlePieceGlobalQmax (fun _ => uCount V D) ((std V D k K p μ0).C alpha) alpha
      (alpha / 2) k ≤ (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + 1 + 1 + μD)) := hQ
  have hQv1 : 1 ≤ singlePieceGlobalQmax (fun _ => uCount V D) ((std V D k K p μ0).C alpha) alpha
      (alpha / 2) k := one_le_uCount _ _ _ _ _
  have hQM := floor_succ_le_pw hX hQv1 hQv
  have hQM' : ((std V D k K p μ0).QM alpha : Real) + 1 ≤
      (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + μD + 3)) :=
    hQM.trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
  refine ⟨?_, hQM', ?_⟩
  · show (uCount V D _ _ _)⁻¹⁻¹ ≤ _
    rw [inv_inv]
    exact hQ.trans (pw_natpow hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · show (familyRecExp k p ((std V D k K p μ0).QM alpha) / 2)⁻¹ ≤ _
    rw [half_familyRecExp_inv]
    have hq0' : (0 : Real) ≤ ((std V D k K p μ0).QM alpha : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) ((std V D k K p μ0).QM alpha); linarith
    have hk2 : 2 * 2 ^ (k + 1) ≤ 2 ^ (k + 2) := by rw [pow_succ 2 (k + 1)]; omega
    have hpow := pw_pow hX hq0' hQM' hk2
    have hp' : (p : Real) ≤ (2 / alpha) ^ (2 ^ μK) := pw_const hX (by exact_mod_cast hpμ)
    have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ (μK + 1)) := pw_const hX (by
      have : 2 ≤ 2 ^ (μK + 1) := le_trans (by norm_num : 2 ≤ 2 ^ 1)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
      calc (4 : Real) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ (μK + 1)) := pow_le_pow_right₀ (by norm_num) this)
    have hpq0 : (0 : Real) ≤ (((std V D k K p μ0).QM alpha : Real) + 1) ^ (2 * 2 ^ (k + 1)) :=
      pow_nonneg hq0' _
    have h1 := pw_mul' hX (Nat.cast_nonneg _) hpq0 hp' hpow
    have h2 := pw_mul' hX (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hpq0) h4 h1
    refine pw_mono hX h2 ?_
    have : max μK (rhoDeg k μD μ0 + μD + 3 + (k + 2)) + 1 ≤ expDeg k μD μ0 μK - 1 := by omega
    omega

/-- **The slice exponents `Eth` and `Ec`.** -/
theorem slice_exps_inv_le {V : Real} {D k K p μV μD μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) (hD : D ≤ 2 ^ μD) (hkD : k + 1 ≤ D) (hk0 : k ≤ 2 ^ μ0) :
    ((std V D k K p μ0).Eth alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + 2 * μD + 9)) ∧
      ((std V D k K p μ0).Ec alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + 2 * μD + 9)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  set ρ := rhoDeg k μD μ0 with hρdef
  have hρ1 : μD + μ0 + 3 ≤ ρ := by
    rw [hρdef]; unfold rhoDeg; have := le_max_left (μD + μ0 + 2) (fixDeg k); omega
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds k ha ha2
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hC : ∀ u, 0 < u → u ≤ 1 →
      0 < (std V D k K p μ0).C alpha u ∧ (std V D k K p μ0).C alpha u ≤ 1 :=
    genC_pos_le hX1 _ _ _ _
  obtain ⟨hr0, hr1⟩ : 0 < (std V D k K p μ0).Rho1 alpha ∧ (std V D k K p μ0).Rho1 alpha ≤ 1 :=
    nestC_pos_le (c := fun _ => (std V D k K p μ0).C alpha) (fun _ => hC) _ _ ht0 ht1
  have hri : ((std V D k K p μ0).Rho1 alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ ρ) :=
    rho1_inv_le ha ha2 hD hkD hk0
  obtain ⟨hR0, hR1, hRi⟩ := rho_step hX hr0 hr1 hri (by omega)
  obtain ⟨hS0, hS1, hSi⟩ := thetaS_step hX hR0 hR1 hRi
  have hThS : (std V D k K p μ0).ThS alpha =
      singlePieceTheta (((std V D k K p μ0).Rho1 alpha) / 2 *
        (((std V D k K p μ0).Rho1 alpha) / 2 / 2)) 1 := rfl
  rw [← hThS] at hS0 hS1 hSi
  have hbase := baseC_recipPowerLB (D := D) (K := K) (p := p) ha ha2 hV hVμ hμ0
  have ha0 : D * 2 ^ μ0 + 1 ≤ 2 ^ (μD + μ0 + 1) := by
    have h1 : D * 2 ^ μ0 ≤ 2 ^ μD * 2 ^ μ0 := Nat.mul_le_mul_right _ hD
    have h2 : 2 ^ (μD + μ0 + 1) = 2 * (2 ^ μD * 2 ^ μ0) := by rw [pow_add, pow_add]; ring
    have h3 : 1 ≤ 2 ^ μD * 2 ^ μ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hb0 : D + 1 ≤ 2 ^ (μD + 1) := by
    have : 2 ^ (μD + 1) = 2 * 2 ^ μD := by rw [pow_succ]; ring
    omega
  obtain ⟨hc0, hc1, hci⟩ := cS_step hX hbase hS0 hS1 hSi ha0 hb0 (by omega)
  have hCS : (std V D k K p μ0).CS alpha =
      (std V D k K p μ0).baseC alpha ((std V D k K p μ0).ThS alpha) := rfl
  rw [← hCS] at hc0 hc1 hci
  have hslice : ∀ {s : Real} {m : Nat}, 0 < s → s ≤ 1 → s⁻¹ ≤ (2 / alpha) ^ (2 ^ m) →
      μ0 ≤ m + 1 → (uExp V D (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (m + 1 + 1 + μD)) := by
    intro s m hs0 hs1 hsi hm
    have hs20 : 0 < s / 2 := half_pos hs0
    have hs2i : (s / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := by
      rw [inv_div, div_eq_mul_inv]
      exact pw_mul hX (by norm_num) (inv_pos.mpr hs0).le (hX.trans (pw_X hX _)) hsi
    have h := uCount_scale_le (c := m + 1) hX hV hVμ hμ0 (half_pos ha) (by linarith)
      (half_inv_le k ha ha2) hB0 hB1 hBi hs20 (by linarith) hs2i hD
    rw [max_eq_right hm] at h
    show (uCount V D _ _ _)⁻¹⁻¹ ≤ _
    rw [inv_inv]; exact h
  constructor
  · exact pw_mono hX (hslice hS0 hS1 hSi (by omega)) (by omega)
  · exact pw_mono hX (hslice hc0 hc1 hci (by omega)) (by omega)

/-- **The localization exponent is polynomially small.** -/
theorem Eloc_inv_le {V : Real} {D k K p μV μD μ0 μK : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) (hD : D ≤ 2 ^ μD) (hkD : k + 1 ≤ D) (hk0 : k ≤ 2 ^ μ0)
    (hp : 0 < p) (hpμ : p ≤ 2 ^ (2 ^ μK)) :
    0 < (std V D k K p μ0).Eloc alpha ∧
      ((std V D k K p μ0).Eloc alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (expDeg k μD μ0 μK + 3)) := by
  have hX := two_div_ge_two ha ha2
  set M := expDeg k μD μ0 μK with hMdef
  have hM1 : rhoDeg k μD μ0 + 2 * μD + 9 ≤ M := by rw [hMdef]; unfold expDeg; exact le_max_left _ _
  have hM2 : rhoDeg k μD μ0 + μD + k + 7 ≤ M := by
    rw [hMdef]; unfold expDeg; exact (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨hE0, -, -, -, -, -⟩ := (std V D k K p μ0).Eloc_pos_le hV hp ha ha2
  obtain ⟨-, -, -, -, -, -, -, ⟨hEm0, -⟩, ⟨hEth0, -⟩, ⟨hEc0, -⟩, ⟨hN0, -, -⟩, ⟨hBx0, -⟩,
    -, -, -⟩ := (std V D k K p μ0).ranges hV hp ha ha2
  have hNE := nestExp_inv_le (K := K) (p := p) ha ha2 hV hVμ hμ0 hD hkD hk0
  obtain ⟨hEm, -, hBx⟩ := spectrum_exps_inv_le (K := K) ha ha2 hV hVμ hμ0 hD hkD hk0 hpμ
  obtain ⟨hEth, hEc⟩ := slice_exps_inv_le (K := K) (p := p) ha ha2 hV hVμ hμ0 hD hkD hk0
  refine ⟨hE0, ?_⟩
  have hval : ((std V D k K p μ0).Eloc alpha)⁻¹ =
      32 * (((std V D k K p μ0).NestExp alpha)⁻¹ * ((std V D k K p μ0).Em alpha)⁻¹) *
      (((std V D k K p μ0).Bexp alpha)⁻¹ *
        (((std V D k K p μ0).Eth alpha)⁻¹ * ((std V D k K p μ0).Ec alpha)⁻¹)) := by
    show (((std V D k K p μ0).NestExp alpha * ((std V D k K p μ0).Em alpha / 2)) *
      ((std V D k K p μ0).Bexp alpha * ((std V D k K p μ0).Eth alpha *
        (std V D k K p μ0).Ec alpha) / 2) / 8)⁻¹ = _
    field_simp
    ring
  rw [hval]
  have hNE' := pw_mono hX hNE (show rhoDeg k μD μ0 + μD + 3 + k ≤ M by omega)
  have hEm' := pw_mono hX hEm (show rhoDeg k μD μ0 + μD + 2 ≤ M by omega)
  have hEth' := pw_mono hX hEth hM1
  have hEc' := pw_mono hX hEc hM1
  have h32 : (32 : Real) ≤ (2 / alpha) ^ (2 ^ (M + 1)) := pw_const hX (by
    have : 5 ≤ 2 ^ (M + 1) := by have := Nat.lt_two_pow_self (n := M + 1); omega
    calc (32 : Real) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (2 ^ (M + 1)) := pow_le_pow_right₀ (by norm_num) this)
  have p1 := pw_mul hX (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le hNE' hEm'
  have p2 := pw_mul hX (inv_pos.mpr hEth0).le (inv_pos.mpr hEc0).le hEth' hEc'
  have p3 := pw_mul' hX (inv_pos.mpr hBx0).le (by positivity) hBx p2
  have p4 := pw_mul hX (by norm_num) (by positivity) h32 p1
  have p5 := pw_mul' hX (by positivity) (by positivity) p4 p3
  exact pw_mono hX p5 (by omega)

end GenParams

end LeanProofs.GowersSzemeredi
