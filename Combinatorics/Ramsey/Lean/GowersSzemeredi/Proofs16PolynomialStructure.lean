import GowersSzemeredi.Proofs18CoverBudget

/-! **Theorem 16.2 with polynomial controls** (Notes L.15i).

The printed Theorem 16.2 (`Theorem162At`) allows a relation of product
parameter `γ` to be restricted to a set of density `1 − θ` on which it is
multiply linear with graph count `q(r⁻¹ρ, γ, k)^r` at precision `ρ`, where
`r = γ⁻²·s(θ, γ, k)` and `s = (2/(θγ))^(2^(2^(k+6)))`: exponential in a
polynomial of `1/θ`. The class covers built for the induction
(`polyCoverAt_class68`) give much more: a graph count **polynomial** in
`1/(γθρ)`,
`Q(γ, θ, ρ) = max(1, (4V/(γθρ))^(2^(68·2^k)))` with `V = 2^(2^(2^(k+4)+1))`
(`uCount_eq`, `classV_le_tight`), and width exponent `Q⁻¹`, in every
dimension `k ≥ 1`:
* `theorem_16_2_polynomial_of_profiles`, from the recurrence profiles;
* `theorem_16_2_polynomial` (explicit profiles, in
  `Proofs18CoverSharperAllDegrees`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The polynomial graph count, in closed form. -/
theorem uCount_eq_closed (V : Real) (D : Nat) (gamma theta rho : Real) :
    uCount V D gamma theta rho = max 1 ((4 * V / (gamma * theta * rho)) ^ D) := by
  unfold uCount uniformBase
  congr 2
  push_cast
  ring

/-- **Theorem 16.2 with polynomial controls in every dimension**, from the
recurrence profiles. -/
theorem theorem_16_2_polynomial_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDeg68 k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDeg68 k)) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  exact (polyCoverAt_class68 Kc pc hK1 hp hlem hk).uniform_mono (one_le_classV Kc pc k)
    (classV_le_tight Kc pc hconst k) le_rfl

/-- **The polynomial form implies the printed Theorem 16.2** in dimension `k`. -/
theorem theorem162At_of_polynomial {k : Nat}
    (h : PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDeg68 k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDeg68 k))) : Theorem162At k := by
  set V : Real := 2 ^ (2 ^ tightMuV k) with hVdef
  have hV1 : (1 : Real) ≤ V := one_le_pow₀ (by norm_num)
  have hbase : ∀ gamma theta rho : Real,
      uniformBase V 1 theta gamma rho = 2 * V * (2 / (gamma * theta * rho)) := by
    intro gamma theta rho; unfold uniformBase; push_cast; ring
  have hW0' : 2 * V ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1) := by
    have h1 : 2 ^ tightMuV k + 1 ≤ 2 ^ (2 ^ (k + 6)) - 1 := by
      have h2 : tightMuV k + 1 ≤ 2 ^ (k + 6) - 1 := by
        unfold tightMuV
        have h4 : 2 ^ (k + 6) = 4 * 2 ^ (k + 4) := by rw [show k + 6 = (k + 4) + 2 by ring, pow_add]; ring
        have := Nat.one_le_two_pow (n := k + 4)
        omega
      have h3 : 2 ^ (tightMuV k + 1) ≤ 2 ^ (2 ^ (k + 6) - 1) := Nat.pow_le_pow_right (by norm_num) h2
      have h5 : 2 ^ (2 ^ (k + 6) - 1) * 2 = 2 ^ (2 ^ (k + 6)) := by
        rw [← pow_succ]; congr 1; have := Nat.one_le_two_pow (n := k + 6); omega
      have h6 : 2 ^ (tightMuV k + 1) = 2 * 2 ^ tightMuV k := by rw [pow_succ]; ring
      have h7 := Nat.one_le_two_pow (n := tightMuV k)
      omega
    have h8 : (2 : Real) * V = 2 ^ (2 ^ tightMuV k + 1) := by rw [hVdef, pow_succ]; ring
    rw [h8]
    exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) h1
  have hD : uDeg68 k ≤ (2 : Nat) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := by
    unfold uDeg68
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h1 : 68 * 2 ^ k ≤ 2 ^ (k + 7) := by
      have : 2 ^ (k + 7) = 128 * 2 ^ k := by rw [pow_add]; ring
      omega
    have h2 : k + 7 ≤ 2 ^ (k + 6) := by
      have := Nat.lt_two_pow_self (n := k + 6); omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
  have hge : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 → (1 : Real) ≤ (2 * V * (2 / (gamma * theta * rho))) ^ uDeg68 k := by
    intro gamma theta rho hg hg1 ht ht1 hr hr1
    have hp : gamma * theta * rho ≤ 1 := by
      have := mul_le_one₀ (mul_le_one₀ hg1 ht.le ht1) hr.le hr1; linarith
    have h2 : (1 : Real) ≤ 2 / (gamma * theta * rho) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    exact one_le_pow₀ (by nlinarith)
  refine theorem162At_of_polyCover_tower h (W0 := 2 * V) (by linarith) hW0' hD ?_ ?_
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    unfold uCount
    rw [hbase]
    exact max_le (hge gamma theta rho hg hg1 ht ht1 hr hr1) le_rfl
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    unfold uExp uCount
    rw [hbase]
    exact inv_anti₀ (lt_of_lt_of_le one_pos (le_max_left _ _))
      (max_le (hge gamma theta rho hg hg1 ht ht1 hr hr1) le_rfl)

end LeanProofs.GowersSzemeredi
