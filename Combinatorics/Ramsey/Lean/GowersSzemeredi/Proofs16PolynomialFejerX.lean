import GowersSzemeredi.Proofs16PolynomialFejerS
import GowersSzemeredi.Proofs18CoverFejerHeadlineX

/-! **Theorem 16.2 and Corollary 16.11 with polynomial controls at the classes of
constant `5/2` and the polynomial base budget** (Notes L.16n).

The X instances of `Proofs16PolynomialFejerS` (generated), from the profiles
with polynomial family constants:
* `theorem_16_2_polynomial_fejerX_of_profiles`: graph count
  `max(1, (4V/(γθρ))^uDegX k)` with `V = 2^(2^(4k+13))` and `log₂ uDegX k = tDegX k`.
  This is the exact table up to `k = 12` and `5·2^(k−1) + 3(k+4)² + 2` beyond,
  against `4·2^k + 3(k+4)² + 32` at the S classes and `68·2^k` printed. It
  implies the printed Theorem 16.2 for `k ≥ 1` (`theorem162At_of_polynomial_fejerX`).
* `corollary_16_11_polynomial_fejerX_of_profiles` with `expDegX_tight_le`:
  `e⁻¹ ≤ (2/α)^(2^(3·tDegX k + 6k + 38))`, that is `7.5·2^k + O(k²)`, against
  `32·2^k` at the S classes and `236·2^k` printed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem uDegX_le_uDeg68 {k : Nat} (hk : 1 ≤ k) : uDegX k ≤ uDeg68 k := by
  unfold uDegX uDeg68
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rcases Nat.lt_or_ge k 13 with h | h
  · interval_cases k <;> decide
  · rw [tDegX_eq_of_ge h]
    have h1 := sq_le_two_pow_four k (by omega)
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [show k = (k - 1) + 1 by omega, pow_succ]; simp; ring
    have h3 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    omega

/-- The exponent degree at `(tDegX, tightMu0X)`. -/
theorem expDegX_tight_le (k : Nat) :
    GenParamsX.expDegX k (tightMu0X k) (genMuKX k) + 3 ≤ 3 * tDegX k + 6 * k + 38 := by
  unfold GenParamsX.expDegX GenParamsX.rhoDegX tightMu0X tightMuW genMuKX pDeg
  have := seventeen_le_tDegX k
  have hkt : k ≤ tDegX k := by
    rcases Nat.lt_or_ge k 13 with h | h
    · interval_cases k <;> decide
    · rw [tDegX_eq_of_ge h]
      have : k ≤ (k + 4) ^ 2 := by nlinarith
      omega
  simp only [max_def]
  split_ifs <;> omega

theorem tightMuW_le_tightMuV (k : Nat) : tightMuW k ≤ tightMuV k := by
  unfold tightMuW tightMuV
  have h := Nat.lt_two_pow_self (n := k)
  have h16 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
  omega

/-- **Theorem 16.2 with polynomial controls in every dimension**, from the
recurrence profiles. -/
theorem theorem_16_2_polynomial_fejerX_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegX k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegX k)) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  exact (polyCoverAt_classX Kc pc hK1 hp hlem hk).uniform_mono (one_le_classV Kc pc k)
    (classV_le_poly Kc pc hconst k) le_rfl

/-- **Corollary 16.11 with polynomial exponents in dimension `k + 1`**, from
the recurrence profiles. -/
theorem corollary_16_11_polynomial_fejerX_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧
        e⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsX.expDegX k (tightMu0X k) (genMuKX k) + 3)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  have hX := two_div_ge_two ha ha2
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  let P : GenParamsX := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0X k⟩
  have H : P.CHyp (tightMuW k) (genMuKX k) := tightHyp_of_profiles_fejerX Kc pc hK hp hconst hk
  have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
      PolyCoverAt l (uCount P.V (uDegX l)) (uExp P.V (uDegX l)) := by
    intro l hl1 hlk
    have hcl := polyCoverAt_classX Kc pc hK1 hp hlem hl1
    exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
  have hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ uCount P.V (uDegX l) g t s :=
    fun l g t s _ _ => one_le_uCount P.V (uDegX l) g t s
  have hretile : ∀ q, Section16RetiledLinearityBound P.k q (familyRecExp P.k P.p q)
      (familyRecThr P.k P.K P.p q) :=
    fun q => ((hrec k (by omega)).retiled_family
      (fun q => familyRecThr_pos (by have := hK k; omega) q) q).single
  -- the two exponents
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leX H ha ha2
  obtain ⟨-, -, hei, -, -, -⟩ := P.yIn_boundsX ha ha2 H.hV H.hVμ H.hμ0
  set D := singlePieceGlobalDensityF (fun l => uCount P.V (uDegX l)) alpha (alpha / 2) P.k with hDdef
  have hD0 : 0 < D := singlePieceGlobalDensityF_pos ha (by linarith) hQb
  have heta0 : 0 < P.eta alpha := by
    exact singlePieceEtaF_pos ha (by linarith) hQb
  have hetaD : P.eta alpha ≤ D := singlePieceEtaF_le_density ha (by linarith) hD0.le
  have hDi : D⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsX.expDegX k (tightMu0X k) (genMuKX k) + 3)) := by
    refine (inv_anti₀ heta0 hetaD).trans (pw_mono hX hei ?_)
    show GenParamsX.rhoDegX k (tightMu0X k) + 2 * (tDegX k) + 12 ≤
      GenParamsX.expDegX k (tightMu0X k) (genMuKX k) + 3
    unfold GenParamsX.expDegX
    have := le_max_left (GenParamsX.rhoDegX k (tightMu0X k) + 2 * (tDegX k) + 9)
      (max (GenParamsX.rhoDegX k (tightMu0X k) + tDegX k + k + 7) (genMuKX k + 2))
    omega
  refine ⟨min (P.Eloc alpha) D, lt_min hEl0 hD0, ?_, ⌈P.Tloc alpha⌉₊, ?_⟩
  · rcases min_choice (P.Eloc alpha) D with h | h
    · rw [h]; exact hEli
    · rw [h]; exact hDi
  · intro N _ _ hN f hf hnot
    have hT : P.Tloc alpha ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    obtain ⟨hodd, h15, -, m, hscale, hwide⟩ :=
      P.modulus_conditions H.hV H.hK H.hp ha ha2 N hT
    obtain ⟨q, hq, B, mu, -, hmu, hBw, hcount⟩ := single_piece_frequency_box_global_cover_fejer
      (Qb := fun l => uCount P.V (uDegX l)) (Eb := fun l => uExp P.V (uDegX l))
      (by show 1 ≤ k; omega) ha ha2 hcov hQb
      (fun l g t s _ _ => (uExp_pos_le P.V (uDegX l) g t s).1)
      (fun l g t s _ _ => (uExp_pos_le P.V (uDegX l) g t s).2)
      (familyRecExp P.k P.p) (familyRecThr P.k P.K P.p) hretile hodd h15 m hscale f hf hnot
    have hN1 : (1 : Real) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    refine ⟨B, mu, hmu, ?_, ?_⟩
    · calc (N : Real) ^ min (P.Eloc alpha) D ≤ (N : Real) ^ P.Eloc alpha :=
            Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)
        _ ≤ _ := hwide q hq
        _ ≤ B.width := by exact_mod_cast hBw
    · calc min (P.Eloc alpha) D * B.carrier.card ≤ D * B.carrier.card :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
        _ ≤ _ := hcount





/-- **The polynomial form at `uDegX` implies the printed Theorem 16.2.** -/
theorem theorem162At_of_polynomial_fejerX {k : Nat} (hk : 1 ≤ k)
    (h : PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegX k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegX k))) : Theorem162At k :=
  theorem162At_of_polynomial (h.uniform_mono (one_le_pow₀ (by norm_num))
    (pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) (tightMuW_le_tightMuV k)))
    (uDegX_le_uDeg68 hk))

end LeanProofs.GowersSzemeredi
