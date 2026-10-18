import GowersSzemeredi.Proofs16PolynomialCorollary
import GowersSzemeredi.Proofs18CoverExponentsFejer
import GowersSzemeredi.Proofs18TightClassesFejerSide

/-! **Theorem 16.2 and Corollary 16.11 with polynomial controls at the Fejér
classes** (Notes L.16e).

The Fejér instances of `Proofs16PolynomialStructure` and
`Proofs16PolynomialCorollary` (generated):
* `theorem_16_2_polynomial_fejer_of_profiles`: graph count
  `max(1, (4V/(γθρ))^(2^(23·2^k)))` with `V = 2^(2^(2^(k+4)+1))`, and width
  exponent its inverse, in every dimension `k ≥ 1` (printed route:
  `2^(68·2^k)`). `theorem162At_of_polynomial_fejer`: it implies the printed
  Theorem 16.2.
* `corollary_16_11_polynomial_fejer_of_profiles` and `expDegF_tight_le`:
  Corollary 16.11 with `e⁻¹ ≤ (2/α)^(2^(101·2^k + k + 24))` (printed route:
  `236·2^k + k + 24`; printed statement: `e⁻¹ = exp(poly(1/α))`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem uDeg23_le_uDeg68 (k : Nat) : uDeg23 k ≤ uDeg68 k := by
  unfold uDeg23 uDeg68
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Theorem 16.2 with polynomial controls in every dimension**, from the
recurrence profiles. -/
theorem theorem_16_2_polynomial_fejer_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDeg23 k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDeg23 k)) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  exact (polyCoverAt_class23 Kc pc hK1 hp hlem hk).uniform_mono (one_le_classV Kc pc k)
    (classV_le_tight Kc pc hconst k) le_rfl

/-- The localization parameter is at most the box density. -/
theorem singlePieceEtaF_le_density {Qb : Nat → Real → Real → Real → Real} {alpha : Real}
    {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hD : 0 ≤ singlePieceGlobalDensityF Qb alpha (alpha / 2) k) :
    singlePieceEtaF Qb alpha k ≤ singlePieceGlobalDensityF Qb alpha (alpha / 2) k := by
  exact singlePieceEta_scalar_le hD ha.le ha1

/-- The exponent degree at the tight base budget, in closed form. -/
theorem expDegF_tight_le (k : Nat) :
    GenParamsF.expDegF k (tightMu0 k) (genMuK k) + 3 ≤ 101 * 2 ^ k + k + 24 := by
  unfold GenParamsF.expDegF GenParamsF.rhoDegF tightMu0 tightMuV genMuK fixDeg
  rw [two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 2 ^ k = x at *
  omega

/-- **Corollary 16.11 with polynomial exponents in dimension `k + 1`**, from
the recurrence profiles. -/
theorem corollary_16_11_polynomial_fejer_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧
        e⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsF.expDegF k (tightMu0 k) (genMuK k) + 3)) ∧
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
  let P : GenParamsF := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩
  have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles_fejer Kc pc hK hp hconst hk
  have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
      PolyCoverAt l (uCount P.V (uDeg23 l)) (uExp P.V (uDeg23 l)) := by
    intro l hl1 hlk
    have hcl := polyCoverAt_class23 Kc pc hK1 hp hlem hl1
    exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
  have hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ uCount P.V (uDeg23 l) g t s :=
    fun l g t s _ _ => one_le_uCount P.V (uDeg23 l) g t s
  have hretile : ∀ q, Section16RetiledLinearityBound P.k q (familyRecExp P.k P.p q)
      (familyRecThr P.k P.K P.p q) :=
    fun q => ((hrec k (by omega)).retiled_family
      (fun q => familyRecThr_pos (by have := hK k; omega) q) q).single
  -- the two exponents
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leF H ha ha2
  obtain ⟨-, -, hei, -, -, -⟩ := P.yIn_boundsF ha ha2 H.hV H.hVμ H.hμ0
  set D := singlePieceGlobalDensityF (fun l => uCount P.V (uDeg23 l)) alpha (alpha / 2) P.k with hDdef
  have hD0 : 0 < D := singlePieceGlobalDensityF_pos ha (by linarith) hQb
  have heta0 : 0 < P.eta alpha := by
    show 0 < singlePieceEtaF _ alpha P.k
    unfold singlePieceEtaF; positivity
  have hetaD : P.eta alpha ≤ D := singlePieceEtaF_le_density ha (by linarith) hD0.le
  have hDi : D⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsF.expDegF k (tightMu0 k) (genMuK k) + 3)) := by
    refine (inv_anti₀ heta0 hetaD).trans (pw_mono hX hei ?_)
    show GenParamsF.rhoDegF k (tightMu0 k) + 2 * (23 * 2 ^ k) + 12 ≤
      GenParamsF.expDegF k (tightMu0 k) (genMuK k) + 3
    unfold GenParamsF.expDegF
    have := le_max_left (GenParamsF.rhoDegF k (tightMu0 k) + 2 * (23 * 2 ^ k) + 9)
      (max (GenParamsF.rhoDegF k (tightMu0 k) + 23 * 2 ^ k + k + 7) (genMuK k + 2))
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
      (Qb := fun l => uCount P.V (uDeg23 l)) (Eb := fun l => uExp P.V (uDeg23 l))
      (by show 1 ≤ k; omega) ha ha2 hcov hQb
      (fun l g t s _ _ => (uExp_pos_le P.V (uDeg23 l) g t s).1)
      (fun l g t s _ _ => (uExp_pos_le P.V (uDeg23 l) g t s).2)
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


/-- **The Fejér polynomial form implies the printed Theorem 16.2** in dimension `k`. -/
theorem theorem162At_of_polynomial_fejer {k : Nat}
    (h : PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDeg23 k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDeg23 k))) : Theorem162At k :=
  theorem162At_of_polynomial (h.uniform_mono (one_le_pow₀ (by norm_num)) le_rfl (uDeg23_le_uDeg68 k))

end LeanProofs.GowersSzemeredi
