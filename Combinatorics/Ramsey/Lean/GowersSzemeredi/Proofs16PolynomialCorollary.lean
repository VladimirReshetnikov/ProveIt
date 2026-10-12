import GowersSzemeredi.Proofs16PolynomialStructure

/-! **Corollary 16.11 with polynomial exponents** (Notes L.15j).

The printed Corollary 16.11 (`Corollary1611At`) finds, for a function that is
not uniform of degree `k + 1`, a box of width `N^e` carrying a multilinear
frequency on an `e` fraction, with `e = section16CorollaryExponent α k`: a
tower in `1/α`. The single-piece step with the joint-cover remainder gives
the same conclusion with `e` **polynomial** in `α`:
`e⁻¹ ≤ (2/α)^(2^(expDegC k μ₀ μK + 3))`, where `e` is the smaller of the
localization exponent `Eloc` and the box density
(`corollary_16_11_polynomial_of_profiles`, in dimension `k + 1` for every
`k ≥ 2`, at the tight base budget). The oddness of `N` comes for free. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The localization parameter is at most the box density. -/
theorem singlePieceEtaC_le_density {Qb : Nat → Real → Real → Real → Real} {alpha : Real}
    {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hD : 0 ≤ singlePieceGlobalDensityC Qb alpha (alpha / 2) k) :
    singlePieceEtaC Qb alpha k ≤ singlePieceGlobalDensityC Qb alpha (alpha / 2) k := by
  unfold singlePieceEtaC
  set D := singlePieceGlobalDensityC Qb alpha (alpha / 2) k
  have h1 : (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (by positivity))
  have h1' : (0 : Real) ≤ (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) := by positivity
  have h2 : (1 : Real) ≤ (2 : Real) ^ (k + 1) := one_le_pow₀ (by norm_num)
  have h3 : alpha ^ 2 / 4 ≤ 1 := by nlinarith
  have h4 : D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 ≤ D := by
    have h5 : D / (2 : Real) ^ (k + 1) ≤ D := div_le_self hD h2
    have h6 : 0 ≤ D / (2 : Real) ^ (k + 1) := by positivity
    calc D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 = D / (2 : Real) ^ (k + 1) * (alpha ^ 2 / 4) := by
          ring
      _ ≤ D / (2 : Real) ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left h3 h6
      _ ≤ D := by rw [mul_one]; exact h5
  have h7 : 0 ≤ D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4 := by positivity
  calc (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (D / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)
      ≤ 1 * D := mul_le_mul h1 h4 h7 (by norm_num)
    _ = D := one_mul D

/-- The exponent degree at the tight base budget, in closed form. -/
theorem expDegC_tight_le (k : Nat) :
    GenParamsC.expDegC k (tightMu0 k) (genMuK k) + 3 ≤ 236 * 2 ^ k + k + 24 := by
  unfold GenParamsC.expDegC GenParamsC.rhoDegC tightMu0 tightMuV genMuK fixDeg
  rw [two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 2 ^ k = x at *
  omega

/-- **Corollary 16.11 with polynomial exponents in dimension `k + 1`**, from
the recurrence profiles. -/
theorem corollary_16_11_polynomial_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧
        e⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsC.expDegC k (tightMu0 k) (genMuK k) + 3)) ∧
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
  let P : GenParamsC := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩
  have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles Kc pc hK hp hconst hk
  have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
      PolyCoverAt l (uCount P.V (uDeg68 l)) (uExp P.V (uDeg68 l)) := by
    intro l hl1 hlk
    have hcl := polyCoverAt_class68 Kc pc hK1 hp hlem hl1
    exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
  have hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ uCount P.V (uDeg68 l) g t s :=
    fun l g t s _ _ => one_le_uCount P.V (uDeg68 l) g t s
  have hretile : ∀ q, Section16RetiledLinearityBound P.k q (familyRecExp P.k P.p q)
      (familyRecThr P.k P.K P.p q) :=
    fun q => ((hrec k (by omega)).retiled_family
      (fun q => familyRecThr_pos (by have := hK k; omega) q) q).single
  -- the two exponents
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leC H ha ha2
  obtain ⟨-, -, hei, -, -, -⟩ := P.yIn_boundsC ha ha2 H.hV H.hVμ H.hμ0
  set D := singlePieceGlobalDensityC (fun l => uCount P.V (uDeg68 l)) alpha (alpha / 2) P.k with hDdef
  have hD0 : 0 < D := singlePieceGlobalDensityC_pos ha (by linarith) hQb
  have heta0 : 0 < P.eta alpha := by
    show 0 < singlePieceEtaC _ alpha P.k
    unfold singlePieceEtaC; positivity
  have hetaD : P.eta alpha ≤ D := singlePieceEtaC_le_density ha (by linarith) hD0.le
  have hDi : D⁻¹ ≤ (2 / alpha) ^ (2 ^ (GenParamsC.expDegC k (tightMu0 k) (genMuK k) + 3)) := by
    refine (inv_anti₀ heta0 hetaD).trans (pw_mono hX hei ?_)
    show GenParamsC.rhoDegC k (tightMu0 k) + 2 * (68 * 2 ^ k) + 12 ≤
      GenParamsC.expDegC k (tightMu0 k) (genMuK k) + 3
    unfold GenParamsC.expDegC
    have := le_max_left (GenParamsC.rhoDegC k (tightMu0 k) + 2 * (68 * 2 ^ k) + 9)
      (max (GenParamsC.rhoDegC k (tightMu0 k) + 68 * 2 ^ k + k + 7) (genMuK k + 2))
    omega
  refine ⟨min (P.Eloc alpha) D, lt_min hEl0 hD0, ?_, ⌈P.Tloc alpha⌉₊, ?_⟩
  · rcases min_choice (P.Eloc alpha) D with h | h
    · rw [h]; exact hEli
    · rw [h]; exact hDi
  · intro N _ _ hN f hf hnot
    have hT : P.Tloc alpha ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    obtain ⟨hodd, h15, -, m, hscale, hwide⟩ :=
      P.modulus_conditions H.hV H.hK H.hp ha ha2 N hT
    obtain ⟨q, hq, B, mu, -, hmu, hBw, hcount⟩ := single_piece_frequency_box_global_cover
      (Qb := fun l => uCount P.V (uDeg68 l)) (Eb := fun l => uExp P.V (uDeg68 l))
      (by show 1 ≤ k; omega) ha ha2 hcov hQb
      (fun l g t s _ _ => (uExp_pos_le P.V (uDeg68 l) g t s).1)
      (fun l g t s _ _ => (uExp_pos_le P.V (uDeg68 l) g t s).2)
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

end LeanProofs.GowersSzemeredi
