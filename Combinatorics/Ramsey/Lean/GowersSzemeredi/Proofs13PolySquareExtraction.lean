import GowersSzemeredi.Proofs13PolyRowExponent
import GowersSzemeredi.Proofs13ExplicitGeometricThreshold

/-! The Section 13 square extraction at a polynomial exponent (Notes L.7c, P3b).

`section13_complete_square_extraction_explicit` gives a bilinear square of
side `N^(section13SquareExponent δ)`. Its first factor is the catalogue row
exponent `2^(−13Q(δ))`, doubly exponential in `1/δ`.

Here the row exponent is `polyRowExponent p δ`, which is polynomial in
`1/δ`. The route:
1. Stage 13.4 is the corpus's `lemma_13_4_holds`.
2. Stage 13.5 is `lemma_13_5_poly_with_catalogue`.
3. The integer budgets are the corpus's
   `uniform_rounded_power_budgets_explicit` at the exponents of
   `Proofs13PolyRowExponent`.
4. Stage 13.6 is `lemma_13_6_from_initial_stages_at`.
5. Everything from Stage 13.7 to the square is the corpus's
   `section13_square_extraction_of_scales`, unchanged.

The phase partition enters as the hypothesis
`ProgressionPhasePartition K p`, with `K ≤ 2^p` and `p ≤ 2^(2^64)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section13PolyBudgetThreshold (p : Nat) (delta : Real) (q : Nat) : Real :=
  let theta := section10Lambda (delta ^ 32 / 16)
  let d₀ := section13ThetaOne theta / (64 * Real.pi)
  max (uniformRoundedPowerThreshold (section13Zeta delta / 2) (min 1 (d₀ / 2))
    (section10Zeta (delta ^ 32 / 16)) (polyRowExponent p delta))
    (positivePowerThreshold 4 d₀ (section13ThetaOne theta ^ 2 / (16 * (q : Real))))

theorem stage135UniformExponent_le_one {p q : Nat} (hp : 0 < p) :
    stage135UniformExponent p q ≤ 1 := by
  unfold stage135UniformExponent
  have hc : 1 ≤ 2 * p * (q + 1) ^ 8 := by
    have : 0 < 2 * p * (q + 1) ^ 8 := by positivity
    omega
  have hcR : (1 : Real) ≤ ((2 * p * (q + 1) ^ 8 : Nat) : Real) := by exact_mod_cast hc
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hcR)

/-- The integer budgets of Stage 13.6 at the polynomial exponents, for one
spectrum size `q`. -/
theorem section13_poly_integer_budgets {delta : Real} (hδ : 0 < delta) (hδone : delta ≤ 1)
    {p q : Nat} (hp : 0 < p) (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) (hq : 0 < q) :
    ∀ (N : Nat), section13PolyBudgetThreshold p delta q ≤ N → ∀ alpha : Real,
      delta ≤ alpha → alpha ≤ 1 →
      (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)) → ∀ n L Q : Nat,
      IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
        (64 * Real.pi) * (N : Real) ^
          (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) n →
      (L = n ∨ L + 1 = n) →
      (L : Real) ^ stage135UniformExponent p q / 2 ≤ Q →
      ∃ m : Nat, 0 < m ∧ m * m ≤ N ∧ m + 1 ≤ Q ∧
        section13Zeta alpha / 2 *
          (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) ≤ m ∧
        section13Zeta alpha / 2 * (N : Real) ^ polyRowExponent p alpha ≤ m ∧
        (L : Real) ^ (-stage135UniformExponent p q) ≤
          section10Zeta (alpha ^ 32 / 16) / m := by
  intro N hthreshold
  let theta := section10Lambda (delta ^ 32 / 16)
  let d₀ := section13ThetaOne theta / (64 * Real.pi)
  let d := min 1 (d₀ / 2)
  let u₀ := section13ThetaOne theta ^ 2 / (16 * (q : Real))
  let c₀ := section13Zeta delta / 2
  let e₀ := polyRowExponent p delta
  let z₀ := section10Zeta (delta ^ 32 / 16)
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hθ₁ : 0 < section13ThetaOne theta := by unfold section13ThetaOne; positivity
  have hd₀ : 0 < d₀ := div_pos hθ₁ (mul_pos (by norm_num) Real.pi_pos)
  have hd : 0 < d := lt_min zero_lt_one (div_pos hd₀ (by norm_num))
  have hu₀ : 0 < u₀ := div_pos (pow_pos hθ₁ _) (mul_pos (by norm_num) (by exact_mod_cast hq))
  have hc₀ : 0 < c₀ := by dsimp [c₀, section13Zeta]; positivity
  have he₀ : 0 < e₀ := polyRowExponent_pos hδ hδone hp
  have hz₀ : 0 < z₀ := section10Zeta_pos (by positivity)
  have hround : uniformRoundedPowerThreshold c₀ d z₀ e₀ ≤ (N : Real) :=
    (le_max_left _ _).trans hthreshold
  have hfloor := positivePowerThreshold_spec hd₀ hu₀
    ((le_max_right _ _).trans hthreshold : positivePowerThreshold 4 d₀ u₀ ≤ (N : Real))
  have hNpos : 1 ≤ N := by
    exact_mod_cast (positivePowerThreshold_one_le 1 c₀ e₀).trans ((le_max_left _ _).trans hround)
  intro alpha hδα hαone hqB n L Q hn hL hQlen
  have hα : 0 < alpha := hδ.trans_le hδα
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hNpos
  let u := section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real))
  let e := polyRowExponent p alpha
  let v := stage135UniformExponent p q
  have ht := section13ThetaOne_mono hθ.le (section13_cutoff_mono hδ hδα)
  have hdle : d₀ ≤ section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) :=
    div_le_div_of_nonneg_right ht (by positivity)
  have hule : u₀ ≤ u := div_le_div_of_nonneg_right (pow_le_pow_left₀ hθ₁.le ht 2)
    (by positivity)
  have hfour : 4 ≤ d₀ * (N : Real) ^ u := by
    calc
      _ ≤ d₀ * (N : Real) ^ u₀ := by simpa only [Real.rpow_zero, mul_one] using hfloor
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNreal hule) hd₀.le
  have hPlower : d * (N : Real) ^ u ≤ (L : Real) := by
    have hnupper := hn.2
    have hlower := mul_le_mul_of_nonneg_right hdle (Real.rpow_nonneg (Nat.cast_nonneg N) u)
    have hhalf : d₀ / 2 * (N : Real) ^ u ≤ (L : Real) := by
      rcases hL with hL | hL
      · subst L
        nlinarith only [hnupper, hlower, hfour]
      · have hLc : (L : Real) + 1 = n := by exact_mod_cast hL
        nlinarith only [hnupper, hlower, hfour, hLc]
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg N) u)).trans hhalf
  have hcc : c₀ ≤ section13Zeta alpha / 2 :=
    div_le_div_of_nonneg_right (section13Zeta_mono hδ hδα hαone) (by norm_num)
  have hcmax : section13Zeta alpha / 2 ≤ 1 / 2 :=
    div_le_div_of_nonneg_right (section13Zeta_le_one hα hαone) (by norm_num)
  have hee : e₀ ≤ e := polyRowExponent_antitone hδ hδα hαone hp
  have hemax : 2 * e ≤ 1 := two_mul_polyRowExponent_le_one hα hαone hp
  have hv : 0 < v := stage135UniformExponent_pos hp
  have hvone : v ≤ 1 := stage135UniformExponent_le_one hp
  have hz : z₀ ≤ section10Zeta (alpha ^ 32 / 16) := by
    apply section10Zeta_mono (by positivity)
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hδ.le hδα 32) (by norm_num))
    have hh := pow_le_one₀ hα.le hαone (n := 32)
    linarith only [hh]
  have hrec : 2 * e ≤ u * v := two_mul_polyRowExponent_le hα hαone hp hq hqB
  obtain ⟨m, hm, hmsq, hmQ, hmlower, hmbohr⟩ := uniform_rounded_power_budgets_explicit hc₀ hd
    (min_le_left _ _) hz₀ he₀ N hround
    (section13Zeta alpha / 2) e u v v (section10Zeta (alpha ^ 32 / 16)) L Q
    hcc hcmax hee hemax hv hvone hv hvone hz hrec hrec hPlower hQlen
  have hcat : section13Zeta alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) ≤
      section13Zeta alpha / 2 * (N : Real) ^ e := by
    apply mul_le_mul_of_nonneg_left _ (by unfold section13Zeta; positivity)
    exact Real.rpow_le_rpow_of_exponent_le hNreal
      (catalogue_length_exponent_le_polyRowExponent hα hαone hp hpB)
  exact ⟨m, hm, by simpa only [pow_two] using hmsq, by exact_mod_cast hmQ,
    hcat.trans hmlower, hmlower, hmbohr⟩

/-- A finite maximum handles every admissible spectrum size. -/
def section13PolyIntegerThreshold (p : Nat) (delta : Real) : Nat :=
  (Finset.range (Nat.floor (section13QBound (section10Lambda (delta ^ 32 / 16))) + 1)).sup
    (fun q => Nat.ceil (section13PolyBudgetThreshold p delta q))

theorem section13_uniform_poly_integer_budgets {delta : Real} (hδ : 0 < delta)
    (hδone : delta ≤ 1) {p : Nat} (hp : 0 < p) (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    (N : Nat) (hN : section13PolyIntegerThreshold p delta ≤ N)
    (alpha : Real) (hδα : delta ≤ alpha) (hαone : alpha ≤ 1) (q n L Q : Nat)
    (hq : 0 < q) (hqB : (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)))
    (hn : IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
      (64 * Real.pi) * (N : Real) ^
        (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) n)
    (hL : L = n ∨ L + 1 = n)
    (hQlen : (L : Real) ^ stage135UniformExponent p q / 2 ≤ Q) :
    ∃ m : Nat, 0 < m ∧ m * m ≤ N ∧ m + 1 ≤ Q ∧
      section13Zeta alpha / 2 *
        (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) ≤ m ∧
      section13Zeta alpha / 2 * (N : Real) ^ polyRowExponent p alpha ≤ m ∧
      (L : Real) ^ (-stage135UniformExponent p q) ≤ section10Zeta (alpha ^ 32 / 16) / m := by
  have hθ : 0 < section10Lambda (delta ^ 32 / 16) := by unfold section10Lambda; positivity
  have hqfloor : q ≤ Nat.floor (section13QBound (section10Lambda (delta ^ 32 / 16))) :=
    Nat.le_floor (hqB.trans (section13QBound_antitone hθ (section13_cutoff_mono hδ hδα)))
  have hqmem : q ∈ Finset.range
      (Nat.floor (section13QBound (section10Lambda (delta ^ 32 / 16))) + 1) :=
    Finset.mem_range.mpr (by omega)
  have hceil : Nat.ceil (section13PolyBudgetThreshold p delta q) ≤ N :=
    (Finset.le_sup (f := fun q => Nat.ceil (section13PolyBudgetThreshold p delta q)) hqmem).trans hN
  exact section13_poly_integer_budgets hδ hδone hp hpB hq N
    ((Nat.le_ceil _).trans (by exact_mod_cast hceil)) alpha hδα hαone hqB n L Q hn hL hQlen

/-- **Stages 13.5 and 13.6 at the polynomial exponent**, above a closed
threshold depending only on the lower density. The row is at least
`ζ(α)/2·N^(polyRowExponent p α)` long. -/
theorem lemma_13_6_poly_explicit {delta : Real} (hδ : 0 < delta) (hδone : delta ≤ 1)
    {K : Real} {p : Nat} (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    (N : Nat) [Fact N.Prime] (S : Section13Context N) (D : Stage134Data N)
    (hS : delta ≤ S.alpha) (hN : section13PolyIntegerThreshold p delta ≤ N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D) :
    ∃ E : Stage135Data N, ∃ F : Stage136Data N,
      IsStage135Data S D E ∧ IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length ∧
      section13Zeta S.alpha / 2 * (N : Real) ^ polyRowExponent p S.alpha ≤ F.R.length := by
  obtain ⟨E, h135, hE⟩ := lemma_13_5_poly_with_catalogue (Fact.out : N.Prime) hpp hp hK S D _ h134
  obtain ⟨m, hm, hsize, hupper, hlower, hpoly, hbudget⟩ :=
    section13_uniform_poly_integer_budgets hδ hδone hp hpB N hN S.alpha hS S.alpha_at_most_one
      D.q D.m D.P.length E.Q.length h134.1 h134.2.2.2.2.1 h134.2.2.2.2.2.1
      h134.2.2.2.2.2.2.1 hE.2.2.2.1
  obtain ⟨F, hF, hmF, hFQ⟩ := lemma_13_6_from_initial_stages_at S D E m _ h134 h135
    hE.2.2.2.2.1 hm hsize hupper hlower hbudget
  exact ⟨E, F, h135, hF, hFQ, hpoly.trans (by exact_mod_cast hmF)⟩

/-- The polynomial square exponent: `polyRowExponent p δ` times the
catalogue's three remaining factors. -/
def section13PolySquareExponent (p : Nat) (delta : Real) : Real :=
  polyRowExponent p delta * ((2 : Real) ^ (-(100 : Int)) * delta ^ 448) *
    cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1 / 4

def section13PolyGeometricThreshold (p : Nat) (delta : Real) : Real :=
  let c := section13Zeta delta / 2
  let e := polyRowExponent p delta
  let f := (2 : Real) ^ (-(100 : Int)) * delta ^ 448
  let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1
  max 1 (max (section13PolyIntegerThreshold p delta)
    (max (squareScaleThreshold c e f g ((2 : Real) ^ 135 * delta ^ (-(704 : Int))))
      (squarePowerThreshold c e f g)))

/-- **The Section 13 square at a polynomial exponent.** Above a closed
threshold, every context of density at least `δ` contains a bilinear square
of side at least `N^(section13PolySquareExponent p δ)`, with the corpus's
density `2^(−137)δ^704`. -/
theorem section13_complete_square_extraction_poly {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1)
    {K : Real} {p : Nat} (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N),
      delta ≤ S.alpha → section13PolyGeometricThreshold p delta ≤ N →
      ∃ V W : ModAP N, ∃ B : Finset (Pair N),
        V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
        (N : Real) ^ section13PolySquareExponent p delta ≤ V.length ∧
        B ⊆ S.A ∧ B ⊆ V.carrier.product W.carrier ∧
        (2 : Real) ^ (-(137 : Int)) * delta ^ 704 * V.length * W.length ≤ B.card ∧
        BilinearOn B S.phi := by
  intro N _ S hS hN
  let c := section13Zeta delta / 2
  let e := polyRowExponent p delta
  let f := (2 : Real) ^ (-(100 : Int)) * delta ^ 448
  let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1
  have hc : 0 < c := by dsimp [c, section13Zeta]; positivity
  have he : 0 < e := polyRowExponent_pos hδ hδone hp
  have hf : 0 < f := mul_pos (zpow_pos (by norm_num) _) (pow_pos hδ _)
  have hg : 0 < g := by dsimp [g, cor711Exponent]; positivity
  have hNreal : (1 : Real) ≤ N := (le_max_left _ _).trans hN
  have hN₂ : section13PolyIntegerThreshold p delta ≤ N := by
    exact_mod_cast ((le_max_left _ _).trans ((le_max_right _ _).trans hN) :
      (section13PolyIntegerThreshold p delta : Real) ≤ N)
  have hN₃ : squareScaleThreshold c e f g ((2 : Real) ^ 135 * delta ^ (-(704 : Int))) ≤
      (N : Real) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN₄ : squarePowerThreshold c e f g ≤ (N : Real) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  let theta := section10Lambda (S.alpha ^ 32 / 16)
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; have := S.alpha_pos; positivity
  obtain ⟨D, hD⟩ := lemma_13_4_holds N S theta (Fact.out : N.Prime) hθ
    (section13_lambda_le_initial_threshold S.alpha_pos S.alpha_at_most_one)
  obtain ⟨E, F, hE, hF, hFupper, hRpoly⟩ :=
    lemma_13_6_poly_explicit hδ hδone hpp hp hK hpB N S D hS hN₂ hD
  have hminimum : c * (N : Real) ^ e ≤ F.R.length := by
    calc
      _ ≤ section13Zeta S.alpha / 2 * (N : Real) ^ polyRowExponent p S.alpha := by
        apply mul_le_mul
          (div_le_div_of_nonneg_right (section13Zeta_mono hδ hS S.alpha_at_most_one) (by norm_num))
          (Real.rpow_le_rpow_of_exponent_le hNreal
            (polyRowExponent_antitone hδ hS S.alpha_at_most_one hp))
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        have := S.alpha_pos
        unfold section13Zeta
        positivity
      _ ≤ _ := hRpoly
  have hRpos : 0 < F.R.length := by
    have hreal : (0 : Real) < F.R.length :=
      (mul_pos hc (Real.rpow_pos_of_pos (zero_lt_one.trans_le hNreal) e)).trans_le hminimum
    exact_mod_cast hreal
  have hRone : (1 : Real) ≤ F.R.length := by exact_mod_cast hRpos
  obtain ⟨hr, hw, hs⟩ := square_scales_above_power_explicit hc he hf hg N F.R.length hN₃ hminimum
  obtain ⟨hfm, hgm, hWm⟩ := section13_square_parameters_mono hδ hS
  obtain ⟨hr', hw', hs', hmono⟩ := square_scales_mono hRone hf hfm hg hgm hWm hr hw hs
  obtain ⟨V, W, B, hVs, hVW, hV, hW, hVl, hsize, hBA, hbox, hmass, hbil⟩ :=
    section13_square_extraction_of_scales S D E F hE hF hFupper hr' hw' hs'
  have hsmall : (c * (N : Real) ^ e) ^ f ≤ (F.R.length : Real) ^ f :=
    Real.rpow_le_rpow (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hminimum hf.le
  have hfloor : Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 ≤
      Nat.floor ((F.R.length : Real) ^ f) / 2 := Nat.div_le_div_right (Nat.floor_mono hsmall)
  have hfloorR : ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ≤
      ((Nat.floor ((F.R.length : Real) ^ f) / 2 : Nat) : Real) := by exact_mod_cast hfloor
  have hpower := Real.rpow_le_rpow (Nat.cast_nonneg _) hfloorR
    (div_nonneg hg.le (by norm_num : (0 : Real) ≤ 2))
  have hNpower := square_power_lower_explicit hc he hf hg N hN₄
  refine ⟨V, W, B, hVs, hVW, hV, hW, hVl, ?_, hBA, hbox, ?_, hbil⟩
  · change (N : Real) ^ (e * f * g / 4) ≤ V.length
    linarith only [hNpower, hpower, hmono, hsize]
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hS 704) (by positivity))
      (Nat.cast_nonneg V.length)) (Nat.cast_nonneg W.length)).trans hmass

end LeanProofs.GowersSzemeredi
