import GowersSzemeredi.Proofs18CoverDegrees
import GowersSzemeredi.Proofs18GenericSzemeredi

/-! **Sharper exponents for Theorems 18.1 and 18.2** (Notes L.15).

The joint-cover envelopes (`Proofs18CoverDegrees`) are at most `1000·2^k`,
a quarter of the printed budgets. They therefore prove the two theorems with
smaller tower constants:
* Theorem 18.1 at degree `d ≥ 4` with exponent `α^(2^(2^(d+8)))` in place of
  the printed `α^(2^(2^(d+10)))` (`theorem_18_1_sharper_of_profiles_cover`);
* Theorem 18.2 at length `L ≥ 6` with threshold `2^(2^(δ⁻¹^(2^(2^(L+6)))))`
  in place of the printed `L + 9` (`theorem_18_2_sharper_of_profiles_cover`).

`Theorem181AtSharp c k` and `Theorem182AtSharp c k` are `Theorem181At` and
`Theorem182At` with `k + c` in place of `k + 10` and `k + 9`; at the printed
constants they are the catalogue statements (`theorem181AtSharp_ten_iff`,
`theorem182AtSharp_nine_iff`), and they weaken as `c` grows (`.mono`). The
method stops here: the envelope recursion grows like `536·2^k`, which exceeds
`512·2^k`, so `d + 7` and `L + 5` are out of reach.

`genMuC_le_sharp` (`genMuC k ≤ 1000·2^k`) tightens `genMuC_le` with the
cube bound `(k+3)³ ≤ 32·2^k`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-! ### Theorem 18.1 with a parameterized exponent -/

/-- The Theorem 18.1 exponent with `k + c` in place of the printed `k + 10`. -/
def section18ExponentAt (c : Nat) (alpha : Real) (k : Nat) : Real :=
  alpha ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + c)))

/-- Theorem 18.1 at degree `k` with the exponent `section18ExponentAt c`. -/
def Theorem181AtSharp (c k : Nat) : Prop :=
  ∀ (alpha : Real), 0 < alpha → alpha ≤ 1 / 2 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ A : Finset (ZMod N), ¬ UniformSetOfDegree A alpha k →
        ∃ M : Nat, ∃ P : Fin M → ModAP N,
          IsPartition (fun i => (P i).carrier) Finset.univ ∧
          (∀ i, (P i).IsProper) ∧
          (N : Real) ^ section18ExponentAt c alpha k ≤
            averageCellSize (fun i => (P i).carrier) ∧
          section18ExponentAt c alpha k * N ≤
            ∑ i, ‖∑ s ∈ (P i).carrier, balanced A s‖

/-- At `c = 10` it is the catalogue's Theorem 18.1 at degree `k`. -/
theorem theorem181AtSharp_ten_iff (k : Nat) : Theorem181AtSharp 10 k ↔ Theorem181At k :=
  Iff.rfl

/-- A smaller constant gives a stronger statement. -/
theorem Theorem181AtSharp.mono {c c' k : Nat} (h : Theorem181AtSharp c k) (hc : c ≤ c') :
    Theorem181AtSharp c' k := by
  intro alpha ha ha2
  obtain ⟨N0, hN0⟩ := h alpha ha ha2
  refine ⟨N0, fun N _ _ hN A hA => ?_⟩
  obtain ⟨M, P, hp, hpr, h1, h2⟩ := hN0 N hN A hA
  have hle : section18ExponentAt c' alpha k ≤ section18ExponentAt c alpha k :=
    pow_le_pow_of_le_one ha.le (by linarith)
      (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  exact ⟨M, P, hp, hpr, (Real.rpow_le_rpow_of_exponent_le hN1 hle).trans h1,
    (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)).trans h2⟩

theorem Theorem181AtSharp.of_function_discrepancy {c k : Nat}
    (h : ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 → ∃ beta sigma T : Real,
      section18ExponentAt c alpha k ≤ beta ∧ section18ExponentAt c alpha k ≤ sigma ∧
        FunctionDiscrepancyBound k alpha beta sigma T) :
    Theorem181AtSharp c k := by
  intro alpha hα hα2
  obtain ⟨beta, sigma, T, hb, hs, hT⟩ := h alpha hα hα2
  refine ⟨⌈T⌉₊, fun N _ _ hN A hnot => ?_⟩
  obtain ⟨M, Q, hpart, hproper, hsize, hdisc⟩ :=
    hT N ((Nat.le_ceil T).trans (by exact_mod_cast hN)) (balanced A)
      (balanced_discValued A) hnot
  refine ⟨M, Q, hpart, hproper, ?_, ?_⟩
  · have hN1 : (1 : Real) ≤ N := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    exact (Real.rpow_le_rpow_of_exponent_le hN1 hs).trans hsize
  · exact (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg N)).trans hdisc

theorem section18ExponentAt_le_of_inv_le {alpha : Real} (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2)
    {x : Real} (hx : 0 < x) {μ k c : Nat} (hμ : μ + 1 ≤ 2 ^ (k + c))
    (hxinv : x⁻¹ ≤ (2 / alpha) ^ (2 ^ μ)) : section18ExponentAt c alpha k ≤ x := by
  have hαone : alpha ≤ 1 := by linarith only [hα2]
  unfold section18ExponentAt
  have h1 : alpha ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + c))) ≤ alpha ^ (2 ^ (μ + 1)) :=
    pow_le_pow_of_le_one hα.le hαone (Nat.pow_le_pow_right (by norm_num) hμ)
  have h2 : alpha ^ (2 ^ (μ + 1)) = (alpha ^ 2) ^ (2 ^ μ) := by
    rw [pow_succ, mul_comm (2 ^ μ) 2, pow_mul]
  have h3 : (alpha ^ 2) ^ (2 ^ μ) ≤ (alpha / 2) ^ (2 ^ μ) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith only [hα, hα2]) _
  have h4 : (alpha / 2) ^ (2 ^ μ) = ((2 / alpha) ^ (2 ^ μ))⁻¹ := by rw [← inv_pow, inv_div]
  have h5 : ((2 / alpha) ^ (2 ^ μ))⁻¹ ≤ x := by
    have h := inv_anti₀ (inv_pos.mpr hx) hxinv
    rwa [inv_inv] at h
  calc _ ≤ alpha ^ (2 ^ (μ + 1)) := h1
    _ = (alpha ^ 2) ^ (2 ^ μ) := h2
    _ ≤ (alpha / 2) ^ (2 ^ μ) := h3
    _ = ((2 / alpha) ^ (2 ^ μ))⁻¹ := h4
    _ ≤ x := h5

theorem theorem181AtSharp_of_polyEnvBound {c d μ : Nat} (h : PolyEnvBound d μ)
    (hμ : μ + 1 ≤ 2 ^ (d + c)) : Theorem181AtSharp c d := by
  apply Theorem181AtSharp.of_function_discrepancy
  intro alpha ha ha2
  obtain ⟨b, s, T, hB, b0, -, s0, -, bi, si⟩ := h alpha ha ha2
  exact ⟨b, s, T, section18ExponentAt_le_of_inv_le ha ha2 b0 hμ bi,
    section18ExponentAt_le_of_inv_le ha ha2 s0 hμ si, hB⟩

/-! ### Theorem 18.2 with a parameterized threshold -/

/-- The Theorem 18.2 threshold with `k + c` in place of the printed `k + 9`. -/
def szemerediThresholdAt (c : Nat) (delta : Real) (k : Nat) : Real :=
  (2 : Real) ^
    ((2 : Real) ^
      (delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat)))))

/-- Theorem 18.2 at length `k` with the threshold `szemerediThresholdAt c`. -/
def Theorem182AtSharp (c k : Nat) : Prop :=
  ∀ (delta : Real) (N : Nat), 0 < delta → delta ≤ 1 / 2 →
    szemerediThresholdAt c delta k ≤ N →
    ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → delta * N ≤ A.card → HasNatAP A k

/-- At `c = 9` it is the catalogue's Theorem 18.2 at length `k`. -/
theorem theorem182AtSharp_nine_iff (k : Nat) : Theorem182AtSharp 9 k ↔ Theorem182At k :=
  Iff.rfl

theorem double_exp_le_szemerediThresholdAt {L μ c : Nat} (hL : 1 ≤ L) {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + c)) :
    Real.exp (Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)))) ≤
      szemerediThresholdAt c delta L := by
  obtain ⟨ha0, -, -, hXu⟩ := intervalUniformityParameter_gen_bounds hL hδ hδhalf
  set u : Real := delta⁻¹ with hu'
  have hu : 2 ≤ u := by rw [hu', ← one_div, le_div_iff₀ hδ]; linarith
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  set q : Nat := 2 ^ (μ + 2 * L + 13) with hq
  set E : Nat := 2 ^ (2 ^ (L + c)) with hE
  have hqE : q + 2 ≤ E := by
    have h2 : 2 ^ (μ + 2 * L + 14) = 2 * 2 ^ (μ + 2 * L + 13) := by
      rw [show μ + 2 * L + 14 = (μ + 2 * L + 13) + 1 by ring, pow_succ]; ring
    have h3 : 2 ≤ 2 ^ (μ + 2 * L + 13) :=
      le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h1 : q + 2 ≤ 2 ^ (μ + 2 * L + 14) := by rw [hq]; omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) hfit)
  have habsorb : (2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)) ≤ u ^ q := by
    have h := pow_le_pow_left₀ (by positivity) hXu (2 ^ (μ + 9))
    rw [← pow_mul, ← pow_add] at h
    rw [hq, show μ + 2 * L + 13 = 2 * L + 4 + (μ + 9) by ring]
    exact h
  have hx1 : 1 ≤ u ^ q := one_le_pow₀ hu1
  have hinner : 1 + 2 * u ^ q ≤ u ^ E := by
    calc
      _ ≤ u ^ q * 4 := by linarith only [hx1]
      _ ≤ u ^ q * u ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hu] : (4 : Real) ≤ u ^ 2) (by positivity)
      _ = u ^ (q + 2) := (pow_add u q 2).symm
      _ ≤ _ := pow_le_pow_right₀ hu1 hqE
  have hexp : Real.exp (Real.exp (u ^ q)) ≤ (2 : Real) ^ ((2 : Real) ^ (u ^ E)) := by
    apply (section18_exp_le_two_rpow (Real.exp_pos _).le).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc
      2 * Real.exp (u ^ q) ≤ 2 * (2 : Real) ^ (2 * u ^ q) :=
        mul_le_mul_of_nonneg_left (section18_exp_le_two_rpow (by positivity)) (by norm_num)
      _ = (2 : Real) ^ (1 + 2 * u ^ q) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner
  refine (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr habsorb)).trans (hexp.trans (le_of_eq ?_))
  unfold szemerediThresholdAt
  rw [hE, ← hu']
  simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]

theorem theorem182AtSharp_of_envBound {L μ c : Nat} (hL : 3 ≤ L) (henv : EnvBound (L - 2) μ)
    (hμ : 42 ≤ μ) (hLμ : 4 * L + 20 ≤ 2 ^ μ) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + c)) :
    Theorem182AtSharp c L := by
  intro delta N hδ hδhalf hN A hA hcard
  obtain ⟨ha0, haδ, -, -⟩ := intervalUniformityParameter_gen_bounds (by omega : 1 ≤ L) hδ hδhalf
  have ha2 : intervalUniformityParameter delta L ≤ 1 / 2 := haδ.trans hδhalf
  obtain ⟨beta, sigma, T, hB, b0, b1, s0, -, bi, si, Ti⟩ := henv _ ha0 ha2
  have hclosed := closedThreshold_le_of_env (by omega : 1 ≤ L) hδ hδhalf hμ hLμ b0 b1 s0 bi si Ti
  have hsrc := double_exp_le_szemerediThresholdAt (by omega : 1 ≤ L) hδ hδhalf hfit
  exact FunctionDiscrepancyBound.natural_szemeredi_closed (k := L) (by omega) hδ b0 s0 hB N
    ((hclosed.trans hsrc).trans hN) A hA hcard

/-! ### The sharper envelope and the sharper theorems -/

/-- `(k+3)³ ≤ 32·2^k`. -/
theorem cube_le_two_pow_sharp (k : Nat) : (k + 3) ^ 3 ≤ 32 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; norm_num
    · have hstep : (k + 1 + 3) ^ 3 ≤ 2 * (k + 3) ^ 3 := by
        have hk : 1 ≤ k := h
        nlinarith [sq_nonneg (k : Nat), hk]
      calc (k + 1 + 3) ^ 3 ≤ 2 * (k + 3) ^ 3 := hstep
        _ ≤ 2 * (32 * 2 ^ k) := Nat.mul_le_mul_left _ ih
        _ = 32 * 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- **The Theorem 18.2 envelope is at most `1000·2^k`.** -/
theorem genMuC_le_sharp : ∀ k, 1 ≤ k → genMuC k ≤ 1000 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => show 62 ≤ 1000 * 2 ^ 1; norm_num
  | succ k hk ih =>
    rw [genMuC_succ hk]
    have h1 := envStepCT_le (k + 1) (genMuC k)
    have h2 := quad_le_two_pow k
    have h3 := cube_le_two_pow_sharp k
    have h4 : 2 ≤ 2 ^ k := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hk)
    rw [show k + 1 + 2 = k + 3 by ring] at h1
    rw [pow_succ] at h1 ⊢
    refine h1.trans (max_le (by omega) (by omega))

/-- **Theorem 18.1 at every degree `d ≥ 4` with exponent `α^(2^(2^(d+8)))`**,
from the recurrence profiles and a phase partition. -/
theorem theorem_18_1_sharper_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd4 : 4 ≤ d) : Theorem181AtSharp 8 d := by
  have henv := polyEnvBound_allC Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  have h := polyGenMuC_le (d - 2) (by omega)
  have h2 : 2 ^ (d + 8) = 1024 * 2 ^ (d - 2) := by
    rw [show d + 8 = (d - 2) + 10 by omega, pow_add]; ring
  rw [h2]
  have := Nat.one_le_two_pow (n := d - 2)
  omega

/-- **Theorem 18.2 at every length `L ≥ 6` with `L + 6` in the threshold**,
from the recurrence profiles. -/
theorem theorem_18_2_sharper_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) : Theorem182AtSharp 6 L := by
  have henv := envBound_allC Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hle := genMuC_le_sharp (L - 4) (by omega)
  have hge := genMuC_ge (L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have h4 : 4 ≤ 2 ^ (L - 4) :=
    le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h42 : 42 ≤ genMuC (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuC (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuC (L - 4))
    omega
  have h2 : 2 ^ (L + 6) = 1024 * 2 ^ (L - 4) := by
    rw [show L + 6 = (L - 4) + 10 by omega, pow_add]; ring
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  rw [h2]
  omega

end LeanProofs.GowersSzemeredi
