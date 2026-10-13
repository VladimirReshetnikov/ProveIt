import GowersSzemeredi.Proofs18CoverDegrees
import GowersSzemeredi.Proofs18ThresholdAt

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

/-! ### The sharper envelope and the sharper theorems -/

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
