"""Proofs18CoverFejerHeadlineQ: Theorem 18.1 at d+5 (d >= 12), Theorem 18.2 at L+3 (L >= 14)."""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import assemble_coverq as cq  # noqa: E402  (re-running it regenerates the three cover modules)

GS = cq.GS
s = (GS / 'Proofs18CoverFejerHeadline.lean').read_text(encoding='utf-8')
a = s.index('/-- The envelope after one step (no threshold). -/')
b = s.index('/-! ### Closed forms -/')
body = s[a:b]
body = cq.sub(body, [('''        unfold tightMu0 fixDeg; have := Nat.lt_two_pow_self (n := k + 5)
        have := le_max_right (tightMuV k) (2 ^ (k + 5) + 7); omega)''',
                      '''        unfold tightMu0Q; have := five_k_le_fixDegQ k
        have := le_max_right (tightMuV k) (fixDegQ k); omega)''')])
body = cq.common(body)
cq.check('HeadlineQ', body)

HEADER = '''import GowersSzemeredi.Proofs18CoverExponentsFejerQ
import GowersSzemeredi.Proofs18CoverFejerHeadline

/-! **Theorem 18.1 at `d + 5` for every `d ≥ 12` and Theorem 18.2 /
Corollary 18.7 at `L + 3` for every `L ≥ 14`, from the recurrence profiles**
(Notes L.16i).

The Section 18 envelope at `GenParamsQ`. The class covers sit at degree
`uDegQ l = 2^qDeg l`, `qDeg l = 14·2^l + 3(l+4)² + 2`
(`polyCoverAt_classQ`, from the split invariant with additive slack). The
base budget is `tightMu0Q k = max(tightMuV k, fixDegQ k) + 2 = 2^(k+4) + 9`,
the class-base term, since the Fejér θ₁ no longer forces the printed
`2^(k+5) + 9`. The step lemmas and recursions are generated from
`Proofs18CoverFejerHeadline`; the closed forms are new.

One step now costs exactly `58·2^k + 9(k+4)² + 4(k+3)² + k + 45`
(`envStepQ_le_tight`), so the envelope tends to `116·2^k < 128·2^k`. The
polynomial terms are absorbed from `k = 10` (`polyGenMuQ_le`,
`genMuXQ_le`: `μ_k + 4k + 128 ≤ 128·2^k`). This yields:
* `theorem_18_1_d5_of_profiles_cover`: Theorem 18.1 with exponent
  `α^(2^(2^(d+5)))` at every degree `d ≥ 12`;
* `theorem_18_2_L3_of_profiles_cover`, `corollary_18_7_L3_of_profiles_cover`:
  `L + 3` at every length `L ≥ 14`.
Smaller degrees and lengths keep `d + 6` / `L + 4`
(`Proofs18CoverFejerHeadline`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The base budget at the class-base term. -/
def tightMu0Q (k : Nat) : Nat := max (tightMuV k) (fixDegQ k) + 2

'''

TAIL = r'''
/-! ### Closed forms -/

/-- One step at `(qDeg, tightMu0Q)` costs `58·2^k` plus a polynomial. -/
theorem envStepQ_le_tight {k : Nat} (hk : 1 ≤ k) (μ : Nat) :
    envStepQ k (tightMu0Q k) (genMuK k) μ ≤
      μ + 58 * 2 ^ k + 9 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + k + 45 := by
  unfold envStepQ GenParamsQ.densDegQ GenParamsQ.expDegQ GenParamsQ.rhoDegQ tightMu0Q tightMuV
    genMuK qDeg
  rw [fixDegQ_eq hk, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

theorem envStepQTx_le_tight {k : Nat} (hk : 1 ≤ k) (μ : Nat) :
    envStepQTx k (tightMu0Q k) (genMuK k) μ ≤
      max (μ + 58 * 2 ^ k + 9 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + k + 45) (64 * 2 ^ k + 8) := by
  unfold envStepQTx GenParamsQ.densDegQ GenParamsQ.threshDegQ GenParamsQ.expDegQ
    GenParamsQ.rhoDegQ tightMu0Q tightMuV genMuK qDeg
  rw [fixDegQ_eq hk, two_pow_six_mul, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

theorem envStepQTx_ge_tight {k : Nat} (hk : 1 ≤ k) (μ : Nat) :
    μ + 58 * 2 ^ k ≤ envStepQTx k (tightMu0Q k) (genMuK k) μ := by
  unfold envStepQTx GenParamsQ.densDegQ GenParamsQ.rhoDegQ tightMu0Q tightMuV qDeg
  rw [fixDegQ_eq hk, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

/-- `4(k+5)² ≤ 2^k` for `k ≥ 10`. -/
theorem four_sq_le_two_pow_ten : ∀ k, 10 ≤ k → 4 * (k + 5) ^ 2 ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1 + 5) ^ 2 ≤ 2 * (k + 5) ^ 2 := by nlinarith
    calc 4 * (k + 1 + 5) ^ 2 ≤ 2 * (4 * (k + 5) ^ 2) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

theorem polyGenMuQ_ten : polyGenMuQ 10 + 4 * 10 + 128 ≤ 128 * 2 ^ 10 := by decide

/-- **The Theorem 18.1 envelope at `(qDeg, tightMu0Q)`**: `μ_k + 4k + 128 ≤ 128·2^k`
for `k ≥ 10`. -/
theorem polyGenMuQ_le : ∀ k, 10 ≤ k → polyGenMuQ k + 4 * k + 128 ≤ 128 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyGenMuQ_ten
  | succ k hk ih =>
    rw [polyGenMuQ_succ (by omega)]
    have h1 := envStepQ_le_tight (k := k + 1) (by omega) (polyGenMuQ k)
    have h2 := four_sq_le_two_pow_ten k hk
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : k + 50 ≤ 2 ^ k := le_trans (by nlinarith) h2
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXQ_ten : genMuXQ 10 + 4 * 10 + 128 ≤ 128 * 2 ^ 10 := by decide

theorem genMuXQ_le : ∀ k, 10 ≤ k → genMuXQ k + 4 * k + 128 ≤ 128 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXQ_ten
  | succ k hk ih =>
    rw [genMuXQ_succ (by omega)]
    have h1 := envStepQTx_le_tight (k := k + 1) (by omega) (genMuXQ k)
    have h2 := four_sq_le_two_pow_ten k hk
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : k + 50 ≤ 2 ^ k := le_trans (by nlinarith) h2
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXQ_ge : ∀ k, 2 ≤ k → 58 * 2 ^ k ≤ genMuXQ k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXQ_succ (by omega)]
  have := envStepQTx_ge_tight (k := j + 1) (by omega) (genMuXQ j)
  omega

/-! ### The headline statements -/

/-- **Theorem 18.1 at every degree `d ≥ 12` with exponent `α^(2^(2^(d+5)))`**,
from the recurrence profiles and a phase partition. -/
theorem theorem_18_1_d5_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd : 12 ≤ d) : Theorem181AtSharp 5 d := by
  have henv := polyEnvBound_allQ Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  have hle := polyGenMuQ_le (d - 2) (by omega)
  have h2 : 2 ^ (d + 5) = 128 * 2 ^ (d - 2) := by
    rw [show d + 5 = (d - 2) + 7 by omega, pow_add]; ring
  rw [h2]
  omega

/-- **Theorem 18.2 at every length `L ≥ 14` with `L + 3` in the threshold**,
from the recurrence profiles. -/
theorem theorem_18_2_L3_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL : 14 ≤ L) : Theorem182AtSharp 3 L := by
  have henv := envBound_allXQ Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXQ_ge (L - 4) (by omega)
  have hle := genMuXQ_le (L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have h4 : 4 ≤ 2 ^ (L - 4) :=
    le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h42 : 42 ≤ genMuXQ (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXQ (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXQ (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  have h2 : 2 ^ (L + 3) = 128 * 2 ^ (L - 4) := by
    rw [show L + 3 = (L - 4) + 7 by omega, pow_add]; ring
  rw [h2]
  omega

/-- **Corollary 18.7 at every length `L ≥ 14` with `L + 3`**, from the profiles. -/
theorem corollary_18_7_L3_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL : 14 ≤ L) : Corollary187AtSharp 3 L :=
  (theorem_18_2_L3_of_profiles_cover Kc pc hK hp hrec hconst hL).corollary_18_7

end LeanProofs.GowersSzemeredi
'''
out = HEADER + body + TAIL
(GS / 'Proofs18CoverFejerHeadlineQ.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
