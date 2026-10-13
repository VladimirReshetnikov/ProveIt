import GowersSzemeredi.Proofs18CoverDegrees
import GowersSzemeredi.Proofs18ThresholdAt
import GowersSzemeredi.Proofs18SharpInterfaces

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

/-! The parameterized interfaces are re-exported from `Proofs18SharpInterfaces`. -/

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
