import Diophantine.Paper1982.Carries
import Mathlib.Tactic

/-!
# The literal compact54 local native clause

The low fields are 9,9,9,2 bits wide; the aggregate payload has 44 masked
bits. This file treats the actual mask and positive receiver increments.
Global clean-band and native phase recovery are separate obligations.
-/

namespace DiophantineConsistency.NativeClause54

open Jones1982

def labelBase : ℕ := 2 ^ 42
def payloadModulus : ℕ := 2 ^ 44

def pack (n gr gl gu P : ℕ) : ℕ :=
  n + (gr + (gl + (gu + P * 2 ^ 2) * 2 ^ 9) * 2 ^ 9) * 2 ^ 9

def clauseMask : ℕ :=
  510 + (256 + (256 + (2 + (payloadModulus - 1) * 2 ^ 2) * 2 ^ 9) * 2 ^ 9) * 2 ^ 9

theorem clauseMask_eq : clauseMask =
    510 + 2 ^ 17 + 2 ^ 26 + 2 ^ 28 + 2 ^ 29 * (2 ^ 44 - 1) := by decide

theorem pack_eq (n gr gl gu P : ℕ) : pack n gr gl gu P =
    n + 2 ^ 9 * gr + 2 ^ 18 * gl + 2 ^ 27 * gu + 2 ^ 29 * P := by
  unfold pack
  norm_num
  ring

theorem masked_pair_iff {k a b M N : ℕ} (ha : a < 2 ^ k) (hM : M < 2 ^ k) :
    (a + b * 2 ^ k) &&& (M + N * 2 ^ k) = 0 ↔ a &&& M = 0 ∧ b &&& N = 0 := by
  simpa only [τ_two_eq_zero_iff] using (lemma_2_10 ha hM).symm

/-- The selector mask is decoded before any assumption about higher carries. -/
theorem selector_iff {n : ℕ} (hn : n < 512) : n &&& 510 = 0 ↔ n ≤ 1 := by
  constructor
  · intro h
    have hdiv := congrArg (fun z : ℕ => z / 2) h
    rw [Nat.and_div_two] at hdiv
    change n / 2 &&& 255 = 0 at hdiv
    have he : n / 2 &&& 255 = n / 2 := by
      exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) (by omega)
    rw [he] at hdiv
    omega
  · intro h
    interval_cases n <;> decide

theorem clear_top_bit_iff {v k : ℕ} (hv : v < 2 ^ (k + 1)) :
    v &&& 2 ^ k = 0 ↔ v < 2 ^ k := by
  constructor
  · intro h
    by_contra hlt
    have ht := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega : 2 ^ k ≤ v) hv
    rw [Nat.and_two_pow,ht] at h
    simp at h
  · intro h
    rw [Nat.and_two_pow,Nat.testBit_lt_two_pow h]
    simp

theorem masked_fields_iff {n gr gl gu P : ℕ}
    (hn : n < 512) (hR : gr < 512) (hL : gl < 512) (hu : gu < 4) :
    pack n gr gl gu P &&& clauseMask = 0 ↔
      n &&& 510 = 0 ∧ gr &&& 256 = 0 ∧ gl &&& 256 = 0 ∧
      gu &&& 2 = 0 ∧ P % payloadModulus = 0 := by
  unfold pack clauseMask
  rw [masked_pair_iff (k := 9) hn (by decide),
    masked_pair_iff (k := 9) hR (by decide),
    masked_pair_iff (k := 9) hL (by decide),
    masked_pair_iff (k := 2) hu (by decide)]
  change _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ P % 2 ^ 44 = 0
  unfold payloadModulus
  rw [Nat.and_two_pow_sub_one_eq_mod]

def rightGate (n alpha QR : ℕ) : ℕ := 255 * (n - alpha) + QR
def leftGate (n beta QL : ℕ) : ℕ := 255 * (n - beta) + QL
def commonGate (n alpha beta u : ℕ) : ℕ := n - alpha - beta + u

/-- Exact arithmetic consequences of the selector and three gate fields. -/
theorem gate_sound {n alpha beta QR QL u P : ℕ}
    (hn : n < 512) (hQR : QR < 256) (hQL : QL < 256) (hu : u ≤ 1)
    (hmask : pack n (rightGate n alpha QR) (leftGate n beta QL)
      (commonGate n alpha beta u) P &&& clauseMask = 0) :
    n ≤ 1 ∧ rightGate n alpha QR < 256 ∧ leftGate n beta QL < 256 ∧
      commonGate n alpha beta u < 2 ∧ P % payloadModulus = 0 ∧
      (n = 1 → (alpha = 0 → QR = 0) ∧ (beta = 0 → QL = 0) ∧
        (alpha = 0 → beta = 0 → u = 0)) := by
  have hfirst : n &&& 510 = 0 := by
    exact ((masked_pair_iff (k := 9) hn (by decide)).mp hmask).1
  have hn1 := (selector_iff hn).mp hfirst
  have hR : rightGate n alpha QR < 512 := by dsimp [rightGate]; omega
  have hL : leftGate n beta QL < 512 := by dsimp [leftGate]; omega
  have hU : commonGate n alpha beta u < 4 := by dsimp [commonGate]; omega
  obtain ⟨_,hRmask,hLmask,hUmask,hP⟩ := (masked_fields_iff hn hR hL hU).mp hmask
  have hR' : rightGate n alpha QR < 256 := (clear_top_bit_iff (k := 8) hR).mp hRmask
  have hL' : leftGate n beta QL < 256 := (clear_top_bit_iff (k := 8) hL).mp hLmask
  have hU' : commonGate n alpha beta u < 2 := (clear_top_bit_iff (k := 1) hU).mp hUmask
  refine ⟨hn1,hR',hL',hU',hP,?_⟩
  intro hnEq
  dsimp [rightGate,leftGate,commonGate] at hR' hL' hU'
  constructor
  · intro h; omega
  constructor
  · intro h; omega
  · intro h h'; omega

def auxiliary (QR QL u : ℕ) : ℕ :=
  2 * QR + 2 ^ 11 * u + 2 ^ 21 * (2 * QL) + 2 ^ 32 * (2 * QR + 2 * QL + u)

theorem auxiliary_eq_zero_iff (QR QL u : ℕ) :
    auxiliary QR QL u = 0 ↔ QR = 0 ∧ QL = 0 ∧ u = 0 := by
  unfold auxiliary
  norm_num
  omega

theorem auxiliary_even (QR QL u : ℕ) : auxiliary QR QL u % 2 = 0 := by
  unfold auxiliary
  omega

theorem auxiliary_lt {QR QL u : ℕ} (hQR : QR < 256) (hQL : QL < 256) (hu : u ≤ 1) :
    auxiliary QR QL u < labelBase := by
  unfold auxiliary labelBase
  norm_num
  omega

def payload (n L V Z y A1 A2 : ℕ) : ℕ := n + L + V + Z + labelBase * (y + A1 + A2)

/-- The complete aggregate decoder, including the exact empty-cell result.
The occupied label range is a numeric field-fit premise, separated from
the global clause and from the literal mode-table binding. -/
theorem aggregate_iff {n L V Z y A1 A2 : ℕ}
    (hn : n ≤ 1) (hLzero : n = 0 → L = 0) (hLV : n = 1 → L + V < labelBase)
    (hV : V < labelBase) (hZ : Z < labelBase)
    (hLeven : L % 2 = 0) (hVeven : V % 2 = 0) (hZbit : Z % 2 = y)
    (hy : y ≤ 1) (hA1 : A1 ≤ 1) (hA2 : A2 ≤ 1) :
    payload n L V Z y A1 A2 % payloadModulus = 0 ↔
      (n = 0 ∧ L = 0 ∧ V = 0 ∧ Z = 0 ∧ y = 0 ∧ A1 = 0 ∧ A2 = 0) ∨
      (n = 1 ∧ y = 1 ∧ A1 = 1 ∧ A2 = 1 ∧ L + V + Z = labelBase - 1) := by
  constructor
  · intro hmod
    have hmod2 : payload n L V Z y A1 A2 % 2 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_trans (by decide : 2 ∣ payloadModulus) (Nat.dvd_of_mod_eq_zero hmod)
    have hny : n = y := by
      unfold payload labelBase at hmod2
      omega
    by_cases hn0 : n = 0
    · left
      have hL := hLzero hn0
      unfold payload labelBase payloadModulus at hmod
      unfold labelBase at hV hZ
      omega
    · right
      have hn1 : n = 1 := by omega
      have hLV' := hLV hn1
      unfold payload labelBase payloadModulus at hmod
      unfold labelBase at hLV' hZ
      unfold labelBase
      omega
  · rintro (⟨hn,hL,hV,hZ,hy,hA1,hA2⟩ | ⟨hn,hy,hA1,hA2,hLVZ⟩)
    · subst_vars
      rfl
    · unfold payload labelBase payloadModulus at *
      omega

end DiophantineConsistency.NativeClause54
