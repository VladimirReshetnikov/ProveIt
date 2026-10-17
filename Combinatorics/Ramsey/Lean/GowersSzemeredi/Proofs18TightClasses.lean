import GowersSzemeredi.Proofs18UniformCovers
import GowersSzemeredi.Proofs18UniformCoversSide

/-! A tighter degree for the split classes (Notes L.10b).

`split_pair_bounds` keeps `D_k ≤ 2^(75·2^k)`. The recursion
`D_{k+1} ≤ 2^(k+6)·a_k·(a_k + D_k)·P_k + T_k`, with `2^(k+6)·a_k ≤ 2^(35·2^k)`,
`P_k = 2^(32·2^k+6)` and `T_k = 2^(64·2^k)`, has its fixed point at
`log D_k ≈ 67·2^k`.
* `split_pair_tight`: `2·D_k ≤ 2^(68·2^k)` for every `k ≥ 3`. The base `k = 3`
  is computed from the seed, and the step needs `8 ≤ 2^k`.
* `uDeg68 l = 2^(68·2^l)` and `split_pair_le_uDeg68`.
* `polyCoverAt_class68`: the cover in dimension `l` at degree `uDeg68 l`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem stepP_eq (k : Nat) : stepP k = 2 ^ (32 * 2 ^ k + 6) := by
  unfold stepP; congr 1; rw [pow_add]; ring

theorem stepT_eq (k : Nat) : stepT k = 2 ^ (64 * 2 ^ k) := by
  unfold stepT; congr 1; rw [pow_add]; ring

/-- **The tight split degree**: `2·D_k ≤ 2^(68·2^k)` for `k ≥ 3`. -/
theorem split_pair_tight : ∀ k, 3 ≤ k → 2 * (splitPair k).2 ≤ 2 ^ (68 * 2 ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [show (3 : Nat) = 2 + 1 from rfl, splitPair_succ le_rfl, splitPair_two]
    have hstep := splitStepD_le (k := 2) (a := splitSeed) (D := splitSeed)
      (by unfold splitSeed; exact Nat.one_le_two_pow) (by unfold splitSeed; exact Nat.one_le_two_pow)
    rw [stepP_eq, stepT_eq] at hstep
    have hval : 2 ^ (2 + 6) * (splitSeed * (splitSeed + splitSeed)) * 2 ^ (32 * 2 ^ 2 + 6) +
        2 ^ (64 * 2 ^ 2) = 2 ^ 407 + 2 ^ 256 := by
      unfold splitSeed
      rw [show (2 : Nat) ^ 132 + 2 ^ 132 = 2 ^ 133 by ring]
      rw [← pow_add, ← pow_add, ← pow_add,
        show 2 + 6 + (132 + 133) + (32 * 2 ^ 2 + 6) = 407 by norm_num,
        show 64 * 2 ^ 2 = 256 by norm_num]
    rw [hval] at hstep
    have h1 : 2 ^ 256 ≤ 2 ^ 407 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have h2 : 2 * (2 ^ 407 + 2 ^ 256) ≤ 2 ^ 409 := by
      have e : (2 : Nat) ^ 409 = 4 * 2 ^ 407 := by
        rw [show (409 : Nat) = 2 + 407 from rfl, pow_add]; norm_num
      rw [e]
      calc 2 * (2 ^ 407 + 2 ^ 256) ≤ 2 * (2 ^ 407 + 2 ^ 407) :=
            Nat.mul_le_mul_left 2 (Nat.add_le_add_left h1 _)
        _ = 4 * 2 ^ 407 := by rw [← two_mul, ← mul_assoc, show (2 : Nat) * 2 = 4 from rfl]
    have h3 : 2 ^ 409 ≤ 2 ^ (68 * 2 ^ 3) := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact (Nat.mul_le_mul_left 2 hstep).trans (h2.trans h3)
  | succ k hk ih =>
    obtain ⟨ha, hD, hA, -⟩ := split_pair_bounds k (by omega)
    rw [splitPair_succ (by omega)]
    set a := (splitPair k).1
    set D := (splitPair k).2
    set E := 2 ^ k with hEdef
    have hE8 : 8 ≤ E := by
      rw [hEdef]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hstep := splitStepD_le (k := k) ha hD
    rw [stepP_eq, stepT_eq] at hstep
    -- `a + D ≤ 2^(68E)`
    have h2a : 2 * a ≤ 2 ^ (68 * E) := by
      have h1 : 2 ≤ 2 ^ (k + 6) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (35 * E) ≤ 2 ^ (68 * E) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 * a ≤ 2 ^ (k + 6) * a := Nat.mul_le_mul_right _ h1
        _ ≤ 2 ^ (35 * E) := hA
        _ ≤ 2 ^ (68 * E) := h2
    have haD : a + D ≤ 2 ^ (68 * E) := by omega
    have hmain : 2 ^ (k + 6) * (a * (a + D)) * 2 ^ (32 * E + 6) ≤ 2 ^ (135 * E + 6) := by
      calc 2 ^ (k + 6) * (a * (a + D)) * 2 ^ (32 * E + 6)
          = (2 ^ (k + 6) * a) * (a + D) * 2 ^ (32 * E + 6) := by ring
        _ ≤ 2 ^ (35 * E) * 2 ^ (68 * E) * 2 ^ (32 * E + 6) :=
            Nat.mul_le_mul (Nat.mul_le_mul hA haD) le_rfl
        _ = 2 ^ (135 * E + 6) := by rw [← pow_add, ← pow_add]; congr 1; ring
    have hT : 2 ^ (64 * E) ≤ 2 ^ (135 * E + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfin : 2 * (2 ^ (135 * E + 6) + 2 ^ (135 * E + 6)) ≤ 2 ^ (68 * 2 ^ (k + 1)) := by
      have h4 : 2 * (2 ^ (135 * E + 6) + 2 ^ (135 * E + 6)) = 2 ^ (135 * E + 8) := by
        rw [show 135 * E + 8 = (135 * E + 6) + 2 by ring, pow_add]; ring
      have h5 : 68 * 2 ^ (k + 1) = 136 * E := by rw [pow_succ, ← hEdef]; ring
      rw [h4, h5]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * splitStepD k a D ≤ 2 * (2 ^ (k + 6) * (a * (a + D)) * 2 ^ (32 * E + 6) + 2 ^ (64 * E)) :=
          Nat.mul_le_mul_left 2 hstep
      _ ≤ 2 * (2 ^ (135 * E + 6) + 2 ^ (135 * E + 6)) :=
          Nat.mul_le_mul_left 2 (Nat.add_le_add hmain hT)
      _ ≤ 2 ^ (68 * 2 ^ (k + 1)) := hfin

/-- The tight uniform degree in dimension `l`. -/
def uDeg68 (l : Nat) : Nat := 2 ^ (68 * 2 ^ l)

/-- The split degrees fit the tight degree. -/
theorem split_pair_le_uDeg68 {l : Nat} (hl : 2 ≤ l) :
    (splitPair l).1 + (splitPair l).2 + l + 1 ≤ uDeg68 l := by
  unfold uDeg68
  rcases Nat.lt_or_ge l 3 with h | h
  · obtain rfl : l = 2 := by omega
    rw [splitPair_two]
    unfold splitSeed
    have h1 : 2 ^ 132 ≤ 2 ^ 270 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have h2 : 4 * 2 ^ 270 = 2 ^ (68 * 2 ^ 2) := by
      rw [show 68 * 2 ^ 2 = 2 + 270 by norm_num, pow_add]; norm_num
    have h3 : 3 ≤ 2 ^ 270 :=
      le_trans (by norm_num : 3 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    omega
  · obtain ⟨-, -, hA, -⟩ := split_pair_bounds l hl
    have hD := split_pair_tight l h
    set E := 2 ^ l with hEdef
    have hE8 : 8 ≤ E := by
      rw [hEdef]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) h
    have hsplit : 2 ^ (68 * E) = 4 * 2 ^ (68 * E - 2) := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have ha : (splitPair l).1 ≤ 2 ^ (68 * E - 2) := by
      have h1 : (splitPair l).1 ≤ 2 ^ (35 * E) :=
        le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hA
      exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hl1 : l + 1 ≤ 2 ^ (68 * E - 2) := by
      have h1 : l + 1 ≤ 2 ^ (l + 1) := Nat.lt_two_pow_self.le
      have h2 : l + 1 ≤ 68 * E - 2 := by
        have := Nat.lt_two_pow_self (n := l); omega
      exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
    omega

/-- **The class cover in dimension `l` at the tight degree.** -/
theorem polyCoverAt_class68 (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDeg68 l)) (uExp (classV Kc pc l) (uDeg68 l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform hVl ?_
    unfold uDeg68
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · obtain ⟨C⟩ := splitUniformClass_all Kc pc hK hp hlem l hl
    have hfit := split_pair_le_uDeg68 hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDeg68 l) (by omega) (by omega)
      (by omega)
    refine P0.weaken ?_ ?_ ?_
    · intro g t s hg hg1 ht ht1 hs hs1
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
    · intro g t s _ _ _ _ _ _
      exact (uExp_pos_le _ _ g t s).1
    · intro g t s hg hg1 ht ht1 hs hs1
      show (uCount _ _ g t s)⁻¹ ≤ _
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]

end LeanProofs.GowersSzemeredi
