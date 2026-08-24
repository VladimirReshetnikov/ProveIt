import DavisEntringerGrahamSimmons1977.Statements
import Mathlib.Data.Fin.VecNotation

/-!
# Modular consequences for Davis--Entringer--Graham--Simmons (1977)

This file proves the paper's elementary lifting observation: an ordinary
three-term-progression-free permutation is automatically free of five-term
progressions modulo the length of its interval.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.DavisEntringerGrahamSimmons1977

private theorem small_int_multiple_cases (n : Nat) (hn : 0 < n) (z : Int)
    (hdiv : (n : Int) ∣ z) (hlower : -2 * (n : Int) < z)
    (hupper : z < 2 * (n : Int)) :
    z = -(n : Int) ∨ z = 0 ∨ z = (n : Int) := by
  obtain ⟨k, hk⟩ := hdiv
  have hn' : (0 : Int) < n := by exact_mod_cast hn
  have hk_lower : (-2 : Int) < k := by
    apply (Int.mul_lt_mul_left hn').mp
    simpa [hk, mul_comm] using hlower
  have hk_upper : k < (2 : Int) := by
    apply (Int.mul_lt_mul_left hn').mp
    simpa [hk, mul_comm] using hupper
  have : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl | rfl
  · simp [hk]
  · simp [hk]
  · simp [hk]

private theorem three_term_progression_of_midpoint (u v w : Int)
    (huv : u ≠ v) (hmid : u + w = 2 * v) :
    IsArithmeticProgression ![u, v, w] := by
  refine ⟨u, v - u, ?_, ?_⟩
  · rw [bne_iff_ne]
    exact sub_ne_zero.mpr huv.symm
  · intro i
    fin_cases i <;> simp
    omega

/-- Five distinct integers in `[1,n]` that form a modular arithmetic
progression contain three terms, in their displayed order, that form an
ordinary arithmetic progression.

The proof examines the three consecutive second differences. Each is a
multiple of `n` strictly between `-2n` and `2n`, hence is `-n`, `0`, or `n`.
If none vanishes, their combination on terms zero, two, and four must vanish.
-/
private theorem five_modular_terms_contain_three
    (n : Nat) (hn : 0 < n) (x : Fin 5 → Int) (hx : Function.Injective x)
    (hxlower : ∀ i, 1 ≤ x i) (hxupper : ∀ i, x i ≤ (n : Int))
    (a d : ZMod n) (hvalues : ∀ i, (x i : ZMod n) = a + (i : Nat) * d) :
    ∃ q : Fin 3 → Fin 5, StrictMono q ∧
      IsArithmeticProgression (fun i => x (q i)) := by
  have h0 := hvalues (0 : Fin 5)
  have h1 := hvalues (1 : Fin 5)
  have h2 := hvalues (2 : Fin 5)
  have h3 := hvalues (3 : Fin 5)
  have h4 := hvalues (4 : Fin 5)
  norm_num at h0 h1 h2 h3 h4
  let δ0 : Int := x 0 - 2 * x 1 + x 2
  let δ1 : Int := x 1 - 2 * x 2 + x 3
  let δ2 : Int := x 2 - 2 * x 3 + x 4
  have hδ0_cast : (δ0 : ZMod n) = 0 := by
    dsimp [δ0]
    push_cast
    rw [h0, h1, h2]
    ring
  have hδ1_cast : (δ1 : ZMod n) = 0 := by
    dsimp [δ1]
    push_cast
    rw [h1, h2, h3]
    ring
  have hδ2_cast : (δ2 : ZMod n) = 0 := by
    dsimp [δ2]
    push_cast
    rw [h2, h3, h4]
    ring
  have hδ0_div : (n : Int) ∣ δ0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd δ0 n).mp hδ0_cast
  have hδ1_div : (n : Int) ∣ δ1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd δ1 n).mp hδ1_cast
  have hδ2_div : (n : Int) ∣ δ2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd δ2 n).mp hδ2_cast
  have hδ0_lower : -2 * (n : Int) < δ0 := by
    dsimp [δ0]
    have hxl0 := hxlower (0 : Fin 5)
    have hxl2 := hxlower (2 : Fin 5)
    have hxu1 := hxupper (1 : Fin 5)
    omega
  have hδ0_upper : δ0 < 2 * (n : Int) := by
    dsimp [δ0]
    have hxu0 := hxupper (0 : Fin 5)
    have hxu2 := hxupper (2 : Fin 5)
    have hxl1 := hxlower (1 : Fin 5)
    omega
  have hδ1_lower : -2 * (n : Int) < δ1 := by
    dsimp [δ1]
    have hxl1 := hxlower (1 : Fin 5)
    have hxl3 := hxlower (3 : Fin 5)
    have hxu2 := hxupper (2 : Fin 5)
    omega
  have hδ1_upper : δ1 < 2 * (n : Int) := by
    dsimp [δ1]
    have hxu1 := hxupper (1 : Fin 5)
    have hxu3 := hxupper (3 : Fin 5)
    have hxl2 := hxlower (2 : Fin 5)
    omega
  have hδ2_lower : -2 * (n : Int) < δ2 := by
    dsimp [δ2]
    have hxl2 := hxlower (2 : Fin 5)
    have hxl4 := hxlower (4 : Fin 5)
    have hxu3 := hxupper (3 : Fin 5)
    omega
  have hδ2_upper : δ2 < 2 * (n : Int) := by
    dsimp [δ2]
    have hxu2 := hxupper (2 : Fin 5)
    have hxu4 := hxupper (4 : Fin 5)
    have hxl3 := hxlower (3 : Fin 5)
    omega
  have hδ0_cases :=
    small_int_multiple_cases n hn δ0 hδ0_div hδ0_lower hδ0_upper
  have hδ1_cases :=
    small_int_multiple_cases n hn δ1 hδ1_div hδ1_lower hδ1_upper
  have hδ2_cases :=
    small_int_multiple_cases n hn δ2 hδ2_div hδ2_lower hδ2_upper
  by_cases hδ0_zero : δ0 = 0
  · refine ⟨![0, 1, 2], by decide, ?_⟩
    convert three_term_progression_of_midpoint (x 0) (x 1) (x 2)
      (hx.ne (by decide)) (by dsimp [δ0] at hδ0_zero; omega) using 1
    funext i
    fin_cases i <;> rfl
  by_cases hδ1_zero : δ1 = 0
  · refine ⟨![1, 2, 3], by decide, ?_⟩
    convert three_term_progression_of_midpoint (x 1) (x 2) (x 3)
      (hx.ne (by decide)) (by dsimp [δ1] at hδ1_zero; omega) using 1
    funext i
    fin_cases i <;> rfl
  by_cases hδ2_zero : δ2 = 0
  · refine ⟨![2, 3, 4], by decide, ?_⟩
    convert three_term_progression_of_midpoint (x 2) (x 3) (x 4)
      (hx.ne (by decide)) (by dsimp [δ2] at hδ2_zero; omega) using 1
    funext i
    fin_cases i <;> rfl
  have hδ0_sign : δ0 = -(n : Int) ∨ δ0 = (n : Int) := by
    rcases hδ0_cases with h | h | h
    · exact Or.inl h
    · exact (hδ0_zero h).elim
    · exact Or.inr h
  have hδ1_sign : δ1 = -(n : Int) ∨ δ1 = (n : Int) := by
    rcases hδ1_cases with h | h | h
    · exact Or.inl h
    · exact (hδ1_zero h).elim
    · exact Or.inr h
  have hδ2_sign : δ2 = -(n : Int) ∨ δ2 = (n : Int) := by
    rcases hδ2_cases with h | h | h
    · exact Or.inl h
    · exact (hδ2_zero h).elim
    · exact Or.inr h
  let ε : Int := x 0 - 2 * x 2 + x 4
  have hε_lower : -2 * (n : Int) < ε := by
    dsimp [ε]
    have hxl0 := hxlower (0 : Fin 5)
    have hxl4 := hxlower (4 : Fin 5)
    have hxu2 := hxupper (2 : Fin 5)
    omega
  have hε_upper : ε < 2 * (n : Int) := by
    dsimp [ε]
    have hxu0 := hxupper (0 : Fin 5)
    have hxu4 := hxupper (4 : Fin 5)
    have hxl2 := hxlower (2 : Fin 5)
    omega
  have hε_identity : ε = δ0 + 2 * δ1 + δ2 := by
    dsimp [ε, δ0, δ1, δ2]
    ring
  have hε_zero : ε = 0 := by
    rcases hδ0_sign with hδ0 | hδ0 <;>
      rcases hδ1_sign with hδ1 | hδ1 <;>
      rcases hδ2_sign with hδ2 | hδ2 <;> omega
  refine ⟨![0, 2, 4], by decide, ?_⟩
  convert three_term_progression_of_midpoint (x 0) (x 2) (x 4)
    (hx.ne (by decide)) (by dsimp [ε] at hε_zero; omega) using 1
  funext i
  fin_cases i <;> rfl

theorem ordinary_three_free_implies_modular_five_free_holds :
    ordinary_three_free_implies_modular_five_free := by
  intro n p hthree hfive
  apply hthree
  obtain ⟨pos, hpos, a, d, _hd, hvalues⟩ := hfive
  have hn : 0 < n := by
    have := pos (0 : Fin 5)
    exact Nat.zero_lt_of_lt this.isLt
  let x : Fin 5 → Int := fun i => finitePermutationSequence p (pos i)
  have hx : Function.Injective x := by
    intro i j hij
    apply hpos.injective
    apply p.injective
    apply Fin.ext
    dsimp [x, finitePermutationSequence] at hij
    omega
  have hxlower : ∀ i, 1 ≤ x i := by
    intro i
    dsimp [x, finitePermutationSequence]
    omega
  have hxupper : ∀ i, x i ≤ (n : Int) := by
    intro i
    dsimp [x, finitePermutationSequence]
    have := (p (pos i)).isLt
    omega
  have hxvalues : ∀ i, (x i : ZMod n) = a + (i : Nat) * d := by
    intro i
    simpa [x, finitePermutationSequence, finiteModValue] using hvalues i
  obtain ⟨q, hq, hprogression⟩ :=
    five_modular_terms_contain_three n hn x hx hxlower hxupper a d hxvalues
  exact ⟨fun i => pos (q i), hpos.comp hq, hprogression⟩

end LeanProofs.DavisEntringerGrahamSimmons1977
