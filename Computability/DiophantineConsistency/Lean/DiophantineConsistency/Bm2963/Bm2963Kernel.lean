import DiophantineConsistency.ArithmeticMaskKernel
import DiophantineConsistency.Bm2963.Bm2963MaskData
import Mathlib.Algebra.BigOperators.Fin

/-! # The block-mask2963 kernel, as a term sum

The block-mask2963 counterpart of `Adm942Kernel` (`CurrentKernelData2011`,
`ArithmeticMaskKernel`; `research/low-padding-independent/PROOF.md` §3):

  `K = ρ^18 + ρ^1005 + ρ^(L+9) + Σ_e c_e ρ^(1956−e)`,

`L = 2963`, `ρ^(L+9) = B·D_R` with `D_R = ρ^9`. The 976 weighted entries are
the 2011 ones (`CurrentKernel2011.Entry`, `CurrentKernel2011.weight`: the 942
`WangTiles942` selector weights and the 34 label weights), with the 2011 label
positions `942/960/969/978` and every selector at its index `j`, exactly as in
admissible942. The clause is **one** reflected band at `1956` with coefficient
`c_e` (admissible942 had two, at `1992` and `2998`). So the coefficient mass is
`3 + Σ c_e = 3829914518400945`.

The exponents are pairwise distinct: the band occupies `[971,1956]`, the bare
terms are `18, 1005, 2972`, and the bare `1005` is not a band exponent because
no entry sits at position `951`. `check_recipe.py` rebuilds `K` from this term
list and matches the pinned payload. -/
set_option autoImplicit false
set_option Elab.async false

namespace Bm2963Kernel
open DiophantineConsistency DiophantineConsistency.WangTiles942
open scoped BigOperators

abbrev radix : ℕ := Bm2963MaskData.radix

/-- The 976 weighted entries, as in 2011: 942 selectors, then west, north, east,
south label bits. -/
abbrev Entry := CurrentKernel2011.Entry

/-- Selectors sit at their index; the labels at the 2011 positions. -/
def position : Entry → ℕ
  | .inl i => i.val
  | .inr (.inl j) => 978 + j.val -- west
  | .inr (.inr (.inl j)) => 960 + j.val -- north
  | .inr (.inr (.inr (.inl j))) => 969 + j.val -- east
  | .inr (.inr (.inr (.inr j))) => 942 + j.val -- south

/-- The coefficient `c_e` of an entry; identical to the 2011 weight. -/
abbrev weight : Entry → ℕ := CurrentKernel2011.weight

/-- The three bare terms, then the single band (`1956`). -/
abbrev Term := Fin 3 ⊕ Entry

def exponent : Term → ℕ
  | .inl j => ![18, 1005, 2972] j
  | .inr e => 1956 - position e

def coefficient : Term → ℕ
  | .inl _ => 1
  | .inr e => CurrentKernel2011.weight e

def rawWord (r : ℕ) : ℕ := ∑ t : Term, coefficient t * r ^ exponent t

def K : ℕ := rawWord radix

/-! ## Positions and exponents -/

theorem position_le (e : Entry) : position e ≤ 985 := by
  rcases e with i | j | j | j | j <;> simp only [position] <;> omega

/-- No entry sits in the gap `951..959`. -/
theorem position_gap (e : Entry) : position e < 951 ∨ 960 ≤ position e := by
  rcases e with i | j | j | j | j <;> simp only [position] <;> omega

theorem position_inSupport (e : Entry) : Bm2963MaskData.InSupport (position e) := by
  unfold Bm2963MaskData.InSupport
  rcases e with i | j | j | j | j <;> simp only [position] <;> omega

theorem position_injective : Function.Injective position := by
  intro a b h
  rcases a with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ <;>
  rcases b with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    simp only [position, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.mk.injEq] at h ⊢ <;>
    omega

private theorem bare_values : ∀ j : Fin 3,
    (![18, 1005, 2972] : Fin 3 → ℕ) j = 18 ∨ (![18, 1005, 2972] : Fin 3 → ℕ) j = 1005 ∨
      (![18, 1005, 2972] : Fin 3 → ℕ) j = 2972 := by decide

private theorem bare_injective : ∀ j j' : Fin 3,
    (![18, 1005, 2972] : Fin 3 → ℕ) j = (![18, 1005, 2972] : Fin 3 → ℕ) j' → j = j' := by
  decide

theorem exponent_le (t : Term) : exponent t ≤ 2972 := by
  rcases t with j | e
  · rcases bare_values j with h | h | h <;> simp only [exponent] <;> omega
  · simp only [exponent]; omega

/-- The band lies in `[971, 1956]`. -/
theorem band (e : Entry) :
    971 ≤ exponent (.inr e) ∧ exponent (.inr e) ≤ 1956 := by
  have := position_le e
  simp only [exponent]; omega

/-- All 979 exponents are distinct. -/
theorem exponent_injective : Function.Injective exponent := by
  intro a b h
  rcases a with j | e <;> rcases b with j' | e' <;>
    simp only [exponent, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢
  · exact bare_injective j j' h
  · have := position_le e'; have := position_gap e'
    rcases bare_values j with h' | h' | h' <;> omega
  · have := position_le e; have := position_gap e
    rcases bare_values j' with h' | h' | h' <;> omega
  · have := position_le e; have := position_le e'; exact position_injective (by omega)

/-! ## The coefficient mass and the expanded kernel -/

theorem coefficient_elim : coefficient =
    Sum.elim (fun _ : Fin 3 => 1) CurrentKernel2011.weight := by
  funext t; rcases t with j | e <;> rfl

/-- `3 + Σ c_e`. A plain `simp` on such goals exhausted memory in admissible942, so
every step is an explicit rewrite. -/
theorem coefficient_mass : (∑ t : Term, coefficient t) = 3829914518400945 := by
  rw [coefficient_elim, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [ArithmeticMaskKernel.entry_mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  all_goals norm_num

/-- The kernel in the recipe form of `PROOF.md` §3, for an arbitrary radix. -/
theorem rawWord_eq (r : ℕ) :
    rawWord r = r^18 + r^1005 + r^2972 +
      ∑ e : Entry, CurrentKernel2011.weight e * r^(1956 - position e) := by
  unfold rawWord
  rw [Fintype.sum_sum_type, Fin.sum_univ_three]
  simp only [exponent, coefficient, one_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

end Bm2963Kernel

#print axioms Bm2963Kernel.position_inSupport
#print axioms Bm2963Kernel.position_injective
#print axioms Bm2963Kernel.exponent_injective
#print axioms Bm2963Kernel.coefficient_mass
#print axioms Bm2963Kernel.rawWord_eq
