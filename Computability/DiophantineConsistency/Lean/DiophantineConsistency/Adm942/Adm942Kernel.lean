import DiophantineConsistency.ArithmeticMaskKernel
import DiophantineConsistency.Adm942.Adm942MaskData
import Mathlib.Algebra.BigOperators.Fin

/-! # The admissible942 kernel, as a term sum

The admissible942 counterpart of `CurrentKernelData2011` and
`ArithmeticMaskKernel` (`research/admissible942-independent/PROOF.md` §3):

  `K = ρ^18 + ρ^1005 + ρ^(L+9) + Σ_e c_e (ρ^(1992−e) + ρ^(2998−e))`,

`L = 4027`, `ρ^(L+9) = B·D_R` with `D_R = ρ^9`. The 976 weighted entries are
the 2011 ones (`CurrentKernel2011.Entry`, `CurrentKernel2011.weight`: the 942
`WangTiles942` selector weights and the 34 label weights), with the 2011 label
positions `942/960/969/978` but with every selector at its index `j` (2011
used the sorted `physicalPosition`). The clause is two reflected bands at
`1992` and `2998` with coefficient `c_e` each, instead of the 2011 doubled band
at `1005`. So the coefficient mass `3 + 2·Σ c_e` is the 2011 mass
`7659829036801887`.

The exponents are pairwise distinct: the bands occupy `[1007,1992]` and
`[2013,2998]`, the bare terms are `18, 1005, 4036`. `check_ports.py` rebuilds
`K` from this term list and matches the pinned payload. -/
set_option autoImplicit false
set_option Elab.async false

namespace Adm942Kernel
open DiophantineConsistency DiophantineConsistency.WangTiles942
open scoped BigOperators

abbrev radix : ℕ := Adm942MaskData.radix

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

/-- The three bare terms, then the lower band (`1992`), then the upper band (`2998`). -/
abbrev Term := Fin 3 ⊕ (Entry ⊕ Entry)

def exponent : Term → ℕ
  | .inl j => ![18, 1005, 4036] j
  | .inr (.inl e) => 1992 - position e
  | .inr (.inr e) => 2998 - position e

def coefficient : Term → ℕ
  | .inl _ => 1
  | .inr (.inl e) => CurrentKernel2011.weight e
  | .inr (.inr e) => CurrentKernel2011.weight e

def rawWord (r : ℕ) : ℕ := ∑ t : Term, coefficient t * r ^ exponent t

def K : ℕ := rawWord radix

/-! ## Positions and exponents -/

theorem position_le (e : Entry) : position e ≤ 985 := by
  rcases e with i | j | j | j | j <;> simp only [position] <;> omega

theorem position_inSupport (e : Entry) : Adm942MaskData.InSupport (position e) := by
  unfold Adm942MaskData.InSupport
  rcases e with i | j | j | j | j <;> simp only [position] <;> omega

theorem position_injective : Function.Injective position := by
  intro a b h
  rcases a with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ <;>
  rcases b with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    simp only [position, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.mk.injEq] at h ⊢ <;>
    omega

private theorem bare_values : ∀ j : Fin 3,
    (![18, 1005, 4036] : Fin 3 → ℕ) j = 18 ∨ (![18, 1005, 4036] : Fin 3 → ℕ) j = 1005 ∨
      (![18, 1005, 4036] : Fin 3 → ℕ) j = 4036 := by decide

private theorem bare_injective : ∀ j j' : Fin 3,
    (![18, 1005, 4036] : Fin 3 → ℕ) j = (![18, 1005, 4036] : Fin 3 → ℕ) j' → j = j' := by
  decide

theorem exponent_le (t : Term) : exponent t ≤ 4036 := by
  rcases t with j | e | e
  · rcases bare_values j with h | h | h <;> simp only [exponent] <;> omega
  · simp only [exponent]; omega
  · simp only [exponent]; omega

/-- The lower band lies in `[1007, 1992]`. -/
theorem lower_band (e : Entry) :
    1007 ≤ exponent (.inr (.inl e)) ∧ exponent (.inr (.inl e)) ≤ 1992 := by
  have := position_le e
  simp only [exponent]; omega

/-- The upper band lies in `[2013, 2998]`. -/
theorem upper_band (e : Entry) :
    2013 ≤ exponent (.inr (.inr e)) ∧ exponent (.inr (.inr e)) ≤ 2998 := by
  have := position_le e
  simp only [exponent]; omega

/-- All 1955 exponents are distinct. -/
theorem exponent_injective : Function.Injective exponent := by
  intro a b h
  rcases a with j | e | e <;> rcases b with j' | e' | e' <;>
    simp only [exponent, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢
  · exact bare_injective j j' h
  · have := position_le e'; rcases bare_values j with h' | h' | h' <;> omega
  · have := position_le e'; rcases bare_values j with h' | h' | h' <;> omega
  · have := position_le e; rcases bare_values j' with h' | h' | h' <;> omega
  · have := position_le e; have := position_le e'; exact position_injective (by omega)
  · have := position_le e; have := position_le e'; omega
  · have := position_le e; rcases bare_values j' with h' | h' | h' <;> omega
  · have := position_le e; have := position_le e'; omega
  · have := position_le e; have := position_le e'; exact position_injective (by omega)

/-! ## The coefficient mass and the expanded kernel -/

theorem coefficient_elim : coefficient =
    Sum.elim (fun _ : Fin 3 => 1) (Sum.elim CurrentKernel2011.weight CurrentKernel2011.weight) := by
  funext t; rcases t with j | e | e <;> rfl

/-- The 2011 mass. A plain `simp` closing this goal exhausted memory, so every
step is an explicit rewrite. -/
theorem coefficient_mass : (∑ t : Term, coefficient t) = 7659829036801887 := by
  rw [coefficient_elim, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [ArithmeticMaskKernel.entry_mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  norm_num

/-- The kernel in the recipe form of `PROOF.md` §3, for an arbitrary radix. -/
theorem rawWord_eq (r : ℕ) :
    rawWord r = r^18 + r^1005 + r^4036 +
      ∑ e : Entry, CurrentKernel2011.weight e * (r^(1992 - position e) + r^(2998 - position e)) := by
  unfold rawWord
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_three]
  simp only [exponent, coefficient, one_mul, mul_add, Finset.sum_add_distrib]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

end Adm942Kernel

#print axioms Adm942Kernel.position_inSupport
#print axioms Adm942Kernel.position_injective
#print axioms Adm942Kernel.exponent_injective
#print axioms Adm942Kernel.coefficient_mass
#print axioms Adm942Kernel.rawWord_eq
