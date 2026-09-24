import Diophantine.Paper1980.CounterMacros100
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Tape halves as counter values

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`, §§2–3: *"Give every tape symbol a
distinct positive code, including blank.  Let b be one larger than the number of tape
symbols. ...  Every stored stack digit is a positive symbol code.  An empty stack has value
zero and popping it returns blank without changing any counter.  Thus absent cells are blank,
while explicit blank digits may also be stored."*

A stack number `n` in base `b = |Γ| + 2` with nonzero digits (`Good n`) represents the list of
the symbols of its digits, lowest digit first (`stk n`), up to trailing blanks.  Popping reads
the head of that tape half and leaves its tail; pushing a code conses a symbol.

`loadB` is §2's loader: it pops the binary digits of `a` from the least significant and pushes
their symbols, so the most significant digit ends on top.
-/

namespace Jones1980

open Turing

namespace TMStack

variable (Γ : Type) [Inhabited Γ] [Fintype Γ]

/-- The stack base `b = |Γ| + 2` (one spare digit keeps `b ≥ 2` without a symbol). -/
def base : ℕ := Fintype.card Γ + 2

theorem two_le_base : 2 ≤ base Γ := by
  unfold base; omega

variable {Γ}

/-- The positive code of a symbol. -/
noncomputable def code (a : Γ) : ℕ := (Fintype.equivFin Γ a : ℕ) + 1

/-- The symbol of a digit, blank for zero. -/
noncomputable def sym (j : ℕ) : Γ :=
  if h : 1 ≤ j ∧ j - 1 < Fintype.card Γ then (Fintype.equivFin Γ).symm ⟨j - 1, h.2⟩ else default

theorem code_pos (a : Γ) : 1 ≤ code a := by unfold code; omega

theorem code_lt (a : Γ) : code a < base Γ := by
  unfold code base
  have := (Fintype.equivFin Γ a).isLt
  omega

theorem sym_code (a : Γ) : sym (code a) = a := by
  unfold sym code
  have h : 1 ≤ (Fintype.equivFin Γ a : ℕ) + 1 ∧
      (Fintype.equivFin Γ a : ℕ) + 1 - 1 < Fintype.card Γ :=
    ⟨by omega, by have := (Fintype.equivFin Γ a).isLt; omega⟩
  rw [dif_pos h]
  apply (Fintype.equivFin Γ).symm_apply_eq.2
  ext
  simp

theorem sym_zero : sym (Γ := Γ) 0 = default := by
  unfold sym; rw [dif_neg (by omega)]

/-- The symbols of a stack number, nearest first. -/
noncomputable def stk (n : ℕ) : List Γ :=
  if h : n = 0 then [] else sym (n % base Γ) :: stk (n / base Γ)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by unfold base; omega)

theorem stk_zero : stk (Γ := Γ) 0 = [] := by rw [stk]; simp

theorem stk_ne {n : ℕ} (hn : n ≠ 0) : stk (Γ := Γ) n = sym (n % base Γ) :: stk (n / base Γ) := by
  rw [stk, dif_neg hn]

variable (Γ) in
/-- A stack number all of whose digits are nonzero. -/
def Good (n : ℕ) : Prop := ∀ i, (n / base Γ ^ i) % base Γ = 0 → n / base Γ ^ i = 0

theorem good_zero : Good Γ 0 := fun i _ => by simp

theorem good_eq_zero {n : ℕ} (h : Good Γ n) (h0 : n % base Γ = 0) : n = 0 := by
  have := h 0
  simp only [pow_zero, Nat.div_one] at this
  exact this h0

theorem good_div {n : ℕ} (h : Good Γ n) : Good Γ (n / base Γ) := fun i hi => by
  rw [Nat.div_div_eq_div_mul, ← pow_succ'] at hi ⊢
  exact h (i + 1) hi

theorem good_push {n d : ℕ} (h : Good Γ n) (hd : 1 ≤ d) (hdb : d < base Γ) :
    Good Γ (base Γ * n + d) := by
  have hb := two_le_base Γ
  intro i hi
  rcases i with _ | i
  · simp only [pow_zero, Nat.div_one] at hi ⊢
    rw [show base Γ * n + d = d + base Γ * n by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hdb] at hi
    omega
  · have e : (base Γ * n + d) / base Γ ^ (i + 1) = n / base Γ ^ i := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul, show base Γ * n + d = d + base Γ * n by ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hdb, Nat.zero_add]
    rw [e] at hi ⊢
    exact h i hi

theorem head_stk {n : ℕ} (h : Good Γ n) :
    (ListBlank.mk (stk (Γ := Γ) n)).head = sym (n % base Γ) := by
  rw [ListBlank.head_mk]
  by_cases hn : n = 0
  · subst hn; rw [stk_zero, Nat.zero_mod, sym_zero]; rfl
  · rw [stk_ne hn]; rfl

theorem tail_stk (n : ℕ) :
    (ListBlank.mk (stk (Γ := Γ) n)).tail = ListBlank.mk (stk (n / base Γ)) := by
  rw [ListBlank.tail_mk]
  by_cases hn : n = 0
  · subst hn; rw [Nat.zero_div, stk_zero]; rfl
  · rw [stk_ne hn]; rfl

theorem stk_push (n : ℕ) (a : Γ) : stk (Γ := Γ) (base Γ * n + code a) = a :: stk n := by
  have hb := two_le_base Γ
  have hc := code_lt a
  rw [stk_ne (by have := code_pos a; omega), show base Γ * n + code a = code a + base Γ * n by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc, sym_code,
    Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem cons_stk (n : ℕ) (a : Γ) :
    (ListBlank.mk (stk (Γ := Γ) n)).cons a = ListBlank.mk (stk (base Γ * n + code a)) := by
  rw [ListBlank.cons_mk, stk_push]

/-! ### The loader -/

/-- The binary digits of `a`, least significant first. -/
def lsbBits (a : ℕ) : List Bool :=
  if h : a = 0 then [] else decide (a % 2 = 1) :: lsbBits (a / 2)
termination_by a
decreasing_by omega

/-- The stack after loading the binary digits of `a` on top of `n`. -/
noncomputable def loadB (enc : Bool → Γ) (a n : ℕ) : ℕ :=
  if h : a = 0 then n else loadB enc (a / 2) (base Γ * n + code (enc (decide (a % 2 = 1))))
termination_by a
decreasing_by omega

theorem loadB_spec (enc : Bool → Γ) : ∀ a n, Good Γ n →
    Good Γ (loadB enc a n) ∧ stk (loadB enc a n) = (lsbBits a).reverse.map enc ++ stk n := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro n hn
    by_cases ha : a = 0
    · subst ha
      rw [loadB, dif_pos rfl, lsbBits, dif_pos rfl]
      exact ⟨hn, by simp⟩
    · rw [loadB, dif_neg ha, lsbBits, dif_neg ha]
      obtain ⟨h1, h2⟩ := ih (a / 2) (by omega) _
        (good_push hn (code_pos _) (code_lt _))
      refine ⟨h1, ?_⟩
      rw [h2, stk_push]
      simp

end TMStack

end Jones1980
