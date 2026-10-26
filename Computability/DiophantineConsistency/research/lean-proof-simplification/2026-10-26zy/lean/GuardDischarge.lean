import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Defs

/-! Newly checked arithmetic and equivalence utilities. The two literal row tables
below are copied from the pinned source; full project imports are not replayed. -/

namespace EndogenousGuard

/-- A guard obtainable from either domain element need not be an external
parameter of the equivalence. Proof irrelevance aligns the inverse proofs. -/
def discharge {A B : Type*} {G : Prop} (e : G → A ≃ B)
    (ga : A → G) (gb : B → G) : A ≃ B where
  toFun a := e (ga a) a
  invFun b := (e (gb b)).symm b
  left_inv a := (e (ga a)).left_inv a
  right_inv b := (e (gb b)).right_inv b

/-- Shared sign argument. The final factor D is either L or 1+L. -/
theorem beta_pos_kernel {β J L N D : ℤ}
    (hJ : 0 ≤ J) (hL : 0 < L) (hN : 0 < N) (hD : 0 < D)
    (hquad : L = (1 + β * J)^2 - 1)
    (hlinear : N = (1 + β * J) * D) : 0 < β := by
  have hq : (0 : ℤ) < 1 + β * J :=
    (mul_pos_iff_of_pos_right hD).mp (hlinear ▸ hN)
  have hq1 : (1 : ℤ) < 1 + β * J := by
    by_contra h
    have he : (1 : ℤ) + β * J = 1 := by omega
    rw [he] at hquad
    norm_num at hquad
    omega
  have hp : 0 < β * J := by omega
  exact pos_of_mul_pos_left hp hJ

/-- Gap row 1 is N=qL. -/
theorem gap_rows_beta_pos {β J L N : ℤ}
    (hJ : 0 ≤ J) (hL : 0 < L) (hN : 0 < N)
    (hzero : L + ((-2) * β) * J + (-(β ^ 2)) * (J ^ 2) = 0)
    (hone : (-1) * L + N + (-β) * (J * L) = 0) : 0 < β := by
  apply beta_pos_kernel (D := L) hJ hL hN hL
  · linear_combination hzero
  · linear_combination hone

/-- Old row 1 is N=q(1+L). -/
theorem old_rows_beta_pos {β J L N : ℤ}
    (hJ : 0 ≤ J) (hL : 0 < L) (hN : 0 < N)
    (hzero : L + ((-2) * β) * J + (-(β ^ 2)) * (J ^ 2) = 0)
    (hone : (-1) + (-1) * L + N + (-β) * J + (-β) * (J * L) = 0) : 0 < β := by
  apply beta_pos_kernel (D := 1 + L) hJ hL hN (by omega)
  · linear_combination hzero
  · linear_combination hone

end EndogenousGuard

namespace PinnedGap
variable {R : Type*} [CommRing R]
def rows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=
  ![(x 24 + ((-2) * ports 0) * (x 0) + ((-(ports 0 ^ 2))) * (x 0 ^ 2)),
    ((-1) * (x 24) + x 16 + ((-(ports 0))) * (x 0 * x 24)),
    (x 21 + (-1) * (x 10) + ((-(ports 0))) * (x 0 * x 10)),
    (x 20 + (-1) * (x 17) + (-1) * (x 9) + (-1) * (x 9 * x 16) + ((-(ports 0))) * (x 0 * x 9)),
    ((-1) * (x 20 * x 21) + x 17 + x 17 * x 21),
    (x 19 + (-1) * (x 13 * x 20) + x 13 * x 17 + (-1) * (x 12) + (-1) * (x 12 * x 20) + x 12 * x 17),
    (x 18 + (-1) * (x 17 * x 19) + x 12 * x 17),
    ((-1) + (-1) * (x 18 ^ 2) + (-1) * (x 13 * x 18) + (-1) * (x 12 * x 18) + x 11 ^ 2),
    (x 22 + (-1) * (x 21) + (-1) * (x 19 * x 20) + (-3) * (x 15) + (-4) * (x 15 * x 20)),
    ((-3) + x 30 + (-4) * (x 20) + (-1) * (x 20 ^ 2)),
    (x 23 + (-1) * (x 19 ^ 2)),
    ((-1) + (-1) * (x 23 * x 30) + x 22 ^ 2),
    ((-1) + x 26 + x 13 + x 12 + (-1) * (x 8 * x 19) + (-1) * (x 5 * x 17)),
    ((-1) * (x 26) + x 8 * x 19 + (-1) * (x 2 * x 24) + (-1) * (x 1 * x 24) + x 1 * x 16 + ((-(ports 3)) + (-(ports 2))) * (x 0) + ((-(ports 0))) * (x 0 * x 16) + ((-(ports 0 * ports 3))) * (x 0 ^ 2)),
    ((ports 1) + x 21 + ((-(ports 1))) * (x 2) + (-1) * (x 2 * x 10) + (-1 + (-(ports 1))) * (x 1) + (-1) * (x 1 * x 10) + (ports 0 + ports 0 * ports 1) * (x 0) + ((-(ports 0))) * (x 0 * x 3)),
    (x 25 + (-1) * (x 4 ^ 2)),
    (x 26 + x 19 + (-1) * (x 4 * x 7)),
    (x 27 + x 26 ^ 2 + (-1) * (x 14 ^ 2)),
    (x 28 + (-1) * (x 6 * x 23)),
    (x 29 + (-1) * (x 28 ^ 2)),
    (x 30 + x 29 + (-1) * (x 25 * x 30)),
    ((-1) + (-1) * (x 27 * x 29) + x 14 ^ 2)]
end PinnedGap

namespace PinnedOld
variable {R : Type*} [CommRing R]
def sourceRows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=
  ![(x 24 + ((-2) * ports 0) * (x 0) + ((-(ports 0 ^ 2))) * (x 0 ^ 2)),
    ((-1) + (-1) * (x 24) + x 16 + ((-(ports 0))) * (x 0) + ((-(ports 0))) * (x 0 * x 24)),
    (x 21 + (-1) * (x 10) + ((-(ports 0))) * (x 0 * x 10)),
    (x 20 + (-1) * (x 17) + (-1) * (x 9 * x 16)),
    ((-1) * (x 20 * x 21) + x 17 + x 17 * x 21),
    (x 19 + (-1) * (x 13 * x 20) + x 13 * x 17 + (-1) * (x 12) + (-1) * (x 12 * x 20) + x 12 * x 17),
    (x 18 + (-1) * (x 17 * x 19) + (-1) * (x 13) + (-1) * (x 12) + x 12 * x 17),
    ((-1) + (-1) * (x 18 ^ 2) + x 13 * x 18 + x 12 * x 18 + x 11 ^ 2),
    (x 22 + (-1) * (x 21) + (-1) * (x 19 * x 20) + (-3) * (x 15) + (-4) * (x 15 * x 20)),
    ((-3) + x 30 + (-4) * (x 20) + (-1) * (x 20 ^ 2)),
    (x 23 + (-1) * (x 19 ^ 2)),
    ((-1) + (-1) * (x 23 * x 30) + x 22 ^ 2),
    ((-1) + x 26 + x 13 + x 12 + (-1) * (x 8 * x 19) + (-1) * (x 5 * x 17)),
    ((1) + (-1) * (x 26) + x 24 + (-1) * (x 16) + x 8 * x 19 + (-1) * (x 2 * x 24) + (-1) * (x 1) + (-1) * (x 1 * x 24) + x 1 * x 16 + ((-(ports 3)) + (-(ports 2)) + (2) * ports 0) * (x 0) + (ports 0) * (x 0 * x 24) + ((-(ports 0))) * (x 0 * x 16) + ((-(ports 0))) * (x 0 * x 1) + ((-(ports 0 * ports 3)) + ports 0 ^ 2) * (x 0 ^ 2)),
    ((ports 1) + x 10 + ((-(ports 1))) * (x 2) + (-1) * (x 2 * x 10) + (-1 + (-(ports 1))) * (x 1) + (-1) * (x 1 * x 10) + (ports 0 + ports 0 * ports 1) * (x 0) + (ports 0) * (x 0 * x 10) + ((-(ports 0))) * (x 0 * x 3)),
    (x 25 + (-1) * (x 4 ^ 2)),
    (x 26 + x 19 + (-1) * (x 4 * x 7)),
    (x 27 + x 26 ^ 2 + (-1) * (x 14 ^ 2)),
    (x 28 + (-1) * (x 6 * x 23)),
    (x 29 + (-1) * (x 28 ^ 2)),
    (x 30 + x 29 + (-1) * (x 25 * x 30)),
    ((-1) + (-1) * (x 27 * x 29) + x 14 ^ 2)]
end PinnedOld

namespace EndogenousGuard

def Positive (x : Fin 31 → ℤ) : Prop := ∀ i, 0 < x i

theorem gap_beta_pos (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ)
    (hx : Positive x) (hz : ∀ k, PinnedGap.rows ports x k = 0) : 0 < ports 0 := by
  exact gap_rows_beta_pos (hx 0).le (hx 24) (hx 16) (hz 0) (hz 1)

theorem old_beta_pos (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ)
    (hx : Positive x) (hz : ∀ k, PinnedOld.sourceRows ports x k = 0) : 0 < ports 0 := by
  exact old_rows_beta_pos (hx 0).le (hx 24) (hx 16) (hz 0) (hz 1)

abbrev GapZeros (ports : Fin 4 → ℤ) :=
  {x : Fin 31 → ℤ // Positive x ∧ ∀ k, PinnedGap.rows ports x k = 0}
abbrev OldZeros (ports : Fin 4 → ℤ) :=
  {x : Fin 31 → ℤ // Positive x ∧ ∀ k, PinnedOld.sourceRows ports x k = 0}

/-- Here e is the existing maintained positiveZeroEquiv. This theorem checks
all new reasoning while leaving that established equivalence as a parameter. -/
def unguard (ports : Fin 4 → ℤ)
    (e : 0 < ports 0 → GapZeros ports ≃ OldZeros ports) :
    GapZeros ports ≃ OldZeros ports :=
  discharge e (fun x => gap_beta_pos ports x x.property.1 x.property.2)
    (fun x => old_beta_pos ports x x.property.1 x.property.2)

theorem unguard_exists (ports : Fin 4 → ℤ)
    (e : 0 < ports 0 → GapZeros ports ≃ OldZeros ports) :
    (∃ x, Positive x ∧ ∀ k, PinnedGap.rows ports x k = 0) ↔
      ∃ x, Positive x ∧ ∀ k, PinnedOld.sourceRows ports x k = 0 :=
  (unguard ports e).exists_subtype_congr

/-- For nonpositive beta both positive solution spaces are empty. -/
theorem no_gap_solution_of_beta_nonpos (ports : Fin 4 → ℤ) (hβ : ports 0 ≤ 0) :
    ¬ ∃ x, Positive x ∧ ∀ k, PinnedGap.rows ports x k = 0 := by
  rintro ⟨x, hx, hz⟩
  exact (not_lt_of_ge hβ) (gap_beta_pos ports x hx hz)

theorem no_old_solution_of_beta_nonpos (ports : Fin 4 → ℤ) (hβ : ports 0 ≤ 0) :
    ¬ ∃ x, Positive x ∧ ∀ k, PinnedOld.sourceRows ports x k = 0 := by
  rintro ⟨x, hx, hz⟩
  exact (not_lt_of_ge hβ) (old_beta_pos ports x hx hz)

#print axioms discharge
#print axioms beta_pos_kernel
#print axioms gap_beta_pos
#print axioms old_beta_pos
#print axioms unguard
#print axioms unguard_exists
#print axioms no_gap_solution_of_beta_nonpos
#print axioms no_old_solution_of_beta_nonpos
end EndogenousGuard
