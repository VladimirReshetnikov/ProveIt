import Std

/-!
Explicit fresh coordinate names for the independent-q finite closure kernel.
The distinguished coordinate q is a separate constant satisfying q != o,
as in the 901-bit FEC16-Bq payload. No equation q = nand(o,o) is assumed.
This file checks the assignment/NAND argument only. It is not a Lean proof
of the kernel's consistency calibration or of any binary Turing machine.
All logical assumptions are fields of `Core`, not new axioms.
-/

namespace FiniteKernelSelectorsIndependent

universe u

structure Core (D : Type u) where
  o : D
  q : D
  distinct : q ≠ o
  val : D → D → D
  change : D → D → D → D
  nand : D → D → D
  holds : D → D → Prop
  same : ∀ s j z, val (change s j z) j = z
  other : ∀ s j z i, i ≠ j → val (change s j z) i = val s i
  nand_spec : ∀ s a b, holds s (nand a b) ↔ ¬ (holds s a ∧ holds s b)

variable {D : Type u} (K : Core D)

theorem nand_ne_self (a : D) : K.nand a a ≠ a := by
  intro h
  have hn := K.nand_spec K.o a a
  rw [h] at hn
  by_cases hp : K.holds K.o a
  · exact (hn.mp hp) ⟨hp, hp⟩
  · exact hp (hn.mpr (fun hh => hp hh.1))

def q : D := K.q

theorem q_ne_o : q K ≠ K.o := K.distinct

def diagonal : D :=
  K.change
    (K.change K.o K.o (K.nand (K.val K.o K.o) (K.val K.o K.o)))
    (q K) (K.nand (K.val (q K) (q K)) (K.val (q K) (q K)))

theorem diagonal_at_o :
    K.val (diagonal K) K.o = K.nand (K.val K.o K.o) (K.val K.o K.o) := by
  unfold diagonal
  rw [K.other _ _ _ _ (Ne.symm (q_ne_o K)), K.same]

theorem diagonal_at_q :
    K.val (diagonal K) (q K) = K.nand (K.val (q K) (q K)) (K.val (q K) (q K)) := by
  unfold diagonal
  exact K.same _ _ _

theorem diagonal_ne_o : diagonal K ≠ K.o := by
  intro h
  have hv := diagonal_at_o K
  rw [h] at hv
  exact nand_ne_self K (K.val K.o K.o) hv.symm

theorem diagonal_ne_q : diagonal K ≠ q K := by
  intro h
  have hv := diagonal_at_q K
  rw [h] at hv
  exact nand_ne_self K (K.val (q K) (q K)) hv.symm

def shift (x : D) : D := K.change (diagonal K) (diagonal K) x

theorem shift_injective {x y : D} (h : shift K x = shift K y) : x = y := by
  have hv := congrArg (fun s => K.val s (diagonal K)) h
  simpa only [shift, K.same] using hv

theorem shift_ne_o (x : D) : shift K x ≠ K.o := by
  intro h
  have hv : K.val (shift K x) K.o = K.nand (K.val K.o K.o) (K.val K.o K.o) := by
    rw [shift, K.other _ _ _ _ (Ne.symm (diagonal_ne_o K)), diagonal_at_o]
  rw [h] at hv
  exact nand_ne_self K (K.val K.o K.o) hv.symm

theorem shift_ne_q (x : D) : shift K x ≠ q K := by
  intro h
  have hv : K.val (shift K x) (q K) =
      K.nand (K.val (q K) (q K)) (K.val (q K) (q K)) := by
    rw [shift, K.other _ _ _ _ (Ne.symm (diagonal_ne_q K)), diagonal_at_q]
  rw [h] at hv
  exact nand_ne_self K (K.val (q K) (q K)) hv.symm

def name : Nat → D
  | 0 => K.o
  | n + 1 => shift K (name n)

theorem names_injective (n m : Nat) (h : name K n = name K m) : n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => exact False.elim (shift_ne_o K (name K m) h.symm)
  | succ n ih =>
    cases m with
    | zero => exact False.elim (shift_ne_o K (name K n) h)
    | succ m => exact congrArg Nat.succ (ih m (shift_injective K h))

theorem names_avoid_q (n : Nat) : name K n ≠ q K := by
  cases n with
  | zero => exact Ne.symm (q_ne_o K)
  | succ n => exact shift_ne_q K (name K n)

#print axioms nand_ne_self
#print axioms names_injective
#print axioms names_avoid_q

end FiniteKernelSelectorsIndependent
