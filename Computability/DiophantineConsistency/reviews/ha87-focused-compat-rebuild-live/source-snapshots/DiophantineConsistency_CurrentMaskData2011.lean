import DiophantineConsistency.LowMaskData
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IrreducibleDef

/-! Exact current mask data; no source-window, population or machine premise. -/
namespace DiophantineConsistency.CurrentMasks2011
open LowMaskCoding
set_option Elab.async false

def radix : ℕ := 2 ^ 47

def width : ℕ := 47 * 2011

def beta : ℕ := radix ^ 2011 - 1

irreducible_def lowSupport : Finset ℕ := Finset.range 951 ∪ Finset.Ico 960 986 ∪ {1004}

/-- The two nontrivial components of the low-mask support are disjoint. -/
theorem lowSupport_range_Ico_disjoint :
    Disjoint (Finset.range 951) (Finset.Ico 960 986) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  simp only [Finset.mem_range, Finset.mem_Ico] at hj hk
  omega

/-- The marker is outside both preceding support intervals. -/
theorem lowSupport_marker_disjoint :
    Disjoint (Finset.range 951 ∪ Finset.Ico 960 986) ({1004} : Finset ℕ) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton] at hj hk
  omega

def lowPort : ℕ := mask radix 2 2011 lowSupport

/-- All nonzero high-mask digits occur in this1006-digit prefix. -/
def highPrefix : List ℕ :=
  4 :: (List.replicate 916 8 ++ List.replicate 43 0 ++ List.replicate 9 1 ++
    List.replicate 18 0 ++ List.replicate 8 1 ++ List.replicate 9 0 ++ [1, 2 ^ 45 - 4])

def highDigits : List ℕ := highPrefix ++ List.replicate 1005 0

def highPort : ℕ := Nat.ofDigits radix highDigits

def ports (K : ℤ) : Fin 4 → ℤ := ![beta, K, lowPort, highPort + beta]

end DiophantineConsistency.CurrentMasks2011
