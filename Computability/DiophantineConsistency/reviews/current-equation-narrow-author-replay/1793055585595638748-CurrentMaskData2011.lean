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

def lowPort : ℕ := mask radix 2 2011 lowSupport

/-- All nonzero high-mask digits occur in this1006-digit prefix. -/
def highPrefix : List ℕ :=
  4 :: (List.replicate 916 8 ++ List.replicate 43 0 ++ List.replicate 9 1 ++
    List.replicate 18 0 ++ List.replicate 8 1 ++ List.replicate 9 0 ++ [1, 2 ^ 45 - 4])

def highDigits : List ℕ := highPrefix ++ List.replicate 1005 0

def highPort : ℕ := Nat.ofDigits radix highDigits

def ports (K : ℤ) : Fin 4 → ℤ := ![beta, K, lowPort, highPort + beta]

end DiophantineConsistency.CurrentMasks2011
