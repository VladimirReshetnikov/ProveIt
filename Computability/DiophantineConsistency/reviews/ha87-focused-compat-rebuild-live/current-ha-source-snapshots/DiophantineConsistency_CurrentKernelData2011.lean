import DiophantineConsistency.WangTiles942TableData
import DiophantineConsistency.CurrentMaskData2011
import Mathlib.Data.Fintype.Sum

/-! Exact current finite kernel and complete four-port tuple, without native proofs. -/
namespace DiophantineConsistency.CurrentKernel2011
open WangTiles942
open scoped BigOperators
set_option Elab.async false

abbrev radix : ℕ := CurrentMasks2011.radix

/-- The34 control entries use the actual packed west/north/east/south order. -/
abbrev Entry := Fin 942 ⊕ (Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9)))

def position : Entry → ℕ
  | .inl i => physicalPosition i
  | .inr (.inl j) => 978 + j.val -- west
  | .inr (.inr (.inl j)) => 960 + j.val -- north
  | .inr (.inr (.inr (.inl j))) => 969 + j.val -- east
  | .inr (.inr (.inr (.inr j))) => 942 + j.val -- south

def weight : Entry → ℕ
  | .inl i => selectorWeight (tile i)
  | .inr (.inl j) => 2 ^ (10 + j.val)
  | .inr (.inr (.inl j)) => 2 ^ (18 + j.val)
  | .inr (.inr (.inr (.inl j))) => 2 ^ (27 + j.val)
  | .inr (.inr (.inr (.inr j))) => 2 ^ (35 + j.val)

abbrev Term := Fin 3 ⊕ Entry

def exponent : Term → ℕ
  | .inl j => ![18, 1004, 2020] j
  | .inr e => 1005 - position e

def coefficient : Term → ℕ
  | .inl _ => 1
  | .inr e => 2 * weight e

def rawWord (r : ℕ) : ℕ := ∑ t : Term, coefficient t * r ^ exponent t

def K : ℕ := rawWord radix

end DiophantineConsistency.CurrentKernel2011

namespace DiophantineConsistency.CurrentWindowCarry2011
open CurrentKernel2011

/-- The four actual integer ports, including the one source high-mask shift. -/
def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)

end DiophantineConsistency.CurrentWindowCarry2011
