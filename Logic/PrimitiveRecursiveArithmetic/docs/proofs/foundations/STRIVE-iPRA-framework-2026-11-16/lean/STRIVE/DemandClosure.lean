import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Search

/-!
# STRIVE-iPRA: finite monotone demand closure

This module is an implementation outline for the finite-chain closure theorem.
The mathematical result is inherited from FINER-iPRA and is restated here only
at the exact interface required by the STRIVE compiler.
-/

namespace LeanProofs.IPRA.STRIVE

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

/-- Host metadata for a fixed product of finite chains.  The object module
specializes this record to concrete PR symbols rather than reflecting arbitrary
Lean functions. -/
structure DemandSystem where
  dimension : Nat
  capacities : Fin dimension → Nat
  seed : Fin dimension → Nat
  transfer : (Fin dimension → Nat) → Fin dimension → Nat
  transfer_bounded : ∀ d i, transfer d i ≤ capacities i
  transfer_monotone : ∀ a b, (∀ i, a i ≤ b i) → ∀ i, transfer a i ≤ transfer b i

/-- Metalevel least closure, used to generate test fixtures and concrete PR
recurrences. -/
def DemandSystem.iterate (D : DemandSystem) : Nat → (Fin D.dimension → Nat)
  | 0 => D.seed
  | k + 1 => fun i => max (D.iterate k i) (D.transfer (D.iterate k) i)

/-- Sum of remaining coordinate capacities; each strict step lowers it. -/
def DemandSystem.rank (D : DemandSystem) (d : Fin D.dimension → Nat) : Nat :=
  ∑ i, D.capacities i - d i

/-!
Object-theory targets for each fixed generated system:

* a packed vector representation and projection equations;
* boundedness of every iterate;
* inflation and monotonicity of the generated transfer;
* if step k is not stable, the coordinate-sum increases;
* stability by the numeral `Σ_i capacity_i`;
* prefixedness and leastness over every vector above the seed.

All induction is on the clock and has a quantifier-free packed-state invariant.
-/

end LeanProofs.IPRA.STRIVE
