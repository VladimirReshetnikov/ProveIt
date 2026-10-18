import GowersSzemeredi.Proofs16ShortScale
import GowersSzemeredi.Proofs16FibreCovers
import GowersSzemeredi.Proofs16LocalizedCover
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Bertrand

/-! `Section16WidthTransfer W`: the linearity width `W` transfers along cell
refinements.

Lemma 16.9 at every scale with arbitrary remainder controls, for widths with
this property (`allScaleLemma169WithAt_of`), is in
`Proofs16Lemma9WithRemainderSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A width transfers along cell refinements: a cell of width at least `m^c`
inherits the guarantee at width exponent `c * a`. -/
def Section16WidthTransfer (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (m n q : Nat) (a c zeta : Real), 0 ≤ zeta → 0 ≤ a → 0 ≤ c →
    (m : Real) ^ c ≤ n → W m q (c * a) zeta ≤ W n q a zeta

end LeanProofs.GowersSzemeredi
