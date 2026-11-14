import PA194RelationalEncoding
import PA194SourceSyntax

/-! Host source encoding, kept separate from the LK compiler so arithmetic
calibration of fixed syntax does not import the whole host proof pipeline. -/
namespace PA194Logic.Relational.Source
open LO LO.FirstOrder M6.PA.RelationalSource
abbrev code (p : Proposition language) (f : Nat → Nat) (lo z : Nat) : Nat :=
  relationalCode z (toNamed p Fin.elim0 f lo)
end PA194Logic.Relational.Source
