module
public import PA196.Logic.Relational.Encoding
public import M6PA.Calibration.RelationalSourceSyntax
@[expose] public section

/-! Host source encoding, kept separate from the LK compiler so arithmetic
calibration of fixed syntax does not import the whole host proof pipeline. -/
namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder M6.PA.RelationalSource
abbrev code (p : Proposition language) (f : Nat → Nat) (lo z : Nat) : Nat :=
  relationalCode z (toNamed p Fin.elim0 f lo)
end PA196.Logic.Relational.Source
