import GowersSzemeredi.PrintedSection13BoundsAudit
import GowersSzemeredi.Proofs13IntegerSparseSquare
import Lean.Util.CollectAxioms

/-! Exact types and axiom checks for genuine integer square extraction
in the one-point density regime. The unrestricted corollary remains open. -/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.intervalThrough_integer,
    ``LeanProofs.GowersSzemeredi.intervalThrough_contains,
    ``LeanProofs.GowersSzemeredi.integer_square_of_one_point_budget,
    ``LeanProofs.GowersSzemeredi.corollary_13_10_printed_integer_of_one_point_budget,
    ``LeanProofs.GowersSzemeredi.corollary_13_10_printed_integer_small_modulus
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked five integer square results in the one-point density regime; only approved axioms."

example {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (D : Finset (LeanProofs.GowersSzemeredi.Pair N))
    (phi : LeanProofs.GowersSzemeredi.Pair N → ZMod N)
    (hD : D.Nonempty) (hbilinear : LeanProofs.GowersSzemeredi.BilinearOn D phi)
    (m : Nat) (hm : 0 < m) (hmN : m ≤ N) (delta : Real)
    (hbudget : delta * m * m ≤ 1) :
    ∃ V W : LeanProofs.GowersSzemeredi.ModAP N,
      ∃ E : Finset (LeanProofs.GowersSzemeredi.Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.HasIntegerRepresentatives ∧
      W.HasIntegerRepresentatives ∧ V.length = m ∧ W.length = m ∧
      E ⊆ D ∧ E ⊆ V.carrier.product W.carrier ∧
      delta * V.length * W.length ≤ E.card ∧
      LeanProofs.GowersSzemeredi.BilinearOn E phi :=
  LeanProofs.GowersSzemeredi.integer_square_of_one_point_budget
    hN D phi hD hbilinear m hm hmN delta hbudget
