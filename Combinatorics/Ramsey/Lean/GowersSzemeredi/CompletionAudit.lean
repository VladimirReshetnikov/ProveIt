import GowersSzemeredi.NumberedAudit
import GowersSzemeredi.Proofs18CoverSharperComparisons
import GowersSzemeredi.Proofs18CoverSharperAllDegrees
import Lean.Util.CollectAxioms

/-! Production verification entry point: all numbered catalogue companions
and the stronger inverse, progression, and two-color bounds, including their
every-degree and every-length forms (Proofs18CoverSharperAllDegrees). -/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let strengthened : Array Name := #[
    ``LeanProofs.GowersSzemeredi.theorem_18_1_sharper_four_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_sharper_six_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d7_four_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L5_eleven_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_sharper_six_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L5_eleven_le,
    ``LeanProofs.GowersSzemeredi.section18ExponentAt_strictAnti,
    ``LeanProofs.GowersSzemeredi.szemerediThresholdAt_strictMono,
    ``LeanProofs.GowersSzemeredi.twoColorThresholdAt_strictMono
  ]
  for name in strengthened do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the nine improved-bound and comparison theorems; only approved axioms."

-- Exact statements of the every-degree and every-length strengthenings.
example : ∀ d, LeanProofs.GowersSzemeredi.Theorem181AtSharp 7 d :=
  LeanProofs.GowersSzemeredi.theorem_18_1_d7
example : ∀ L, LeanProofs.GowersSzemeredi.Theorem182AtSharp 5 L :=
  LeanProofs.GowersSzemeredi.theorem_18_2_L5
example : ∀ L, LeanProofs.GowersSzemeredi.Corollary187AtSharp 5 L :=
  LeanProofs.GowersSzemeredi.corollary_18_7_L5
example : ∀ L, LeanProofs.GowersSzemeredi.Theorem182AtSharp 6 L :=
  LeanProofs.GowersSzemeredi.theorem_18_2_L6
example : ∀ L, LeanProofs.GowersSzemeredi.Corollary187AtSharp 6 L :=
  LeanProofs.GowersSzemeredi.corollary_18_7_L6
example : LeanProofs.GowersSzemeredi.theorem_18_1 :=
  LeanProofs.GowersSzemeredi.theorem_18_1_d7_implies_printed
example : LeanProofs.GowersSzemeredi.theorem_18_2 :=
  LeanProofs.GowersSzemeredi.theorem_18_2_L6_implies_printed
example : LeanProofs.GowersSzemeredi.corollary_18_7 :=
  LeanProofs.GowersSzemeredi.corollary_18_7_L6_implies_printed
example : ∀ (k r : Nat), 2 ≤ r → ∀ N : Nat,
    LeanProofs.GowersSzemeredi.szemerediThresholdAt 5 (1 / (r : Real)) k ≤ N →
      ∀ color : Nat → Fin r, LeanProofs.GowersSzemeredi.HasMonochromaticAP N r color k :=
  fun k _ hr N hN color => LeanProofs.GowersSzemeredi.van_der_waerden_L5 k hr N hN color
example : LeanProofs.GowersSzemeredi.Theorem13At 5 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L5

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let everyIndex : Array Name := #[
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d7,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L5,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L5,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L6,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L6,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d7_implies_printed,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L6_implies_printed,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L6_implies_printed,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L5,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_printed,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L5
  ]
  for name in everyIndex do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the eight every-degree and every-length strengthenings, the two van der Waerden bounds and the sharper Theorem 1.3; only approved axioms."

-- The refutation is checked separately; it is never counted as a proof
-- of the original printed encoding or hidden among the 120 companions.
open Lean Elab Command in
run_cmd do
  let target := ``LeanProofs.GowersSzemeredi.lemma_16_10_printed_unit_encoding
  let proof := ``LeanProofs.GowersSzemeredi.lemma_16_10_packaged_premises_counterexample
  let info ← getConstInfo proof
  unless info.isTheorem && info.type == mkApp (mkConst ``Not) (mkConst target) do
    throwError "The Lemma 16.10 counterexample does not negate its printed encoding"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in (← collectAxioms proof) do
    unless allowed.contains axiomName do
      throwError "{proof} depends on unapproved axiom {axiomName}"
  logInfo "Separately checked the refutation of the printed Lemma 16.10 encoding."
