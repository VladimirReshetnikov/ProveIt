# Useful ideas from surreal and omnific work

Source inspection, 16 October 2026. This note separates existing Lean results
from the Surreal collection's unformalized foundational reports. No Surreal
file was modified or rebuilt for this inspection.

The most immediate reuse is its verified formula codec architecture. Its
number-theoretic presentations offer additional competitors, but none supplies
a previously verified small ZFC refutation engine.

## A directly useful parser design

`Algebra/SurrealNumbers/Surreal/Algebra/RingFormulaCode.lean:29` serializes
native formulas; `parse_encode` at line 70 proves parsing pushes exactly
the original formula onto an arbitrary existing stack. `decode_encode`
at line 83 proves recovery, and `encode_of_decode` at line 142 proves
that accepted streams are exactly serialized formulas. These are stronger
than testing some sample round trips.

`RingFormulaValidity.lean:31` replaces the stack of full formulas by a
stack of context sizes. `step_scopes` at line 42 and `parse_scopes` at
line 65 prove that numerical scope validation agrees with native parsing.
`scope_encode`, `valid_iff_decode` and `valid_iff_mem_range` give the
exact accepted language. This separates a small runtime checker from the
larger semantic objects used to prove its correctness.

`RingFormulaCodeComputability.lean:95`, `:111`, `:131` and `:137` then prove
primitive recursiveness of validity, encoding, decoding and context extraction.
They are useful proof patterns; primitive recursiveness alone gives no small
TM state bound.

**Applied here:** `BusyBeaver/ZFC/FormulaRPN.lean` adapts the stack-proof
pattern to a mathlib-free equality-free syntax with membership, NAND and
universal quantification. It proves both codec directions and a scope-correct
closed contradiction. De Bruijn quantifiers carry no variable-label payload.
The tokens still have natural atom payloads, and this Lean prefix codec is
distinct from the Python named-variable postfix binary experiment. No
correspondence between them or binary decoder theorem is claimed yet.

## Real arithmetic interpretations, with their exact boundary

`Surreal/Foundations/OmnificArithmeticInterpretation.lean:25` and `:31`
prove that explicit parameter-free formulas select exactly the ordinary
integer and natural images inside the actual omnific ring. Its
`omnific_realize_integerTranslation` at line 66 and
`omnific_integerSentence_iff` at line 74 give an actual formula translation,
rather than only an informal assertion that arithmetic is representable.

The guard itself is concrete. `Surreal/Algebra/ArithmeticGuards.lean:43`
uses five existential witnesses and three equations involving a Pell relation
and the intersective polynomial `(t²−13)(t²−17)(t²−221)`.
`FormulaRelativization.lean:21` defines the translation recursively, and
`realize_relativize` at line 38 proves its semantic behavior.

This suggests a possible arithmetic or Diophantine certificate route, using
existing verified guards and formula transport. It does not give a small
recursively axiomatized theory equiconsistent with ZFC: truth in the intended
omnific ring is not such an axiom recognizer. The defining guards and
polynomial evaluator must be charged to a compiled machine. We therefore
retain this as an alternative encoding route rather than replace the small
membership kernel with the whole omnific language.

## Surreal-only set theory preserves schemas rather than erasing them

The report `docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets`
has a genuine foundational proposal. Its Part IX uses birthday/simplicity
structure, ordinal bit storage, and pointed well-founded extensional graphs
to recover a set universe. Theorem 73.1 (`hset:sf:thm:axiomprinciple`,
`article.tex:9261`) gives the explicit recipe

`Adm(I) + {σ^I : σ is a source axiom} + Iso(C)`.

Theorem 73.4 at line 9413 applies this to numerical theories bi-interpretable
with ZFC. This is useful as a **calibration recipe**: specify admissibility,
quotient congruence and the round trip, and make the axiom list effective.
It does not compress an infinite source schema into finitely many axioms.
The report explicitly says its presentation sacrifices axiomatic elegance
and is not the announced intrinsic surreal axiom list (`article.tex:9440`).
Its README lines 406–455 records the source contributions and limitations;
lines 790–820 says these new foundational statements are not formalized.

For our purpose, full bi-interpretation and recovery of every numerical
object are more than the required refutation equivalence. We can borrow
the explicit proof-transport discipline while omitting an isomorphism
round trip from the searched theory if consistency calibration suffices.
That omission requires its own proof, as with the incoming kernels.

Two cautions prevent misleading simplifications. Pure real-closed field
algebra does not supply ZFC strength; the report's pure-field obstruction
and pure-omnific birthday nondefinability show why the extra structural
relations matter. Conversely the report's NBG obstruction concerns a
uniform interpretation inside ZFC. It does not exclude using a finitely
axiomatized conservative class theory as an equiconsistency competitor.
Such a competitor still needs an explicit finite axiom list, proof system,
calibration, and measured compiler cost.

The report's hereditary-size analysis also supplies countermodel ideas:
`H_κ` and `V_κ` have different closure properties, and matching a cardinal
size does not prove Replacement or Power Set. The new EFH-transitivity
deletion rejection in [rejected_deletions.md](rejected_deletions.md) uses
this discipline with the specific model `V_{ω₁}`.
