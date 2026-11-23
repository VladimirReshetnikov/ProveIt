# Lean formalization blueprint

**Status: uncompiled.** No Lean build or kernel audit was executed in this
session. Read the formalization chapter of the report before using these files.

- `SemanticCore.lean`: small standalone candidate with word maps, DFA runs,
  Boolean complement and product proof scripts. No `sorry` or axiom is used;
  the file still needs to be typechecked.
- `RegularOutline.lean.txt`: finite row-major DFA/epsilon-NFA records,
  subset construction, regex tree conventions, correctness specifications,
  and remaining object-level derivations.
- `MonoidsOutline.lean.txt`: finite multiplication tables, transformation
  vectors, generated monoids, and syntactic-context obligations.
- `ContextFreeOutline.lean.txt`: grammar/tree/PDA records and all normalization,
  parsing, EBNF, pumping, finiteness, closure, and separation obligations.
- `EffectiveOutline.lean.txt`: bounded tape machine steps, PR compilation,
  certificates, noncontracting membership and its diagonal separation,
  and halting/complement refutations.
- `ObjectTheoryOutline.lean.txt`: numerical PR symbols, representative closed
  `Prf PRAAx` endpoint formulas, source imports, and completion gates.

The theory has two distinct levels. Semantic finite-data proofs are useful,
but the task's constrained setting requires an explicit iPRA derivation of
the encoded sentence. The report explains how to Boolean-compile bounded
invariants before applying quantifier-free induction. Do not replace those
derivations with a claim that a Lean function happens to terminate.

The pin `leanprover/lean4:v4.32.0` matches inspected ProveIt commit
`3eb195cab4cc3d552a9eca78880c6d428f3e44f9`. The standalone `lakefile.toml`
has no Mathlib dependency; integration with the object theory uses the
repository's existing Lake configuration. Nothing in these files claims
compatibility has already been checked.
