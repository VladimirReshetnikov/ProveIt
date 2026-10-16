# Genuine falsity in the ternary formula codec

`BusyBeaver/ZFC/Bottom3Syntax.lean` formalizes the codec proposed by source 16
of the closure-kernel report, delivered in `9439d775aa`. Its proofs extend the
repository's earlier `Base3Syntax` development. Write `P` for Cantor pairing:

| Formula | Code |
|---|---|
| Truth | 0 |
| Bottom | 1 |
| Membership(i,j) | 3 P(i,j) + 4 |
| Implication(A,B) | 3 P(code(A),code(B)) |
| Universal(i,A) | 3 P(i,code(A)) + 2 |

Membership(0,0) now has code 4. No variable occurs in Bottom. This keeps three
constructor residues while making the numerical halting target a genuine
falsity constant. The only syntactic alias is Truth → Truth, recursively
contracted to Truth throughout the formula tree.

Kernel-checked declarations in namespace
`SetTheory.BusyBeaver.ZFC.Bottom3Syntax` establish:

- `encode_decode`: every natural decodes and re-encodes exactly.
- `decode_encode_normalize`: every formula round-trips to its recursively
  normalized form; `normalize_idempotent` proves normalization is stable.
- `encode_injective_on_canonical`: canonical syntax has unique codes.
- `decoded_label_lt`, `code_fresh`, `wrapper_fresh`: all variable labels,
  including binders, lie below the code; the emitter's code+2 label is fresh
  even for matrices 0 and 1.
- `sat_roundtrip`: normalization preserves the ordinary one-sorted semantics
  of every formula, relation and assignment. `sat_bottom` proves code 1 is
  false independently of that relation and assignment.

The fuel decoder is total with fuel n+1; the round-trip proof covers all
naturals, not a bounded sample. The fresh serial 36-module verification is
recorded in `results/lean-verification.json`. Printed theorem dependencies
are only Lean's standard `propext`, `Classical.choice` and `Quot.sound`;
`sat_bottom` has no axioms. No `sorry`, `admit` or `native_decide` is used.

This proves a syntax component for a future complete frontend. It does not
prove capture-avoiding substitution, reference-checker completeness, helper
execution, compiler simulation, or a nonhalting/consistency equivalence.
In particular, the source's 251-state reduced C/G experiment still has the
finite-sort countermodel: shifting membership by three preserves the strict
label bound needed by that argument. Primitive Bottom fixes the falsity
alias but does not supply cross-variable instantiation.
