# Certification contract

The final numerical release must identify one literal table M and prove

    ZFC |- not Halt_blank(M) <-> Con(ZFC).

The equivalent positive contract is Halt_blank(M) <-> exists p Prf_ZFC(p,bottom).
The requested metatheory is ZFC; a PA proof would be stronger but is not imposed
as a new requirement here.

## Mathematical calibration in the report

- Freeze ZF_0 as foundation- and choice-free ZF with functional Replacement and
  full Separation. Do not silently substitute unrestricted Collection.
- Formalize exact constant classes, singleton formation, the fixed switching
  instance, and the positive transitive-cover lemma.
- Prove uniform pure/mixed schema translations for arbitrary formula codes.
- Certify the displayed forward ZF_0 constructions and exact-fiber converse.
- Translate logical equality to D; EC is retained for first-argument congruence.
- Connect to ordinary ZFC via effective Foundation and Choice reductions.

These are proved at the ordinary mathematical level in the article. Their
serialized derivations and machine-checked proof transformers are not supplied.

## Reference checker obligations

- Only membership, negation, implication, and universal quantification execute.
- All labels are nonnegative integers, never Boolean values.
- Free slots 0/1 are input/output; bound occurrences remain bound.
- All other free variables are parameters and universally closed.
- All schema binders are fresh above every variable label in the matrix.
- Check Q2 freshness, simultaneous substitution, capture avoidance, shadowing,
  alpha conversion, and strictly backward references.
- No admission or unchecked conclusion record is allowed.
- SC generates an implication; it does not decide the semantic boundedness
  antecedent.
- The final target is the logical contradiction not forall x(E(x,x)->E(x,x)).
  A diagonal membership target requires a proved alternative calibration.

## Search and compiler obligations

Prove both soundness and completeness of the certificate representation,
termination on every finite candidate, and fairness of the unbounded search.
Resource exceptions cannot be ignored as rejected proof candidates. The Python
program is a finite-resource reference, not a certified implementation of the
ideal algorithm. A TM implementation uses unbounded finite tape encodings.

Prove simulation of the exact compiled table, including blank initialization,
start/head convention, symbols, terminal state counting, register invariants,
all optimizer passes, and table identity. A validator can replace trust in an
optimizer only with its own correctness theorem and checked certificate.

## Proof-assistant boundary

New repository formal work is intended for Lean. There is no Lean development
in this archive. A kernel theorem in an ambient type theory is not by itself an
exported derivation in ZFC. Specify the internal derivability endpoint or an
explicit metatheoretic interpretation of the development used.

## Published baseline boundary

The import records an upstream Coq proof and an unsuccessful local historical
build. This work confirms table bytes and finite/static facts only. It does
not replay the Coq proof or infer the exact ordinary-ZFC proof predicate from
the name of an upstream theorem. The original compiler bundle is absent from
the inspected published snapshot.
