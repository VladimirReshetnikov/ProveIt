# Selective equality and constructor fusion: finite ZFC consistency formalisms

This contribution provides a proved reduction of an alternative finite source
theory and exact executable payloads. It does not supply a binary Turing machine
with fewer than 245 states.

The new proof interprets only membership on the quotient by the equality
surrogate. It keeps assignments and class codes raw, then proves their meaning
separately for every ordinary finite formula. As a result, update congruence,
lookup congruence in the selector argument, and all incidence congruence can be
removed. A named selector needs only the literal `not Eq(d,q)`; it need not be
equated to a Boolean class constructor. A further two-coordinate model allows
the hull and NAND constructors to share one function. Making raw updates
injective in that upper model then lets class constructors also provide the
three witnesses. The resulting alternatives have eight, six or five proper
function symbols. These are proved model constructions; raw injectivity is
not imposed as an extra target axiom.

| Theory | Clauses | Literals | Maximum local variables | Exact flat bits |
| --- | ---: | ---: | ---: | ---: |
| Prior completed FC15* reduct | 20 | 53 | 6 | 1,134 |
| SE19, original one-constant layout | 19 | 45 | 4 | 1,027 |
| SE19, named second selector | 19 | 45 | 4 | 971 |
| Prior completed FC16* reduct | 21 | 57 | 6 | 1,341 |
| SE20, original one-constant layout | 20 | 49 | 4 | 1,234 |
| SE20, named second selector | 20 | 49 | 4 | 1,138 |
| Frozen six-function SE17 | 17 | 36 | 4 | 1,042 |
| Frozen six-function SE18, extensional | 18 | 40 | 4 | 1,201 |

The preferred constructor-sharing presentations are:

| Payload | Proper functions | Predicates, including Eq | Clauses/literals | Maximum term depth | Exact flat bits |
| --- | ---: | ---: | ---: | ---: | ---: |
| `se19n` | 8 | 4 | 19/45 | 3 | 971 |
| `se19n6` | 6 | 4 | 19/45 | 4 | 1,011 |
| `se19n5` | 5 | 4 | 19/45 | 4 | 1,027 |
| `se20n` | 8 | 4 | 20/49 | 5 | 1,138 |
| `se20n6` | 6 | 4 | 20/49 | 5 | 1,178 |
| `se20n5` | 5 | 4 | 20/49 | 5 | 1,194 |

All have two explicitly charged constants and at most four local variables.
All admit a total radix-eight ground-term codec. The eight-function version
uses every constructor tag; the six- and five-function versions use two and
three harmless unary padding tags. An optional eight-function variant encodes
the guard by `Eq(A(b,t),d)`, saving one predicate at a cost of 48 flat bits:
`se19n_guard` has 1,019 bits and `se20n_guard` has 1,186.

The new named streams save 163 and 203 bits respectively. Direct grounding over
a frontier of B terms changes from `B^6 + 7 B^4 + 12 B^3` to
`5 B^4 + 13 B^3 + 1` records for the raw theory; the extensional controls add
`B^3`. These are template and grounding costs, not total SAT complexity or TM
state counts.

The frozen corollaries use six proper functions and three predicate symbols.
Their terms are deeper (maximum depth twelve), while their clause counts and
predicate count are smaller than those of the five-function fused targets.
The proof applies the same raw truth lemma to the inherited universal-class
and freeze contracts. These are concrete compiler tradeoffs.

## Proof and calibration

`selective_equality.tex` is a body-only mathematical note suitable for inclusion
in the main report. The four completion clauses are exactly:

1. `not Eq(x,y) or not Eq(x,z) or Eq(y,z)`;
2. `not Eq(s,t) or Eq(V(s,j),V(t,j))`;
3. `not Eq(a,b) or not Eq(x,y) or not E(a,x) or E(b,y)`;
4. `not Eq(d,q)`.

The native assignment law derives reflexivity. Lookup transport gives
cancellation for an encoded pair and arbitrarily many distinct selector
classes. The truth lemma follows actual raw update objects at the quantifier
step and requires neither update nor incidence transport. The native closure
clauses then give every full-parameter raw EPSC instance on the membership
quotient. SE20's extra native class clause makes this quotient extensional.

The sharing theorem starts from an inherited native model M and builds a
model on M × M. Equality and membership read first coordinates; incidence
reads an assignment's first coordinate and a class's second. Thus N's first
coordinate may implement the original hull while its second implements NAND.
An injective code of a raw update's six coordinates can be stored in that
update's otherwise unused second coordinate. Each update then identifies a
unique raw triple. The first coordinates of `A(C(b,t,u),d)` and
`Q(C(b,t,u),d)` provide Y and Z, while `A(C(s,j,a),q)` provides W. The raw d/q
tags are distinct, so the two A roles cannot conflict. Its second coordinate
continues to implement atomic membership classes on every argument. All
function substitutions have exact projection proofs and reverse definitional
expansions.

The final consistency equivalences are ordinary arguments internalizable in
ZFC. SE19 depends on the inherited raw-EPSC calibration. SE20 instead uses the
inherited direct Extensionality-plus-EPSC bootstrap to ZF without Foundation or
Choice and the established Foundation/constructibility relative consistency
transports. No new proof-assistant endpoint or PA proof-code compiler is claimed.

## Reproduction

```sh
python3 selective_equality.py
python3 fused_hull.py
python3 fused_witnesses.py
python3 frozen_selective_control.py
```

This regenerates fourteen `.json`, `.bits`, and `.bin` payload triples in
`results/`, checks independent payload parsing, and performs the recorded
codec and finite-stage checks. The exact measurements and SHA-256 values are
in `results.json`, `fused_results.json`, `fused_witness_results.json`, and
`frozen_results.json` within that directory. The fused witness script checks
8,192 arithmetic term-code roundtrips and eight complete finite SAT witnesses.

The optional `--stage N` chooses one finite stage; `--extensional` chooses SE20.
The optional `--whole-search` runs the ideal unbounded semidecision procedure.
It should not be expected to terminate. It halts only after an exact UNSAT
result. Host errors propagate and are never converted to inconsistency.

The SAT engine receives ordinary propositional atoms for `Eq`, `E`, `Inc`, and
`G`. It does not silently reinstate built-in equality or deleted congruence.
Finite-stage SAT results are checked witnesses for the finite ground clauses,
not finite models or consistency evidence.

## Provenance

The native FC15*/FC16* clauses and their EPSC calibration are from ProveIt
source44. Byte-exact copies of its generators and mathematical note are in
`reference/`, together with the direct extensional lower proof and license.
The general assignment/class architecture is attributed there to Harvey
Friedman's *Impossible Counting*, Section 4.1.

The prior incoming `zfc-sub245-research-20261018` contribution established the
20-clause and 21-clause completed reducts by reconstructing a native model on
the equality quotient. This note strengthens that argument by interpreting
finite formulas directly on raw assignments.

Inspected primary source, at the current pinned ProveIt commit:

- [Native FC15*/FC16* specification and calibration](https://github.com/VladimirReshetnikov/ProveIt/blob/fd1adfa19f8fe8da41444e3fa43b89a59d891067/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/44-nine-notes-finite_class_closure.md)
- [Direct extensional calibration](https://github.com/VladimirReshetnikov/ProveIt/blob/fd1adfa19f8fe8da41444e3fa43b89a59d891067/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/44-nine-notes-extensional_control_proof.md)

Novelty is scoped to the inspected project sources and incoming submissions.
The claim concerns these exact reduced theories and encodings; it does not
license removing equality rules from the existing 245-state Hilbert machine.
