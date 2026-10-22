# Independent audit of the two proof simplifications

Baseline: ProveIt commit `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.
This document records independent source inspection and checking of execution
receipts. It is not a second execution of every compiler command.

## Rocq propositional core: approved as a checked component

All 71 original theorem statements in each of the two named calculi have
matching explicitly typed audit examples. The 142 statements agree with the
old signatures after whitespace normalization. The 71 old pairs of proof
bodies are identical after the documented predicate, constructor and name
renaming. The shared core preserves those derivations while replacing the
arbitrary equality formula used in three proof bodies with an existing bound
formula.

The core's complete contract is the formula carrier, implication, negation,
the theorem predicate, modus ponens and B1/B2/B3. It has no distinguished
formula, equality rule, quantifier rule or inhabited-carrier assumption.
Both concrete adapters supply its rule fields by the existing calculus
constructors. The 26 selected assumption reports are closed. Source and
object hashes in all ten compilation records match their current files;
the recursive `coqchk` receipt records exit zero.

The selected production source scope is exactly the two old files versus
the common core and both compatibility facades:

| Measure | Before | After | Saving |
| --- | ---: | ---: | ---: |
| UTF-8 bytes | 23,160 | 16,001 | 7,159 |
| Physical lines | 297 | 261 | 36 |
| Maintained derivation bodies | 142 | 71 | 71 |

The compiler is Coq 8.18.0. The only consumer compatibility edit is the
`Stdlib` to `Coq` import-prefix change in `L224Meta.v`; no proof statement or
body in that consumer changes. Production Rocq 9.1 integration, producer
wiring, exact dependency bindings and the full K215 endpoint rebuild remain
explicitly separate. This component's source reduction is not a measured
endpoint speedup or a proof-term-size claim.

## Lean direct seed: structural and mathematical audit approved

The direct route is a checked implementation effort based on the existing
`DIRECT_FULL_SEED.md` proposal and the analogous Rocq `Complete222.v` proof.
It must be attributed accordingly. Its decisive completeness premise gives
models of the original named formula with literal equality, even though
the syntactic derivability premise uses the equality interpretation. This
justifies the new construction without a circular dependency.

The freshness proof uses free-variable support: a free name survives the
equality interpretation and is strictly below the resulting encoded formula.
The private name equal to that encoded formula is therefore fresh. Double
negation makes it greater than the two fixed roles, and is removed only
after establishing the named bundle's seed semantics. The final
inhabited-domain witness is the original valuation's `e 0`.

`FullSeed`, `DerivableNF`, the named bundle syntax, and `enc_bundleNF` move
unchanged into a shared interface. Existing optional quotient and
equality-free proof bodies remain intact. Every public theorem statement
in `KEndpoint` remains unchanged; its lower-chain proof chooses the direct
seed on the original domain. The numerical bundle theorem is preserved,
including arbitrary natural codes and coincident-role cases.

Independent import traversal of the final source overlay yields:

| Exact K215 endpoint closure | Before | After | Saving |
| --- | ---: | ---: | ---: |
| Project modules | 178 | 177 | 1 |
| UTF-8 bytes | 2,093,112 | 2,086,255 | 6,857 |
| Physical lines | 40,517 | 40,387 | 130 |

The removed dependencies are `Code254Models`, `KSeedModel222`, and
`KIndisc222`; the added dependencies are `KSeedInterface222` and
`KSeedDirect222`. Retaining the old compatibility route means the six
production source files collectively grow by 7,472 bytes and 184 lines.
The reduction is in the active endpoint proof closure, not in all stored
source. The two audit clients are measured separately.

The final clean serial replay compiled 112 project modules with no project
cache reuse. Every compiler exit code is zero. Independent comparison of
all 112 source, object and raw-log hashes agrees with the final receipt,
and all project imports precede their consumers. The compiler hash also
matches. The receipt has 18 inherited warnings, with zero warnings in
every edited or new source and both audit clients.

The component's nine direct/generic assumption reports and two legacy
reports use only the baseline Lean assumptions `propext`, `Classical.choice`,
and `Quot.sound` (the two support lemmas use a subset). The generic endpoint
client states the original machine-to-ZFC equivalence with its explicit
machine-specific premises. It does not by itself recheck the K215 literal
table, startup or site certificates. The checked final summary has SHA-256
`f0c6ea1aaa851d64297aa0e7ed42dbc03dcc399fcb8883a5941f3a40b8fc9fd2`.

## Conclusion

Both changes preserve their intended public statements and remove actual
duplication at a documented boundary. Neither supplies an internally
encoded PA/ZFC proof object, a smaller Turing machine, or an unconditional
nonhalting theorem. Existing full machine correctness evidence and the
new component evidence must remain separately labelled until production
integration checks the combined source set.
