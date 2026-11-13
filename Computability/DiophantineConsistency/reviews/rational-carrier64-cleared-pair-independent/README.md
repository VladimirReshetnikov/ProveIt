# Independent review: external rational iff and cleared integer iPRA pair

**PASS within captured-provider scope.** The checked
[`external_and_cleared_ipra`](../../research/rational-carrier64-cleared-pair/ClearedCurrentPair.lean)
is exactly a conjunction of:

1. An external Lean iff between existence of a strictly positive integer
   zero of the actual-port 64-row rational evaluator and existence of a
   strictly positive integer zero of `clearedExpression`.
2. The existing standard-iPRA derivability of the equivalence between the
   explicit integer-language `clearedNoZero` sentence and the intuitionistic
   negation of the mapped native refutation predicate.

The proof uses `external_and_ipra.1` and the separately checked `cleared_ipra`.
The first conjunct typechecks because `clearedExpression` is definitionally
`expressionAt CurrentWindowCarry2011.ports`; the rational side uses the same
actual tuple. The inherited pointwise iff uses the identical positive integer
valuation in each direction. The second conjunct concerns the existing
positive-shifted 65-row integer syntax. This conjunction is not an iPRA
proof of an object-language formula with rational constants, a newly
formalized clearing algorithm, or an integer-leaf 64-operation record.
Neither a zero nor Con(ZFC) is asserted.

Attempt01's retained result/log match their temporary originals, record Lean
exit 0, no stop and the expected axiom report. A separate retained outer
observation records session 53951 exit 0; this review did not observe that
prior session directly. Independent [check.py](check.py) ran exit 0, rechecking
the output object, four explicitly guarded provider objects, predecessor
receipts, fresh-base state and all 178 direct/companion/shadow guards;
[result.json](result.json) records the outcome. The prior
[cleared syntax review](../rational-carrier64-cleared-ipra-independent/README.md)
and [external/iPRA pair review](../rational-carrier64-current14-pair-independent/README.md)
cover the component semantics and provider links. No Lean replay or complete
transitive/dynamic ancestry audit was run; sampled resource monitoring limits
remain inherited.

Checker SHA-256
`715ed1055f5ce1076ca58cbdce3ddfbdad8af6854c51d1dd2f029eff15d1cfc5`;
result SHA-256
`c488f550fdb52496c0738a470a13c20b72bb7e627d2771cf8627b393c4c99dfd`.
