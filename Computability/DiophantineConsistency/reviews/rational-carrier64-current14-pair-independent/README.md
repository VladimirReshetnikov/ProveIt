# Independent review: narrow external rational/iPRA pair

**PASS within captured-provider scope.** The checked
[`external_and_ipra`](../../research/rational-carrier64-current14-pair/RationalCarrier64CurrentPair.lean)
is exactly a conjunction of two independently established facts:

1. An external Lean iff between existence of a strictly positive integer
   zero of the fixed-rational-leaf 64-row evaluator and existence of a
   strictly positive integer zero of the integer `expressionAt` syntax.
   Both use `CurrentWindowCarry2011.ports` and the same valuation.
2. The existing derivability statement
   `standardTheory ⊢ noZero14 ↔ ¬mappedNativeRefutation embedding`.

The `noZero14` source uses `naturalExpression`, defined as a positive shift
of `expression`, and `expression` is `expressionAt` of that same actual
port tuple. This is a conjunction of an external rational/integer evaluation
fact and an internal **integer-syntax** iPRA theorem. It does not construct a
rational object-language sentence or prove its equivalence internally in
iPRA. It does not itself prove that either equation has a zero or that ZFC
is consistent.

Attempt02's retained result/log match their temporary originals, record Lean
exit 0, no stop and the expected axiom report. The separately retained
outer-session observation records session 52835 exit 0; this review did not
observe that earlier session itself. The output object and the direct
external-client and fresh-base endpoint objects match their hashes. The
independent [checker](check.py) ran exit 0 and rechecked 65 recorded
provider/companion/shadow guards, the prior external-client receipt, and
the endpoint's base manifest/state, successful producer source, inputs and
log. [result.json](result.json) records the check; previous beta,
specialization and external-client reviews cover those constituent links.

The successful run used `-M2800`, a 120-second timeout, sampled 3.5 GiB
RSS cap and 10 GiB available-memory floor. Its receipt records 10 samples,
a peak of 2,844,966,912 bytes and minimum available 18,819,403,776 bytes.
The RSS limit is a sampling guard, not a hard kernel memory bound. Attempt01
failed at `-M2400` and is not used as successful theorem evidence. No Lean
replay or complete transitive/dynamic ancestry audit was run.

Checker SHA-256
`62bc3b47857ff55981fec62f400d37bb9797de5e3ae7670fd3f72f1b5a2af784`;
result SHA-256
`92f580df2ac40bbf937a1613b0c3abbac63956697c05fa5e75d6496863c98524`.
