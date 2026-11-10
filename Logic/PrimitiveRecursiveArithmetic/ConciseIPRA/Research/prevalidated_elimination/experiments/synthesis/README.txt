SYNTHESIS-STYLE CHECKER EXPERIMENT
================================
This is a research prototype, not a replacement for the selected measured
checker and not a claim of a new smallest axiomatization.

The experiment uses the inherited arity codec and initialized-I/Choice-DI
calculus, but synthesizes the conclusion from proof instructions. A scalar
instruction is a retained-context index; four-field instructions describe
computation, paired introduction, or elimination. Elimination first checks
its major recursively and uses the inferred major's shape and endpoints.
The final advertised goal is still checked, with that comparison included
in the source measurements.

All prototype code reads JSON; it never executes input as Python. No producer
or helper is imported by either prototype checker. The Python/JSON runtime
is the same shared environment as in the comparison programs.

FILES
  synth_checker.py      Transparent direct implementation.
  synth_compact.py      Shared binder continuation, exact-equality index tests.
  check_prototypes.py   Untrusted named proof emitter and finite test harness.
  prototype_receipt.json Exact packets, expectations, and execution receipt.
  measurements.json     Whole-module normalized source and gzip9 measurements.

MEASUREMENTS
                           Bytes  Tokens  AST  Gzip9
  Transparent prototype     951    330    390   446
  Compact prototype         777    334    392   421
  Existing byte leader      558    264    310   345
  Existing token/AST leader 598    262    296   350

These prototypes therefore do not improve any relevant source coordinate.
Their principal benefit is reducing redundant certificate information:
equality endpoints and the major formula are inferred rather than repeated.
That benefit is offset in the checker by explicit hypothesis-index dispatch,
inferred-minor comparison, DI step-conclusion comparison, and scope restoration
with escaping-witness validation. Omitting advertised-goal verification would
not bring either program close to the current byte frontier.

RULE FORMAT
  Scalar j: return context[j], restricted to an in-range integer index in the
  compact variant.
  [m,s,u,t] with truthy m: infer the next proof as major. A unary D major opens
  a new Q context resource and checks the continuation. An equality major
  supplies source/target endpoints for template t; the following proof must
  infer its source instance. A ternary Q major supplies its body; u is its
  specialization target and the following proof must infer its zero instance.
  [m,s,u,t] with falsy m and truthy u: infer the constructed I0/IS equation,
  with predecessor discriminator s, initializer u, and update t.
  [m,s,0,t] with falsy m: paired introduction. Here s is the advertised unary
  D formula and t its witness. Marker m=0 permits progress only at an equation
  matrix; m=[] selects case introduction. Infer the step proof under the
  selected local assumption and compare it to the required successor matrix.

Scopes are local: before a binder rule the old floor is retained, then a new
negative eigenparameter is allocated; after the recursive premise the old
floor is restored and the returned formula is checked at that old scope.
This last validation is essential in D elimination. It prevents an inferred
continuation from returning a formula depending on the eliminated witness.

FINITE EVIDENCE
  From the extracted package root, run:
    python3 experiments/synthesis/check_prototypes.py
  Or run python3 check_prototypes.py from this directory. The runner locates
  the included tests/producer.py relative to its own path, needs no external
  checkout or network, and exits nonzero if any expected verdict fails.
  It refreshes prototype_receipt.json with its exact cases and results.
  19 named cases x two implementations x normal/-O Python = 76 executions.
  All 76 expected verdicts passed. The eight positive cases include genuine
  equation induction, nested closure introduction, nonvacuous D elimination,
  equality transport, arithmetic state updates, and repaired zero initialization.
  Negatives change each advertised theorem to 0=1 and test unallocated goals,
  unproved majors, and invalid hypothesis indices.

This is focused finite implementation evidence. A complete raw-input decoder
soundness proof or whole-iPRA equivalence formalization has not been supplied
for these experimental files. The prototype inherits the same mathematical
basis as the existing drafts and does not supply a foundational breakthrough.

ATTRIBUTION
The arity opener and computation patterns derive from ProveIt's
ipra_certified_zero_2026-11-10 package, at commit
76a2651601d17b34d46753f189ea026a21ce8d29. The untrusted named proof emitter
reuses that package's producer helpers with a new synthesis serialization
and local scope restoration. The existing MIT No Attribution license applies
to the inherited source. These are included as reproducible research prototypes, not established
replacement kernels or published changes to the repository.
