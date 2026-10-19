# Alternative formalisms and what their measured costs establish

The most useful frontend change for the present target is the Theory K construction supplied by Elliot Glazer. The inspected K230 development already connects a literal binary machine, its nonzero initial enumeration seed, and ordinary finite ZFC refutability. Its source has 5,125 primitive occurrences and 212 distinct DAG nodes, counting both cons subtrees and primitive leaves. The supplied 235-state source has 6,455 occurrences and 224 distinct DAG nodes. These are exact source measurements; the five-state difference between the released machines is a complete-machine observation, not a formula that assigns one state to each removed source node.

Theory K retains the full formula schema but makes the emitted theory instance simpler. Its support condition and subset-indexed witness requirement are expressed through a single closure construction. The same numerical matrix is reused in several positions, and its code also supplies a private variable label. The proof source treats low codes, disabled gates, equal input/output labels, and the all-distinct case separately. These details are why the small emitted formula has an actual endpoint, rather than being only an attractive informal axiom.

## Equality and canonical vacuity

The supplied equality-reduction work shows that full equality vacuity can be replaced by a carefully chosen helper with a canonical binder. It also gives an instructive cost control: one exact surgical frontend has 201 decision nodes, but the packaged generic compiler produces 263 working binary states. That count includes the compiler's own startup and totalization. It is not evidence against a future specialized implementation; it establishes that a mathematical axiom simplification does not automatically transfer to a smaller literal table.

One additional source experiment here replaces the original equality-vacuity conjunct

\[
 \operatorname{Eq}(a,b)\to\forall_c\operatorname{Eq}(a,b)
\]

by canonical formula vacuity

\[
 \operatorname{dec}(a)\to\forall_a\operatorname{dec}(a).
\]

It retains all eight original logical rows, the original set-theory block, membership vacuity, the parser, and the gate `c != a,b`. Every canonical instance at code `m` is available by choosing `(a,b,c)=(m,0,m+1)`. Positive decoded codes use only lower variable labels, while code zero is the native truth alias and must be handled separately. Equality codes therefore supply the helper required by the supplied equality theorem. Retaining the original classicality row avoids a circular projection argument through the bundled negative conjunction.

The exact builder replaces three closed scalar-push subtrees. It removes 112 primitive occurrences, taking 6,455 to 6,343, and preserves depth 48 and maximum zero run 6. However, the number of distinct DAG nodes rises from 224 to 225 because sharing changes. Scalar-b and scalar-c variants have the same measured counts. This is a concrete logical/source result at the ordinary mathematical proof boundary of the supplied equality checkpoint. It has no newly compiled binary table, full modified AX binding replay, or new proof-assistant endpoint, and it is not used in the final small-machine proof.

## EPSC and finite equational search

The supplied 235-state package already contains the E663 presentation: nine operation symbols, seven equations, four available local variables, 150 equation-term nodes, and a 663-bit complete packet. Its ground query is `Q(d)=d`; the packet allocates 43 bits to its header, 608 to equations, and 12 to endpoints. The packed transport uses 83 bytes with one padding bit. These numbers are inherited measurements, not a new reduction in this work.

The attraction of this route is that a fixed contextual-rewrite searcher could replace the first-order proof checker. The required search nevertheless ranges over arbitrarily large finite contexts, substitutions, intermediate terms, and derivations. It must be fair in both rewrite directions if it is intended to recognize ordinary equational derivability. Its linked machine must also create or generate the signature, equations, and endpoints from blank tape and encode the variable arities. The 663-bit packet alone does not price that implementation.

No smaller packet or complete competitive binary rewrite engine was constructed here. In particular, an equation should not be removed merely because finite model searches fail to find a counterexample. The inherited work contains a mathematical countermodel for one tempting tail-equation deletion and explicit obstructions to two proposed symbol identifications. Those are useful constraints on the search. A breakthrough along this route would need shared initialization and matching machinery that makes the entire linked blank-tape table smaller, with the same exactness standard as the present interpreter proof.

## Finite class theories and direct ZFC

A finite NBG-style or class-kernel presentation offers a different tradeoff: a finite axiom list can simplify schema recognition, but its syntax, class operations, set/class distinction or translation guards, proof rules, and initialization still need implementation. A concrete proposal must specify its exact choice principles and derive both finite-refutation translations to the intended ZFC presentation. An axiom count alone does not settle either calibration or binary cost. No such complete smaller implementation is claimed here.

Direct ZFC proof enumeration has the clearest target syntax but must implement the Separation and Replacement instance checks, finite formulas, binding conditions, and ordinary proof rules. Theory K earns its practical advantage by reducing that source construction while preserving an existing calibrated interpreter. The successful posttest loop identity then removes only four primitive occurrences, yet creates a useful decoder sharing opportunity. That result and the unsuccessful 112-occurrence canonical-vacuity saving show why the next search should optimize distinct control subtrees, their reachable bit contexts, and full literal runtime together. Primitive-occurrence count, formula length, and packet size are useful diagnostics; the final objective remains a verified complete binary transition table.

## Reproducible sources for this assessment

- `k230_math_audit.md` and `k230_literal_bindings.json`: Theory K endpoint and exact source/table measurements.
- `canonical_v_proof.md`, `build_canonical_v.py`, and `canonical_v/certificate.json`: canonical-vacuity source experiment.
- Supplied equality package, `frontend/generic_cost.json` and `source.tex`: exact generic surgical frontend cost and proof scope.
- Supplied 235 package, `formalisms/e663/generated/E663.json` and `formalisms/README.txt`: complete inherited packet accounting and stated nondeletion results.
