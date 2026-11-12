ATOMIC-SEED ZERO CONTRACTION: STRICT REFERENCE CHECKER
====================================================

This is an independent executable reference for the six-family theory in
the accompanying atomic_seed_section.tex. It is a mathematical reduction in
the number of primitive rule families, NOT a new compact checker record.

The primary presentation permits every well-scoped successor-computation
seed and every well-scoped crossed-transport source. In particular, no
nonzero-seed or nonzero-source restriction is imposed here.

TRUST BOUNDARY

code/atomic_seed_checker.py is a complete standalone acceptance module. It imports
only Python's json and sys modules, validates its closed raw goal and every
active raw rule field, performs capture-avoiding substitution, normalizes,
and checks the proof tree. It imports no theory-specific checker or producer.

Every raw schema body is retained until AFTER its substitutions. The partial
normalizer contracts I(0,a;u.h) only when the normalized initializer a is
the literal zero or a variable. It preserves every formula constructor.
The normalizer is NOT a congruence with substitution into already normalized
metadata. evidence/normalization_examples.json records a concrete counterexample.

The candidate validates arbitrary closed native Eq/Q/D goals. This is a
different public interface from the tiny guarded Eq/D compact checkers;
their byte measurements cannot be compared as identical contracts.

SYNTAX (ZERO-BASED DE BRUIJN INDICES)

  term = ["z"] | ["v",i] | ["s",term] | ["i",counter,seed,update]
  formula = ["=",term,term] | ["q",body] | ["d",matrix]

An iterator binds index 0 only in update. Q binds y at index 0. D binds
y at index 0 and x at index 1. All variable and hypothesis indices must be
exact Python integers, not booleans. The public goal has numerical scope 0.

The top-level JSON object has exactly the fields "goal" and "proof".
Proof nodes are:

  ["hyp",context_index]
  ["step",raw_counter,raw_seed,raw_update]
  ["tr",raw_source,raw_target,raw_term_template,raw_right,
        equality_proof,minor_proof]
  ["qe",raw_body,raw_target,major_proof,base_proof]
  ["open",raw_matrix,raw_exported_goal,major_proof,branch_proof]
  ["intro",raw_matrix,raw_witness,branch_proof]

Their interpretation is exactly the six families Hyp, IS, crossed one-term
Tr, QE, DE, and DI. Each required premise and conclusion is normalized only
after the raw schema instance is constructed. Contexts contain normalized
formulas. An open or introduction branch adds a fresh numerical parameter,
shifts every retained hypothesis, and adds its new normalized hypothesis.

DI uses progress only when its RAW matrix is an equation and its RAW
witness is literal ["z"]. Otherwise it uses cases. The raw witness
I(0,0;u.0) is not the literal zero, although it normalizes to zero; this is
how the mathematical proof recovers the exceptional case introduction.

The transport rule has premises N(s=t) and N(H[s]=r), and conclusion
N(r=H[t]); H is a raw numerical term with one additional variable.

ZERO COMPUTATION IS DERIVED

The schema I(0,t;u.h)=t is not primitive. First, successor computation at
counter 0, seed S0, and constant update t gives L=t. Crossed transport of
that equation with itself gives t=t. DI therefore proves D_xy(y=y), and DE
provides Q_y(y=y).

For raw B(y) := I(0,y;u.h)=y, normalization gives

  N(Q_y B) = Q_y(y=y),     N(B(0)) = 0=0.

QE at t now yields N(I(0,t;u.h)=t), even when t is compound. If B were
normalized before the target substitution, this proof would produce only
t=t. reject_erased_qe_body.json tests this distinction explicitly.

MATCHED CONTROL

reference/atomic_raw_control.py uses the same tagged term/formula language, raw
metadata, validation, substitution, and six existing families. Its
normalizer is the identity, and it adds

  ["zero",raw_seed,raw_update]

as an explicit seventh family. It accepts its primitive zero computation
and rejects the candidate's normalized-major raw-Q proof. It is a matched
illustrative control, not the repository's global smallest checker.

REPRODUCE

Run these commands from the archive root:

  python3 tests/make_atomic_certificates.py
  python3 verify_atomic_seed.py

The producer is untrusted. Every generated positive proof is replayed by
the standalone checker. verify_atomic_seed.py also executes all positives and negatives
under isolated ordinary and optimized Python and measures both complete
modules using ast.unparse plus one final LF. Significant tokens exclude
only layout and comments; every AST node is counted.

The recorded run performs 54 checker executions with zero failed
expectations. The 20 persisted fixtures include ten positive derivations:
general reflexivity, a reflexive closure, nested logical binders, an equation
induction using its hypothesis, specialization of that induction, zero
computation at a compound seed, a nested-binder update, and successor
computation at literal zero, and case introduction with a raw zero alias whose
case assumption is used. Changing that alias to literal zero is rejected
because it switches the mode to progress. Negative fixtures exercise erased metadata,
0=1, a false computation result, two eigenvariable escapes, negative and
boolean hypothesis indices, update scope escape, and the deleted zero rule.
Additional malformed JSON-tree cases are supplied by verify_atomic_seed.py.

RESULT LIMITS

The measured candidate is larger than this matched raw control. It is not
claimed to beat the 248-token / 270-AST / 479-byte compact coordinate
envelope. These finite implementation tests supplement the general written
equivalence proof; they are not a Lean/Rocq formalization, a soundness proof
by exhaustive testing, or an absolute minimality result.
