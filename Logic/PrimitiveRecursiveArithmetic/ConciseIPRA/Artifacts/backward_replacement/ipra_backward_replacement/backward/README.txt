BACKWARD CROSSED REPLACEMENT: EXECUTABLE CHECKER
=============================================

This package demonstrates the eight-rule native calculus with backward
crossed replacement (BRep) in place of arbitrary equality transport.
It is a transparent correctness demonstrator. It is not claimed to beat
the repository's compact-checker size envelope or to be formally verified.

Requirements and reproduction
----------------------------

Python 3 and its standard library suffice. The supplied measurements were
made with CPython 3.12.14, matching the repository's normalization protocol.

    python3 test_checker.py
    python3 compare_checkers.py
    python3 checker.py < fixtures/positive/brep_reflexivity_closed.json

The first command regenerates all fixtures, checker.normalized.py and
test_results.json, and checks all examples. The second prints ACCEPT and
exits with status zero. Invalid certificates print REJECT to standard error
and exit with nonzero status. Resource exhaustion can reject a valid large
certificate; mathematical completeness uses unbounded finite resources.

The public stdin driver accepts closed theorems only. An open-sequent
fixture is intended for the Python verify API, and its rejection by the
closed-theorem driver is tested explicitly.

Public certificate object
-------------------------

Exactly four fields are required:

    {"n": 0, "context": [], "goal": FORMULA, "proof": PROOF_NODE}

The driver requires n = 0 and context = []. For an open sequent use:

    import checker
    checker.verify(n, context, goal, proof)

verify returns None on success and raises InvalidCertificate on failure.
Its parameter n is a nonnegative integer. The free numerical parameters
are indexed 0,...,n-1. A fresh eigenparameter is appended at index n;
existing parameters keep their indices. Every context formula, goal,
term supplied by a rule, and recursive premise is checked for scope.

Term syntax
-----------

    i             numerical variable, an integer with 0 <= i < scope
    []            numerical zero
    [t]           successor S(t)
    [n, a, h]     iterator I(n,a;u.h)

Only h binds one variable. Its bound state variable is index 0. Free
parameters and any enclosing bound variables shift by one under that
binder. A variable is an actual Python integer, not a Boolean. Floats,
strings, null values, objects and arrays of other arities are not terms.

The notation [] for zero is deliberately distinct from the integer 0,
which is a variable index. Thus [[]] represents the numeral one, whereas
[0] represents the successor of variable 0 in a nonempty scope.

Formula syntax
--------------

    [s,t]         equality s = t
    [B]           D_{x,y} B, with y at index 0 and x at index 1
    [0,0,B]       Q_y B, with y at index 0

The first two entries in a Q formula are literal integer tags, not terms.
They must be integers 0; Boolean False is not an alias. Nested formula
binders shift all enclosing variables by their number of bound variables.

The ordinary readings are:

    Q_y B(y)      B(0) -> forall y B(y)
    D_{x,y} B     exists x (B(x,0) -> forall y B(x,y))

Proof-node schemas
------------------

All objects below have exactly the stated fields; extra fields reject.

1. {"rule":"hyp", "index":j}
   The goal must equal context[j]; j is a nonnegative integer in range.

2. {"rule":"i0"}
   The goal must literally be I(0,a;u.h) = a.

3. {"rule":"is"}
   The goal must literally be
   I(S n,a;u.h) = h[I(n,a;u.h)/u].
   The substitution is capture avoiding, including under nested iterators.

4. {"rule":"brep", "equality":[s,t], "major":P, "minor":R}
   If the goal is r = u, P must prove s = t and R must prove
   Rep_t^s(u) = r in the same context and scope.

   Rep is one top-down pass. At a subterm exactly equal to the appropriately
   shifted t, insert the appropriately shifted s and stop traversing that
   occurrence. Otherwise recurse. Inserted copies of s are not revisited.
   Both patterns are shifted when entering an iterator body. All matching
   outermost occurrences are replaced, including passive occurrences;
   this is not a certificate-directed occurrence-selection operation.
   The source s may be numerical zero.

5. {"rule":"qe", "body":B, "term":t, "major":P, "base":R}
   B is scoped under one extra numerical binder and t is in the current
   scope. P proves Q_y B, R proves B(0), and the goal must be B(t).

6. {"rule":"de", "matrix":B, "major":P, "branch":R}
   P proves D_{x,y} B. R proves the unchanged goal under the current
   context extended by Q_y B(b,y), with the new parameter b at index n.
   R is checked at scope n+1. The original goal and context are checked
   at scope n, so b cannot escape into either.

7. {"rule":"di", "witness":t, "premise":P}
   The goal must be D_{x,y} B. The witness t must be scoped at n. P proves
   B(t,S z) under context plus B(t,0), at scope n+1 with z at index n.

8. {"rule":"qi", "premise":P}
   The goal must be Q_y E(y), where E is a literal equation. P proves
   E(S z) under context plus E(z), at scope n+1 with z at index n.
   Progress introduction on a compound formula is rejected.

What the tests establish
-----------------------

There are positive cases for all eight primitive rules, both numerical
zero and nonzero replacement sources, actual nonconstant progress, and
nonempty parameter scopes. Complete generated BRep certificates recover
term congruence using fresh computational markers. The templates include
passive copies of the source, repeated holes, an unused hole, and one or
two nested iterator binders.

Negative tests cover both replacement-capture errors, wrong computation
endpoints, an escaping eigenparameter, an out-of-scope witness, malformed
terms and tags, a non-equational progress matrix, mismatched closure
instances, extra proof fields, invalid hypothesis indices and an unknown
rule. Direct operation tests check capture avoidance under D, Q and I,
the retained y binder, and the absence of cascading replacement inside
the inserted source.

These finite checks supplement the accompanying mathematical equivalence
argument. They do not constitute a proof-assistant verification of the
checker or a machine-checked proof of bi-interpretability.

Measurement contract
--------------------

test_checker.py recursively removes module/function/class docstrings,
reconstructs the entire module using ast.unparse, and appends one final
line feed. Comments disappear during AST reconstruction. It then counts
significant Python tokens, AST nodes of the reconstructed complete module,
and UTF-8 bytes. Imports, strict syntax/scope validation, all eight rules,
the input driver and rejection/acceptance handling are included.
Measurements retaining docstrings are reported separately for clarity.
The normalized program is also supplied as checker.normalized.py.

The reference module is intentionally verbose. Its sizes must not be
compared as evidence of a strict improvement against compact checkers
with a different public input contract.

Matched one-term transport control
----------------------------------

checker_control.py has the same syntax, strict scope checks, seven other
rules, open-sequent API and closed-theorem driver. Its only executable
changes are removal of replace_term and replacement of the BRep branch by
ordinary one-term crossed transport. The comparison script verifies that
the source is exactly this prescribed local transformation.

The control's equality-rule node is:

    {"rule":"tr", "equality":[s,t], "template":H,
     "major":P, "minor":R}

H is a term in scope n+1, with its designated hole at index 0. At goal
r = H(t), P proves s = t and R proves H(s) = r. All substitutions use the
same capture-avoiding routine as the other rules. The checker verifies
that the goal's right side is literally the stated instance H(t).

compare_checkers.py checks the ten common-rule fixtures in both modules
(replacing only the fixed Refl proof macro inside them), and checks one
additional control congruence certificate using H(v)=I(v,s;w.s).
The latter is supplied as tr_congruence.json for the open-sequent API.

Under CPython 3.12.14 and the normalization above:

                         Tokens    AST nodes    Normalized bytes
    one-term Tr control    1581         1738                6971
    BRep candidate         1647         1807                7121
    candidate - control     +66          +69                +150

Thus removing a template field from the certificate does not remove all
of its checking cost: BRep adds a trusted traversal for replacement.
This matched readable implementation is larger in all three coordinates.
No checker-size improvement is claimed. comparison.json records the
measurements, exact source hashes and results of the eleven comparison
checks. The BRep candidate module itself is unchanged by this comparison.
