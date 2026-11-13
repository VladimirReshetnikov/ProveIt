SELECTIVE NORMALIZATION: SIX-RULE REFERENCE CHECKER

Purpose and status
------------------

selective_checker.py is a readable standalone reference implementation of
the selectively normalized calculus developed in the accompanying report.
It is not a compact checker and is not below the repository's size frontier.
It contains six primitive rule cases: Hyp, IS, VSub, QE, DE, WI. Reflexivity
is derived by a specific instance of IS; it is not a primitive checker case.

The mathematical soundness, completeness and bi-interpretation arguments
are paper proofs in the report. This code is not a Lean/Rocq formalization,
and the finite test suite is not a proof of those metatheorems. In particular,
there is no supplied mechanical compiler from arbitrary native derivations.

Run
---

    python3 selective_checker.py < fixtures/closed_all_six_rules.json
    python3 test_selective.py

The first command prints ACCEPT. The second regenerates the examples and
verification.json, measures the complete checker and checks the expectations.
The closed-theorem interface accepts exactly one JSON object with the fields
goal and proof. It admits no initial assumptions or free numerical parameters.
An explicit internal check_proof API is used only by the test harness to
verify open-sequent rule examples with declared assumptions and parameters.

Syntax
------

Numerical terms are:

    0                         numerical zero, the exact JSON integer
    "x"                       a numerical variable
    ["S", t]                  successor
    ["I", n, a, "u", h]       iteration, binding u in h only

Variable names are nonempty strings. Booleans, floats and other integer
literals do not abbreviate zero or numerals. Numerals are nested S at 0.

Formulas are:

    ["=", s, t]
    ["Q", "y", B]
    ["D", "x", "y", B]

The two variables bound by D must have distinct names. Nested binders may
shadow names. Substitution avoids capture; formula matching compares alpha-
equivalence after normalization through canonical keys with de Bruijn
indices for bound occurrences. It does not compare fresh binder spellings
literally. The ordinary readings are

    Q_y B(y)       = B(0) -> forall y B(y)
    D_{x,y} B(x,y) = exists x (B(x,0) -> forall y B(x,y)).

The designated contradiction is 0=S(0). The intended arithmetic domain is
the whole numerical domain and equality is actual equality, as established
by the paper's interpretations.

Selective normalizer N2
-----------------------

Normalize subterms and apply these reductions wherever applicable:

    I(0,a;u.h)       -> a
    I(1,a;u.h)       -> h[a/u]
    I(2,a;u.h)       -> h[h[a/u]/u]
    I(S(n),a;u.h)    -> h       when u is absent from h.

The last rule applies after the body has itself been normalized, so an
occurrence of u erased by an earlier reduction causes no obstruction.
General successor evaluation remains an explicit axiom. For example,
I(3,0;u.S(u)) remains an iterator in normal form and is not equal to 3 by
normalization alone.

The implementation uses an environment evaluator on original syntax.
At an iterator it evaluates the original counter and seed. A normalized
counter of 0 returns the seed. A counter of 1 or 2 evaluates the original
body once or twice under the appropriate already normalized state value.
For any other counter it evaluates the original body under a fresh symbolic
state variable, then either removes a state-free successor iteration or
retains the iterator. No recursive call receives a newly constructed
substitution instance. An activation has at most four recursive children,
each on a strict subterm of the original term.

Fresh naming is handled modulo alpha-equivalence. N2 is alpha-idempotent,
not necessarily byte-for-byte idempotent on named JSON syntax. The proof's
bound on evaluator activations does not claim polynomial output size or
constant-time capture/substitution operations. The program uses ordinary
finite Python resources; completeness is the ideal unbounded-resource
notion for finite mathematical certificates.

Primitive rules and proof records
--------------------------------

All displayed judgments are compared after N2 and alpha-equivalence.
Raw hints are fully scope-validated before they may be erased by N2.
Each proof object contains exactly the fields listed for its rule.

1. Hyp

   From a retained assumption A infer A.

       {"rule":"hyp"}

2. IS (the explicit general successor computation axiom)

   I(S(n),a;u.h) = h[I(n,a;u.h)/u].

       {"rule":"succ", "n":n, "a":a, "u":"u", "h":h}

   The update variable is bound in h only. The source and endpoint are
   independently reconstructed and compared to the target after N2.

   Derived reflexivity: choose n=0 and h=u. The left side reduces by the
   one-iteration clause to a; the right side reduces by zero iteration to a.
   Thus a=a is an IS instance in the quotient language. The test helper
   reflexivity(a) emits this actual successor-axiom record. A record with
   rule="refl" is rejected.

3. VSub (substitution whose source is a numerical variable)

   From x=t and l=r infer r=l[t/x].

       {"rule":"vsub", "x":"x", "t":t, "u":l, "v":r,
        "major":proof_of_x_equals_t, "minor":proof_of_l_equals_r}

   The source x must be an available numerical variable. Composite terms
   cannot be used in the x field. The replacement is capture-avoiding and
   affects l only; r is the unchanged left endpoint of the conclusion.

4. QE (conditional-closure elimination)

   From Q_y B(y) and B(0) infer B(t).

       {"rule":"qe", "y":"y", "body":B, "t":t,
        "major":proof_of_Q, "base":proof_of_B_zero}

5. DE (paired-binder elimination)

   From D_{x,y} B and a derivation of A under the additional assumption
   Q_y B(b,y), infer A. The numerical parameter b is fresh.

       {"rule":"de", "x":"x", "y":"y", "body":B, "b":"b",
        "major":proof_of_D, "minor":proof_of_A_with_opened_clause}

   The original goal is checked outside the scope of b, so b cannot leak
   into the exported conclusion. The major is proved before b is allocated.

6. WI (witness-selected introduction)

   From a derivation of B(t,S(z)) under the additional assumption B(t,eta),
   infer D_{x,y} B. The numerical parameter z is fresh. The mode is

       eta = z if raw B is an equation and raw t is the literal integer 0;
       eta = 0 otherwise.

       {"rule":"wi", "x":"x", "y":"y", "body":B, "t":t, "z":"z",
        "step":proof_of_successor_instance_with_base_assumption}

   This is a test on raw supplied syntax. A compound term that normalizes
   to zero does not select progress. The witness t is validated before z
   enters scope, which rejects future-witness capture. All actual base and
   successor instances are normalized for judgment comparison.

Nontrivial closed certificate
----------------------------

fixtures/closed_all_six_rules.json proves

    3 = I(3,0;u.S(u))

using every primitive rule. It first introduces the naming packet

    D_{x,y}(C(y,0,x)=0),    C(y,a,b)=I(y,a;u.b),

at witness 0. DE opens it at b. QE at 1 yields b=0; its zero premise is
derived by IS with the identity update. VSub at source b with a constant
template then reverses the explicit successor axiom
I(3,0;u.S(u))=3. The result is closed and can be exported from the DE branch.
Hyp supplies the opened closure. The iterator at counter 3 remains in the
normal form, so this example requires actual proof rules and cannot pass
merely because the normalizer computes the target.

Verification and limitations
----------------------------

The latest verification.json records 16 closed-certificate cases checked in
normal Python and Python -O, for 32 CLI executions. Six examples are accepted;
ten invalid certificates are rejected. The invalid cases exercise the raw
zero-witness distinction, future witness capture, reuse of an eigenvariable,
a composite VSub source, a leaked free parameter, a false equation, a wrong
successor endpoint, a Boolean zero alias, accidental full normalization,
and a nonexistent primitive reflexivity rule.

Further internal checks exercise capture avoidance, alpha-equivalence,
state-free reduction after an erased dependency, and VSub/QE on declared open
sequents. Sixty generated finite terms satisfy the implementation checks for
alpha-idempotence, preservation of free-variable bounds, substitution
coherence and the stated activation bound. Their ordinary numerical values
agree before and after normalization for 540 parameter assignments. These
are executable checks, not exhaustive mathematical proofs.

Measured complete standalone checker under CPython 3.12.14:

    significant Python tokens        2662
    all AST nodes                     2904
    normalized UTF-8 bytes           13172
    actual source UTF-8 bytes        13340

Normalization of source means ast.unparse(ast.parse(source)) plus one final
LF. Tokens exclude comments, indentation/dedentation, line separators and
the end marker; docstrings and every actual checker dependency in the module
are charged. Only the Python standard library is imported. The test harness
is outside the trusted checker and is not part of that source measurement.

The size is much larger than the current compact frontiers. The mathematical
proposal therefore supplies a different reference calculus and a restricted
normalization theorem; it does not establish the requested software-size
breakthrough. The mathematical report must retain this distinction.
