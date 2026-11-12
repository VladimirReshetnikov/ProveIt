GUARDED SCALAR J: COMPLETE STRICT CHECKERS AND CERTIFICATES
=========================================================

Primary result and claim boundary
---------------------------------
checker_j.py implements the final guarded scalar J calculus with TWO
unconditional computation axioms. There is no primitive successor
constructor, independent initializer field, Increment rule, conditional
Load rule, or equality-reflexivity rule. checker_i.py is a matched strict
control for the established scalar-iterator presentation. Both use the
same logical rules, variable representation, runtime validation, JSON
interface, substitution operation and acceptance convention.

Measured complete normalized source, CPython 3.12.14:

                         significant tokens   AST nodes   normalized bytes
  scalar I control               1045           1193            3566
  guarded scalar J               1041           1181            3467
  J minus I                        -4            -12             -99

This is a matched reduction in all three coordinates (99 bytes, 2.78%).
It DOES NOT beat the repository's coordinatewise compact-checker frontier,
and DOES NOT establish absolute minimality. The match compares these two
fully specified implementations; it is not a lower bound on all I checkers.
All trusted validation and checking code is included in each measured file.
Neither checker imports the proof producer, measurements, or this README.

Input and acceptance
--------------------
A certificate is a JSON array [goal, proof]. Whitespace and line breaks are
allowed. A successful process exits with status zero and writes exactly
ACCEPT followed by a newline. Any exception or resource failure rejects.
The checkers import only Python's json module. They read no theorem files
and perform no network access. Validation uses explicit runtime require()
conditions; python -O does not disable it.

Numeric syntax uses de Bruijn indices starting at 1. Integer 0 is the numeric
constant zero; positive integer i denotes the i-th nearest numerical binder
or local parameter. Negative integers, booleans, floats, strings, invalid
arities, invalid tags and out-of-scope indices are rejected as terms.

  guarded J term:  0 | i | ["j", n, h]

The body h binds its local state as index 1; n introduces no binder. The
successor abbreviation is S(a) = ["j", a, 0]. Every J body must already be a
well-formed term and must satisfy at least one of these literal conditions:

  (1) the local state does not occur free in h; or
  (2) h is exactly ["j", g, 0], namely S(g).

The guard is checked at EVERY J occurrence, including terms appearing only
inside auxiliary proof nodes. Passive outer parameters are allowed in
constant bodies. The state-free test is subst(h, (0,), 1) == h: it replaces
the current state by zero while preserving every outer index. No equation
prover or arithmetic normalizer is used in the grammar check. At a nonconstant
body the recursive term validator has already established that a compound
term has precisely the J tag and arity. Thus checking its final field for
literal zero exactly recognizes S-headedness; indexing a bare local-state
variable rejects it by exception.

  scalar I term:  0 | i | ["s", a] | ["i", n, a, h]

The body h of I binds its state as index 1; n and a introduce no binder.
There is no body restriction in the I control.

  formula: ["=", s, t] | ["q", B] | ["d", B]

Q binds y as index 1. D binds y as index 1 and x as index 2. Their ordinary
readings are Q_y B = (B(0) -> forall y B(y)) and
D_(x,y) B = exists x (B(x,0) -> forall y B(x,y)). The designated contradiction
is 0 = S(0). The public command-line interface requires a closed goal.

The TWO arithmetic proof nodes for J
-----------------------------------
  ["j0", h]
    yields J(0;u.h) = S(h(0)).

  ["js", n, g]
    constructs the guarded body S(g) and yields
    J(S(n);u.S(g)) = g(J(n;u.S(g))).

Here g is a numerical term with one local-state variable. The second node
has NO equality premise and NO supplied output witness. Both nodes validate
the entire constructed J term, so a forbidden body cannot enter through an
auxiliary computation. Their conclusions are terms, not values obtained by
executing an iteration.

The TWO arithmetic proof nodes for the I control
-----------------------------------------------
  ["i0", a, h]
    yields I(0,a;u.h) = a.

  ["is", n, a, h]
    yields I(S(n),a;u.h) = h(I(n,a;u.h)).

The SIX shared logical proof nodes
---------------------------------
  ["hyp", index]
    returns the indexed retained hypothesis (oldest hypothesis has index 0).

  ["tr", H, p, q]
    H is a one-variable term template. If p proves s=t and q proves H(s)=r,
    the result is r=H(t). This is crossed transport. Equality reflexivity,
    symmetry, transitivity and congruence are derived, not primitive.

  ["qe", t, p, q]
    p proves Q_y B(y), q proves B(0), and the result is B(t).

  ["de", p, q]
    p proves D_(x,y) B. The branch q runs with a fresh numerical parameter b
    and the retained hypothesis Q_y B(b,y). The result must not mention b;
    the checker tests subst(result, (0,), 1) == result before removing the
    fresh parameter from the scope. That result is then exported.

  ["di", B, t, p]
    B is a two-variable formula and t belongs to the outer scope. The branch
    p runs under a fresh z and the retained hypothesis B(t,0), and must prove
    B(t,S(z)). Its result is D_(x,y) B.

  ["qi", E, p]
    E must be a literal equation with one additional numerical variable.
    The branch p runs under a fresh z and hypothesis E(z), and must prove
    E(S(z)). Its result is Q_y E(y). Induction on quantified formulas is
    rejected.

There are eight primitive patterns in each checker: the two computations
and these six logical rules. Equality is actual numerical equality in the
ordinary realization, as specified in the mathematical report.

Executable evidence
-------------------
  python3 reproduce.py
  python3 symbolic.py
  python3 checker_j.py < certificates/j/positive/load_state_dependent.json
  python3 -O checker_j.py < certificates/j/positive/load_state_dependent.json

reproduce.py regenerates the closed fixtures and evidence.json. It measures
the entire standalone sources using ast.unparse plus a final newline and
runs 108 subprocess checks in ordinary and optimized Python: 48 accepts,
60 rejections, zero mismatches. Tests exercise every primitive pattern,
derived reflexivity, scope, escaping witnesses, future witnesses, removal
of the old conditional arithmetic rules, quantified induction rejection,
exact integer typing, malformed shapes, and the guard inside auxiliary
axioms. It also checks valid state-free passive parameters under binders,
valid successor-headed state dependence, and guard preservation for specific
capture-avoiding substitutions.

symbolic.py is an UNTRUSTED producer for twelve symbolic equation certificates:

  f(0,a)=S(a)                   f(S(n),S(a))=a
  W(S(x))=x                    W^3(0)=0
  Z(0)=1                       Z(S(n))=0
  G(0,a)=0                     G(S(n),a)=a
  C(0,a,b)=a                   C(S(n),a,b)=b
  P(0)=0                       P(S(n))=n

The exact f/W/Z/G/C/P macros are defined in that script and in the report.
All twelve certificates use only j0, js and tr; they use no induction,
coverage, quantifier rules or assumed equations. Every result is verified
by checker_j.prove with an EMPTY hypothesis context and the stated number
of arbitrary numerical parameters. symbolic_evidence.json records their
scopes and sizes. These open certificates have a {scope, goal, proof} wrapper
and are checked through the kernel API, not the closed-goal CLI. A closed
Q-closure certificate for W(S(y))=y is also in the ordinary CLI suite.

Assurance and limits
--------------------
The finite certificates check substantive instances of the algebraic
bootstrap and implementation boundaries. They do not prove the general
scalar-iterator compiler, uniqueness, interpretation composites, or global
soundness. Those are written mathematical arguments in the accompanying
report. Neither this checker nor the new arithmetic bridge is claimed to
be verified in Lean or Rocq. Independent same-run assistant review is
recorded separately and is not external human peer review.
