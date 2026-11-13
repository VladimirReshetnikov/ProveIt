SYMBOLIC CERTIFICATE FOR THE GENERIC DIAGONAL PREDECESSOR LEMMA
============================================================

Purpose and limits
------------------
This package mechanically checks one finite symbolic derivation. It does
not evaluate natural numbers, search for a proof, or rely on finite numerical
examples. It verifies 37 explicit equality-proof nodes containing exactly
two applications of literal-equation induction.

This is not a complete iPRA checker, a new Lean/Rocq formalization, a proof
of all upstream factor-map identities, or a checker-size record. It proves
the generic diagonal lemma conditionally on the five fixed schematic laws
below and on the stated equational induction rule. Applying it to a concrete
updater requires the separately supplied mathematical proofs of the three
F laws. W is an abbreviation for I(t,0;u.F(n,u)); its two laws follow from
the ordinary iterator computation equations.

Run
---
  sh build.sh

Or check the already supplied certificate, without running its producer:

  python3 verify_certificate.py certificate.json
  python3 run_checks.py

The verifier uses only Python's standard library. The recorded verification
ran on CPython 3.12.14. Python assertions are not used for validity checks;
normal and optimized (-O) executions agree on all supplied controls.

Fixed mathematical signature
----------------------------
One sort, a constant 0, a unary symbol S, and binary symbols F and W.
There is no computation/evaluation oracle. Let 1 abbreviate S0.

The kernel contains exactly these five universally schematic equality laws:

  W0:    W(0,n) = 0
  WS:    W(St,n) = F(n,W(t,n))
  F10:   F(1,0) = 0
  FSS0:  F(SSn,0) = 1
  FS:    F(Sn,Su) = S F(n,u)

The certificate cannot supply additional axiom schemes. It can instantiate
these schemes by arbitrary well-formed terms. The three F laws are the
hypotheses of the generic diagonal lemma, not claims about an unspecified
arbitrary binary operation.

Kernel rules
------------
Every proof node has an explicit context of literal equations and an
explicit equality conclusion. The verifier checks reflexivity, symmetry,
transitivity, function congruence, hypothesis use, axiom instantiation,
simultaneous variable substitution, weakening, and equation induction.
References must point strictly backward, so the certificate is a finite
acyclic derivation. Unknown symbols, arities, rules, and unexpected fields
are rejected. Substitution changes the entire context along with the
conclusion; it never substitutes recursively inside an inserted image.
Terms have no binders, so this is capture-free first-order substitution.

Weakening is an explicit structural rule: every old assumption must occur
in the new context and the equation must remain unchanged. It is used to
reuse the completed first theorem under the second induction hypothesis.

For equation induction, write E(x) for the supplied equation template.
The rule requires proofs of

  Gamma |- E(0)
  Gamma, E(z) |- E(Sz)

and concludes Gamma |- E(a). The certificate supplies x, z, a, the template,
and both proof references. The verifier checks that z is absent from Gamma,
from the parameters of E other than x, and from a; it also requires z != x
and x absent from the fixed context Gamma. The base, hypothesis, step, and
target equation must literally match the corresponding substitutions.
Thus induction over a quantified formula cannot be silently substituted
for the required literal-equation induction.

Checked conclusions
-------------------
  orbit_conjugacy:
      W(St,SSn) = S W(t,Sn)

  predecessor_successor:
      W(Sn,Sn) = n

  predecessor_zero:
      W(0,0) = 0

Putting P(n)=W(n,n) gives P(0)=0 and P(Sn)=n. The first induction fixes n
and varies t. The second induction reuses the COMPLETED first theorem with
t:=Sr and n:=r. The certificate's substitution rule checks this step,
followed by explicit weakening into the second hypothesis context. No
parameter of an active induction hypothesis is changed.

Syntax
------
  ["0"]                  zero
  ["v", "n"]             a named variable
  ["S", term]            successor
  ["F", term, term]      F application
  ["W", term, term]      W application

An equation is [left,right]. A context is a list of equations.
certificate.json contains the complete derivation. The verifier reports
the actual concluding equations, not just user-supplied theorem names.

Files
-----
  certificate.json             The complete 37-node symbolic derivation.
  verify_certificate.py        Transparent trusted proof-checking kernel.
  build_certificate.py         Untrusted producer, separate from checking.
  run_checks.py                Isolated-process regression and boundary checks.
  build.sh                     Rebuild and verify all supplied artifacts.
  negative_*.json              Four invalid certificates and their manifest.
  verification.json            Recorded normal/-O execution results.

Negative controls
-----------------
The controls deliberately change a theorem endpoint, replace an induction
step with its unadvanced induction hypothesis, capture a fixed parameter
as the induction eigenvariable, and substitute in a conclusion while
leaving its assumption unchanged. All four are rejected for the specified
reason in both normal and optimized executions. Together with the positive
certificate, this gives 10 isolated executions and zero failed checks.
These controls test concrete trust-boundary mistakes; they do not replace
the mathematical soundness argument for the inference rules.

Soundness argument
------------------
Induct over proof-node order. Axioms instantiate a fixed schematic law;
hypotheses belong to the explicit context; the four equality operations
preserve equality. Substitution acts simultaneously on assumptions and
conclusion, and weakening only adds assumptions. The induction rule is an
instance of literal-equation induction because its eigenvariable and all
four equation instances are checked explicitly. Every reported theorem
has an empty context. Consequently acceptance of the supplied certificate
establishes the displayed universal equations in the stated schematic
equational theory. Physical runtime/recursion limits can prevent checking
oversized files; no claim about a total resource-unbounded parser is made.
