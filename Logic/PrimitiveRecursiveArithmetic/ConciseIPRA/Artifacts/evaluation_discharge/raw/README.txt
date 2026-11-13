RAW THREE-FAMILY IPRA CHECKER
===========================

checker.py is the complete standalone acceptance program. It uses raw terms:
there is no numerical normalizer, fuel field or supporting proof oracle.
control.py is a matched four-family program with separate Eval and Open.
The accompanying mathematical report proves the exact open-sequent equivalence.

Run from any working directory:

  python3 /path/to/raw/verify.py
  python3 /path/to/raw/measure.py
  python3 /path/to/raw/checker.py < /path/to/raw/examples/used_induction_hypothesis.json

Only the standard Python library is required. Structural pattern matching
requires Python 3.10 or later; metrics were measured with CPython 3.12.14.
Acceptance means exit zero and exactly ACCEPT on standard output. Any
exception, nonzero exit, parser failure or resource failure is rejection.

CERTIFICATE FORMAT
------------------
The input is exactly an object with goal and proof fields. The goal is closed.
Terms: 0 is zero; negative integers are free numerical levels; positive
integers are de Bruijn indices; [0,t] is successor; [n,a,h] is iteration,
with only h binding one variable. Formulas: [s,t] is equality, and [B] is D
binding two variables, inner index1 and outer index2. Booleans are not integers.

At a context of n clauses, levels -1 through -(n-1) are available and the
next fresh parameter is -n. A clause is (base,body), base=[] for an
unconditional clause, or a formula for a conditional clause. body has one
bound variable. Every proof begins with ([],[1,1]), universal reflexivity.

The three proof instructions are:

  ['u', j, t, q]
      Use context clause j at t. If it has a base, q must prove that base.
      If its base is empty, q is inert and ignored; examples use null.

  ['i', B, t, p]
      Prove D B. Substitute witness t for B's outer bound variable.
      Add the resulting equation/formula at z if B is an equation and t=0,
      and at 0 otherwise, as an unconditional assumption. p must prove the
      resulting formula at successor of fresh z. B, t and the conclusion
      are all checked for syntax and scope.

  ['e', major, auxiliary, branch]
      major proves D B. At fresh b, add the clause B(b,0)->forall y B(b,y).
      auxiliary proves E and branch proves F in that same extended context.
      If E=s=t and F=I(0,s;u.h)=r, return r=t.
      If E=I(c,a;u.h)=t and F=I(S c,a;u.h)=r, return r=h[t/u].
      Otherwise return F unchanged. The returned formula must be valid in
      the OUTER scope, so the fresh witness cannot escape. The literal
      source matches are essential. E may be compound; then F is unchanged.

All terms remain raw in every instruction. In particular I(0,a;u.h) and a
are distinct syntax. All substituted targets are locally closed with respect
to bound indices, so opening does not require a separate lifting traversal.

EVIDENCE
--------
verify.py currently passes 33 pinned reference certificates, 38 accepted
fused certificates, 38 exact-goal control roundtrips, 38 reverse expansions
into the independently implemented pinned raw checker, 34 adversarial
rejections, and 144 ordinary/optimized Python CLI checks. The examples include
real use of an induction hypothesis, nested formula binders, capture-avoiding
opening, nontrivial nested congruence, and witness erasure in both evaluation
cases. Five positive and seven negative fixtures were independently written.

These finite tests support the implementations; the universal mathematical
equivalence is a written proof, not a newly checked Lean development.

Complete normalized source: 1892 bytes,643 tokens,695 AST nodes,773 gzip9 bytes.
Matched separate control:   1995 bytes,665 tokens,717 AST nodes,786 gzip9 bytes.
The comparison counts every parser, syntax/scope check, inference and CLI line.
It is not a global source-size record or an absolute minimality theorem.

FILE MAP
--------
checker.py/control.py          Complete selected and matched acceptance modules.
*_normalized.py                Measured equivalent source text.
translations.py                Untrusted proof compilers, both directions.
verify.py/measure.py            Reproduction, independent replay and metrics.
examples/                      Accepted fused proofs.
reject_examples/               False, malformed and scope-violating inputs.
reference/raw_two_case.py       Pinned independently implemented source checker.
reference/raw_cases/            Pinned original source fixtures.
evidence/                      Executed metrics and verification results.
PROVENANCE.json                 Source revision, paths and SHA-256 hashes.

Reproduction overwrites generated examples and evidence. It performs no
downloads, account access or repository mutations. Concrete Python resource
limits can reject very large valid finite certificates.
