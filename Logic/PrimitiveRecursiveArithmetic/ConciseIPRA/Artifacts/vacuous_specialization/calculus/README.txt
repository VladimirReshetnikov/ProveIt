VACUOUS SPECIALIZATION FOR iPRA
=============================

The three proof-rule families are Use, Close, and Export.  None supplies
an arbitrary numerical term argument.  Use and Close choose the newest
numerical parameter, or zero in an empty scope.  Export infers its
replacement from the opened formula.

This package adds a vacuous-body case to the existing conditional_copy
Export selector.  The packet D_{x,y}(x=t) is proved by Close followed by
its constant assumption; its opened clause is a logical tautology, not
an assertion that the fresh parameter equals t.  Exporting through this
packet recovers arbitrary specialization.  Conditional copy then removes
arbitrary introduction witnesses without weakening finished proofs.

FILES
-----
checker.py
  Complete standalone closed-theorem checker. Reads one JSON [goal,proof]
  from standard input. Success prints ACCEPT and exits zero. Failure raises
  an exception or exits nonzero. No imported proof engine or axiom table.

control_newest_close.py
  Exact pinned conditional_copy/checker.py baseline, with arbitrary Use
  terms and newest-only Close. Its Export has only the old 0/1 selector.

control_liberal.py
  Exact pinned conditional_copy/control_witness.py, with arbitrary Use
  terms and arbitrary Close witnesses. This is the compiler's source.

proof_tools.py, translate.py
  Untrusted explicit proof builders and a structural source compiler.
  Antecedents are rebuilt AFTER specialization packets enlarge the scope.
  Close premises are recursively translated only as proper subderivations
  of the original source. Helper proofs are built directly, not recursively
  sent through the compiler. The target kernel rechecks every result.

test_reference.py, evidence.json
  Thirty-nine focused successful regression checks, including malformed
  syntax rejection, a used induction hypothesis, an existential witness,
  scope/context embeddings, mode changes, the old transport packet, and
  the new vacuous selector. The same script reproduces the source metrics.

verify_cli.py, cli_evidence.json
  Positive and negative command-line checks under ordinary Python and -O.

fixtures/
  Three target certificates and two liberal source certificates. The
  existential and induction target examples are compiler outputs.

SOURCE_PROVENANCE.json, LICENSE.txt
  Pinned upstream source locations, source hashes, adaptation details,
  and the inherited MIT-0 license.

RUNNING
-------
From this directory:

  python3 test_reference.py
  python3 verify_cli.py
  python3 checker.py < fixtures/reflexivity_two.json
  python3 -O checker.py < fixtures/exists_one.json
  python3 translate.py < fixtures/exists_one_liberal.json > translated.json
  python3 checker.py < translated.json

The external Python normalizer operates on finite typed terms. Operational
stack or memory limits can reject a very large finite certificate; the
mathematical completeness statement uses unbounded finite execution.

CERTIFICATE FORMAT
------------------
Numerical terms: zero 0; rigid parameters -1,-2,...; positive de Bruijn
indices; and [n,a,h] for the counter-aware successor-seeded recursor
R(n,a;i,u.h). Only h binds i,u, with u index 1 and i index 2. Successor is
S(a)=[0,a,0]. Active supplied terms must be in full canonical normal form.

Formulas: [s,t] is equality; [B] is D_{x,y}B with y index 1 and x index 2.
Its ordinary meaning is exists x (B(x,0) -> forall y B(x,y)). The initial
context is the universal-reflexivity clause ([],[1,1]). Context length n
allows rigid parameters 1-n,...,-1, and opens the fresh parameter -n.

Use packet: [j,q]. Select clause j and specialize its body at 1-n. If the
clause has an antecedent, q must prove it in the same context. Otherwise q
is ignored; null is conventional. This packet contains no numerical term.

Close packet: [B,q]. Select witness 1-n. Let base be B(1-n,0). If base is
literally [0,0], assume B(1-n,-n); otherwise assume base. The branch q must
prove B(1-n,S(-n)). Conclude [B]. All instances are normalized.

Export packet: [[],p,q]. The major p must prove [B]. Open x at b=-n.
Let body=B(b,y), base=B(b,0), and row=B(b,1), all normalized. Add clause
(base,body) and check branch q. If row is [b,r] and either base=[0,0] OR
body=base literally, replace b by r once in the branch result; otherwise
leave b unchanged. Normalize and require an old-scope result. The new
body=base case is a test on the WHOLE body, not just on its first rows.
The replacement r may itself contain b, but any surviving b rejects.

All inferred formulas are checked for exact sort, scope, and normality;
the requested goal is compared by type-exact printed representation.
Inactive payload fields can be ignored in both matched implementations.

MEASUREMENT AND CLAIM LIMIT
---------------------------
CPython 3.12.14; ast.unparse normalization plus final newline:

                       tokens    AST nodes    normalized bytes
  matched baseline       646         748                 1844
  new checker            645         745                 1830

The complete matched validator is smaller in all three coordinates. It is
not below the separate compact guarded-envelope frontier, which has a
different input contract. The universal equivalence proof is written
mathematics backed by a concrete compiler and tests; no new Lean or Rocq
verification or universal minimality theorem is claimed.
