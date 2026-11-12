ONE TERM CONTEXT FOR EQUALITY
A conservative simplification of ConciseIPRA
Prepared for Vladimir Reshetnikov - November 11, 2026

START WITH report.pdf. The complete editable source is report.tex.

RESULT
Replace native two-context transport
  s=t, a(s)=b(s)  =>  a(t)=b(t)
by the one-context crossed rule
  s=t, h(s)=u     =>  u=h(t).
Two new steps recover each old step. Conversely old transport plus derived
symmetry recovers each new step. This establishes exact consequence
equivalence for every context and formula, so the inherited bi-interpretation
with full first-order iPRA and both identity-domain composites transfer.
All terms, formulas, and the other primitive rules stay unchanged.
A seven-constructor version also composes with the existing WPrf variant.

WHAT IS MEASURABLY SMALLER
1. Within an identical explicit tagged checker design, narrowing the primitive
   equality rule changes the whole module from 3382 to 3358 normalized bytes,
   1101 to 1089 tokens, and 1160 to 1150 AST nodes. Gzip-9 stays 990 bytes.
2. Independently, strict arity-code goal validation can reuse the kernel's
   initial scope check. The kernel and all raw proof instructions are unchanged.
   Ordinary Eq/D: 824 -> 803 bytes, 373 -> 359 tokens, 426 -> 414 AST nodes;
   gzip-9: 460 -> 463. Full Eq/Q/D: 873 -> 863 bytes. Whole-certificate exact
   integer/list typing plus Eq/Q/D: 1049 -> 1039 bytes.

These are local, matched improvements. They DO NOT beat the distinct
257-token / 279-AST-node / 522-byte compact incoming envelope, whose programs
charge a different public-input contract. No absolute minimum or major new
arithmetic foundation is claimed. Compression is informational only.

FILES
  report.tex, report.pdf       Complete presentation, proofs, and comparisons.
  direct/                     Independent standalone tagged checkers, proof
                              translations, certificates, and regressions.
  strict/                     Six smaller strict modules and exact paired
                              references, proof of acceptance equivalence,
                              inherited fixtures, and reproducible metrics.
  lean/                       Uncompiled Lean extension sources and build notes.
  evidence/                   Reproduction receipt, audits, and source snapshot.
  reference/                  Pinned source excerpts, attributed arithmetic
                              foundations, incoming audit, and upstream license.
  scripts/reproduce.py        Runs both Python verification families.
  CLAIMS.json                 Machine-readable claims and qualifications.
  MANIFEST.json               SHA256 hashes of delivered files.

REPRODUCE
From this directory with Python 3.12 (measurements used 3.12.14):

  python3 scripts/reproduce.py
  python3 direct/one_context_checker.py < direct/certificates/used_hypothesis_induction_one.json
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The checkers import only standard-library modules. Proof generators and
regression scripts are untrusted supporting tools, never checker imports.
Acceptance means normal exit and exactly ACCEPT followed by one newline.
Resource exhaustion is not acceptance. The universal proofs abstract from
finite machine resource limits.

VERIFICATION STATUS
Direct: 32 theorem fixtures, 12 negative fixtures, 240 subprocess checks in
normal and optimized Python, and 300 independent semantic substitution checks;
zero mismatches and zero substitution-budget skips.
Strict: 984 process executions / 492 old-new comparisons, zero differences;
31562 parser-factorization comparisons, zero differences. Each new module's
kernel is identical to its paired comparator outside the validator.
These are finite implementation checks; universal claims have written proofs.

The Lean extensions have been source-audited but NOT COMPILED. Neither Lean nor
Lake was installed. No new formal verification of the full Python checker or
arithmetic bridge is claimed. The existing repository's native/iPRA bridge is
an identified inherited result.

PROVENANCE
Repository: VladimirReshetnikov/ProveIt
Commit: a4e5e96c456303cf231eab2aeeb3291d8889833f
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All six incoming archives were authenticated against their Git blob hashes.
The comparison includes them, not just the older README frontier.
Inherited files retain the upstream MIT-0 license and attribution.
