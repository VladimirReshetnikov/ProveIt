SHARED WITNESSES AND ROOT COMPUTATION IN iPRA
13 November 2026

STATUS
======
The requested presentation below the full ConciseIPRA complexity frontier has
NOT been obtained. Do not describe this archive as a smallest axiomatization
or as a checker below every existing coordinate.

The new mathematical result is a two-component common-witness construction
recovering arbitrary one-term equality transport from variable-source
substitution and iterator computation at equation-endpoint roots. It uses
21 additional inference nodes, including 12 root conversions, and no induction.
With literal-equation progress and the stated logical rules, the resulting
calculus has exactly the native public consequences. Its whole-domain
bi-interpretation and equiconsistency with iPRA follow through the pinned
native bridge. Multiple-component bundles are auxiliary proof syntax only.

The complete readable reference checker is 2413 tokens / 2753 AST nodes /
7782 normalized bytes; deterministic gzip-9 is 2295 bytes. It is much larger
than the compact envelope 239 / 255 / 460.

There is also an independent implementation refinement of an existing
sorted-input checker: 584 -> 581 normalized bytes, 311 -> 309 tokens, unchanged
362 AST nodes, and gzip-9 375 -> 378 bytes. This lowers one existing byte
coordinate, not the full compact frontier, and keeps the original public
encoding/completeness qualification.

CONTENTS
========
shared_witness_bundles.tex/.pdf  Full report: rules, proofs, comparisons, limits.
bundle/                        Standalone reference checker, certificate producer,
                               four concrete proofs, and focused binding tests.
refinement/                    581-byte checker, 584-byte control, 63 fixtures,
                               portable differential verifier, proof of the edit.
synthesis/                     Separate theorem-synthesis proof-language experiment;
                               correct interface, no size record.
baseline/                      Seven unchanged attaining/contrast sources, exact
                               upstream provenance, and upstream license.
evidence/                      Measurements, verification receipts, independent
                               review, and local prior-expression search receipt.
measure.py                     Remeasures complete modules without importing them.
verify.py                      Reproduces the delivered functional checks.
build.sh                       Builds the PDF with pdflatex.
CLAIMS.json                    Machine-readable statement of claim boundaries.
SHA256SUMS                     Hashes of the delivered files (excluding itself).

REPRODUCTION
============
Python tools require only the standard library. Measurements were taken with
CPython 3.12.14, ast.unparse plus one LF, and gzip level 9 with mtime=0.

  python3 measure.py
  python3 verify.py
  python3 bundle/bundle_checker.py < bundle/root_congruence.json
  python3 bundle/bundle_checker.py < bundle/induction_then_transport.json
  sh build.sh

The explicit proof checks print ACCEPT. A rejected bundle certificate prints
REJECT. The small inherited/refined profiles accept only when they print
ACCEPT; an exception or resource failure is rejection. The synthesis prototype
prints its constructed native theorem on success and raises on rejection.

bundle_examples.transport(..., scope=...) is an untrusted compiler. When used
in a nonempty context, supply its entire ambient numerical scope, including
unused variables, and the context length. The checker independently enforces
freshness and all other rule conditions.

SOURCE SNAPSHOT AND PROOF STATUS
===============================
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: e88ebf229bb61bd870bb229b9c97caaa1e044e6e
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The native/iPRA interpretations and their two round trips are inherited from
the repository. The new transport result and public equivalence are written
mathematics with executable supporting certificates. No new Lean/Rocq proof
or verification of the Python implementations is claimed. The inherited Lean
project was not rebuilt for this report.

Upstream control sources retain their upstream license. The source identities
and incoming-archive member paths are in baseline/SOURCES.json.
