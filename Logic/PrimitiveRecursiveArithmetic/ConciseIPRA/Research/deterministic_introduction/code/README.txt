DETERMINED INTRODUCTION FOR THE GUARDED iPRA CALCULUS
==================================================

checker.py is a complete standalone verifier with no Intro witness field.
control.py is the tightly matched verifier with an arbitrary supplied witness.
Both use raw scalar terms, Eq/D formulas, guarded atomic D matrices, two
computation axioms, clause use, full formula transport, Open and Intro.
No normalizer, dependency package, proof search, or external process is used.

The new rule reads the witness from a literal naming matrix when present;
otherwise it uses the newest parent-scope numerical parameter, or zero in
an empty scope. The naming-pattern test includes a complete outer-scope check.
FORMAT.txt specifies every syntactic form and inference rule.

Run the finite verification and reproduce source measurements:

    python3 verify.py

Check an example directly:

    python3 checker.py < examples/accepted/arbitrary_witness_translated.json
    python3 checker.py < examples/rejected/naive_scope_weakening_changes_witness.json

The first prints ACCEPT with exit status zero; the second prints REJECT with
nonzero status. The checked examples also run with Python's -O flag. Kernel
acceptance checks do not depend on assert statements.

Recorded on CPython 3.12.14:

  checker.py  3688 normalized bytes, 1159 significant tokens, 1339 AST nodes
  control.py  3442 normalized bytes, 1078 significant tokens, 1252 AST nodes

The complete new verifier is larger by 246 bytes, 81 tokens and 87 AST nodes.
The improvement is the mathematical rule interface, not program size.
gzip9 figures and exact source hashes are in verification.json. Measurements
remove the top module docstring, use ast.unparse, append one LF and count the
whole standalone program. The files are readable sources, not minified code.

Verification: 10 accepted new certificates; 11 control certificates including
the original unrestricted compound-witness proof; 18 rejected malformed or
invalid certificates; 78 standalone normal/-O CLI executions; five explicit
binding/substitution regressions; ten exact new-to-control embeddings; one
explicit old arbitrary-witness-to-new pair; and a naive scope-extension failure
with its naming repair. These are finite implementation checks, not a formal
proof of consistency or of the mathematical equivalence theorem.

The mathematical source is ../deterministic_introduction.tex. Its proof
of structural admissibility uses algebraic cut before general weakening and
general cut, avoiding the circularity caused by the newest-parameter choice.
The native guarded-core/iPRA bridge is inherited from ProveIt at commit
11814771b7490dfbea0ed5fcf0f5b23586334764. No new Lean/Rocq build is claimed.

verify.py is an untrusted builder and audit driver. It is not imported by
either standalone checker and is not part of the trusted checker measurement.
There is a complete deterministic-to-control certificate elaborator there;
the converse mathematical transformation is illustrated by an explicit pair,
not claimed as a complete implemented compiler.
