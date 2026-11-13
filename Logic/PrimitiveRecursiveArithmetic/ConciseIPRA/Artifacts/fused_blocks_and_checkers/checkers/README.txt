Checked compact presentation refinements
=======================================

The new complete standalone checker modules measure, on CPython 3.12.14:

  code/checker_tokens239.py     239 tokens   261 AST nodes   549 bytes
  code/checker_ast256.py        245 tokens   256 AST nodes   580 bytes

The baseline coordinate envelope at ProveIt commit
1156099ffe30f7497d2c11ab20271f46cffcd115, including incoming ZIP packages,
is 240 tokens / 259 AST nodes / 462 bytes. Each minimum is a coordinate
minimum over different complete modules, not a proved lower bound on all
possible presentations. The two new files improve the first two coordinates.
Neither file is below all three old coordinate minima.

These are implementation refinements of the existing guarded scalar
presentation. They do not delete an arithmetic or logical axiom, and they
are not a mathematical breakthrough. The complete inherited checking
relation is preserved; the same existing iPRA bi-interpretation therefore
applies without changing its domains or translations. The independent
operational proof is in evidence/independent_review.txt.

The compact input contract is unchanged: the first line is a canonical
closed guarded public formula, and all following lines are finite exact-
integer/list certificate trees. A valid proof packet has three fields.
Malformed packets reject, but the compact programs do not add public
grammar or arbitrary-JSON validators. Successful execution prints ACCEPT;
exceptions reject. Resource limits may reject large valid certificates.

The code/checker_readable.py file is a standalone explanatory expansion.
No compact checker imports it, any test, or any other proof logic.

Reproduction
------------

  python3 verify.py

This measures five complete compact modules and runs both new modules,
their matched controls, and the readable expansion on all 30 focused
fixtures with normal and optimized Python. The fixtures include a derivation
that actually uses its induction hypothesis, compound implication
elimination, scope attacks, wrong endpoints, false-goal mutations, and
malformed packet arities. Separate instrumented checks verify that a
future witness is rejected before its neutral-major packet is read.

Rebuild the static census from a separate pinned checkout:

  python3 census.py /path/to/ProveIt/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA census.json

The census expands gzip copies and recursively nested ZIP archives, removes
leading docstrings, and measures normalized source. It never executes any
repository code. Its syntactic acceptance-marker flag is only a search aid;
eligibility and soundness require the manual review recorded separately.

Sources
-------

The matched 240-token and 261-AST return-reservation controls, together with
their canonical fixtures, are from the incoming ipra_procedure_presentation
package. The current 259-AST record is from ipra_direct_packets. Their exact
paths and SHA256 hashes are recorded in evidence/baseline_summary.json.
The original repository license is included as LICENSE-ProveIt.txt.

The new token transformation replaces a Boolean multiplication by a
short-circuit mode expression. Its internal False leaves are related to
the old integer-zero leaves by a recursive erasure map. The AST profile
also uses exact list-pattern binding, relocates a compile-time global
declaration, and performs global initialization in a function default.
The scope bound, order of witness preparation, recursion order, record
consumption, and fresh-name reservation schedule remain unchanged.
