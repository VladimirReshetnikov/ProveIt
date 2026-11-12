CHECKER REFINEMENTS AND BENCHMARK AUDIT
======================================

The current repository plus all three incoming archives has the observed
coordinate envelope 253 significant tokens / 275 AST nodes / 506 normalized
bytes. These minima are attained by different programs, and are not a
mathematical lower bound.

This directory provides two implementation refinements of the inherited
guarded iPRA presentation:

                                 Tokens   AST nodes   Normalized bytes
Frozen incoming token control       253         280                599
New token profile                   251         283                605
Frozen repository byte control      267         303                506
Eager parity companion              270         303                503
New compact byte profile            269         301                502
Strict byte-profile companion       421         471                869

The token and byte improvements are separate programs. They do not improve
the incumbent 275-node coordinate, and no single program reaches the new
combined envelope 251 / 275 / 502. No mathematical axiom is deleted.

The compact programs assume a canonical closed guarded Eq/D public goal.
The strict companion includes validation of that grammar and every input
leaf, including unused prefixes. All programs read a JSON certificate on
standard input and print exactly ACCEPT followed by a newline on success;
exceptions reject. Both ordinary Python and python -O are supported.

ARGUMENT.txt contains the universal equivalence and completeness arguments.
PROVENANCE.json identifies the comparison sources. The original permissive
license is preserved in reference/LICENSE-upstream.txt.

To reproduce the measurements and finite checks:

    python3 reproduce.py

The final receipt used CPython 3.12.14 and reports 512 checker executions
with no unexpected outcomes. Global-scope token fixtures are intentionally
kept separate from local-scope byte fixtures; do not mix them.

The incoming audit measured all 1,416 Python files in the three delivered
archives, including the 1,380 frozen source blobs in the orbit archive.
Every file below 506 normalized bytes was a classified utility. The
Research Git tree is unchanged between the older audit's commit and the
current pinned repository commit. The corresponding detailed JSON receipts
are under evidence/.

Finite tests are implementation evidence, not proofs of universal soundness.
The scalar arithmetic bridge and its whole-domain bi-interpretation with
iPRA are inherited unchanged. No new Lean or Rocq verification is claimed.
