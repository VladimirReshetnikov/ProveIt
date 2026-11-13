REMOVING THE WITNESS FROM INTRODUCTION IN iPRA
Prepared for Vladimir Reshetnikov, November 12, 2026

RESULT AND LIMIT

The requested construction below the current overall complexity frontier
HAS NOT BEEN OBTAINED. This package provides a narrower mathematical result:
in the raw Alias/Back calculus, with a witness-independent diagonal
introduction mode, Close can always use the newest outer parameter (zero
in the empty scope). Its numerical witness field disappears. A relative
compiler recovers all arbitrary witnesses through fresh substitutive aliases.

The complete new checker measures 862 significant tokens, 1011 AST nodes,
and 3245 normalized UTF-8 bytes. Its directly matched diagonal control
measures 870 / 1022 / 3274. This saves 8 tokens, 11 nodes, and 29 bytes.
It does not beat the current compact envelope 248 / 270 / 479, which is
attained by different programs. No global minimum is proved.

The written proof gives the same open consequences as the inherited
diagonal calculus and hence a bi-interpretation with full first-order iPRA,
with whole numerical domains, actual equality, and both numerical
composites x=y. The full inherited foundational chapter is included in the
report and attributed. The new theorem is not formalized in Lean or Rocq.

START HERE

ipra_local_introduction.pdf   Compiled report with complete inherited
                              arithmetic/logic appendix and full new checker.
ipra_local_introduction.tex   Self-contained LaTeX source for that report.
code/diagonal_newest.py       Standalone target proof checker.
code/diagonal_control.py      Standalone directly matched arbitrary-witness control.
code/compile_newest.py        Untrusted compiler; all emitted proofs are replayed.
code/FORMAT.txt               Detailed executable syntax and limits.
proofs/witness_removal.tex    New theorem and proof as a section fragment.
proofs/independent_review.txt Independent reading of the mathematical argument.
controls/                    Attributed incumbents for reproducible comparison.
tests/                       Source, translated, and adversarial certificates.
evidence/                    Exact measurements, checks, source inventory.
reference/                   Attributed foundations and 97 upstream Lean sources.
STATUS.json                  Machine-readable positive results and unmet target.
PROVENANCE.json               Pinned sources and selected file hashes.
MANIFEST.sha256               Hashes of the delivered archive's members.

REPRODUCE

Use CPython 3.12.14 to reproduce the exact size convention:

    python3 measure.py
    python3 verify.py
    python3 code/diagonal_newest.py < tests/newest/nonzero_close_witness.json
    python3 build.py

The checker prints ACCEPT on success. Verification recompiles 18 source
certificates, checks their target proofs, rejects 18 attacks, and records
108 standalone normal/optimized process runs. It also checks a non-order-
preserving parameter embedding with a non-contiguous clause map.

The compiler's source is the provided control (Back and Use already select
the newest parameter). The written abstract theorem permits a more general
source; no executable parser for that larger source is claimed. Progress
fixtures consume their hypothesis, but are not claimed to establish the
independence or essentiality of induction.

The new checkers validate public syntax and consumed proof, term, scope,
and premise fields. Antecedent-free Use ignores its dummy premise (normally
null), so this is not a claim to lexically validate every unused JSON subtree.
The compact baselines assume a guarded public goal and use other certificate
protocols; they are not interchangeable with the new examples.

The theorem requires compound Back and a matrix-only introduction mode.
Simply retaining the incoming witness==0 mode and replacing its witness
by a fresh variable is not justified. The ordinary realization explicitly
includes the falsity bridge (0=S0)->bottom.

All Python checking is offline. Build needs pdfLaTeX and the ordinary
packages listed in the source. The report source itself has no local
input-file dependencies. Verification/building refresh derived outputs;
check the original manifest before rebuilding if exact delivered bytes matter.

COMPARISON SNAPSHOT

VladimirReshetnikov/ProveIt
dbe0094df420f93f2d5be366b94a0d0c4318dc5b
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All six pending incoming ZIPs were inspected and verified against their Git
blob identities. The 97 included Lean files match that snapshot. The upstream
Lean project was not rebuilt, and its formalization does not verify either
new Python acceptance module. Inherited material retains the MIT-0 license.
