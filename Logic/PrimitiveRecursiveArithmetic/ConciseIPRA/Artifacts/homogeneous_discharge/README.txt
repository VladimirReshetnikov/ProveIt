A THREE-RULE HOMOGENEOUS PRESENTATION OF iPRA
November 13, 2026

RESULT AND LIMITATION
The recommended theory is H3-rho, specified in report.pdf / report.tex.
It combines homogeneous formula-body contexts with substitution-stable
diagonal introduction and evaluation at witness discharge. Only the fixed
universal reflexivity body rho(v) = (v=v) allows premise-free Use. All other
base proofs are explicit.

This is a proved smaller MATCHED presentation, not a new global minimum.
It DOES NOT meet the request to beat the repository's entire size frontier.
The final complete readable checker measures 1097 significant tokens,
1223 AST nodes, and 3427 normalized bytes. Its matched four-family control
measures 1138 / 1262 / 3547. The reduction is 41 / 39 / 120.
The inspected compact records include 239 tokens, 256 AST nodes, and 462
bytes, attained by different programs under different input contracts.
They are measured upper bounds on an unknown optimum, not proved lower
bounds. The report separates all of these comparisons.

WHAT IS PROVIDED
report.pdf / report.tex       Complete mathematical report, editable source.
code/h3_seed_checker.py      Preferred standalone trusted checker.
code/h4_checker.py           Original matched four-family control.
code/h3_checker.py           Fusion-only variant.
code/h4_seed_checker.py      Seed-restriction-only variant.
code/translations.py         Untrusted explicit proof-tree translations.
code/verify.py               Translation, rejection, and size checks.
code/*.h3_seed.json          Small accepted certificates for the final checker.
validation/                 Independent scope audit and peer-review record.
reference/                  Pinned upstream foundation and incumbent sources.
evidence/                   Provenance, comparison classes, inspection limits.
MANIFEST.sha256             Hashes of all delivered files except this manifest.

QUICK START
  python3 code/h3_seed_checker.py < code/zero_computation.h3_seed.json
The output is True. False means rejection. Exit status zero alone does not
mean that a proof was accepted. Do not run a checker with -O or -OO: the
checker explicitly refuses those modes because they remove assertions.

REPRODUCE
  python3 reproduce.py
Measurements match the repository protocol on CPython 3.12.14.
The driver verifies file hashes, checks 11 positive groups and 9 negative
groups, checks refusal of optimized execution, and runs 7200 deterministic
generated scope/syntax checks. It also remeasures the inspected incumbent
sources. It does not treat these finite tests as formal verification.

BUILD THE REPORT
  python3 build_pdf.py
Requires pdfLaTeX and the standard AMS, geometry, mathtools, booktabs, array,
xurl, hyperref, microtype, and Latin Modern packages. If the installed TeX
sources have no format cache, the script builds a private one. No download
or network is used.

MATHEMATICAL STATUS
The new equivalence is proved in writing and independently reviewed.
The full iPRA bi-interpretation is inherited through the repository's native
calculus, with whole domains, actual equality, both formula round trips,
and identity numerical composites. There is no new Lean/Rocq formalization
of the combined calculus in this archive.

UPSTREAM SNAPSHOT AND NOVELTY LIMIT
VladimirReshetnikov/ProveIt, commit:
95d3dd192e97a19bd4f8783c764331ec41126264
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The combined construction is not stated in the inspected integrated article.
Its individual ingredients are prior work and are attributed in the report.
Three pending archives could not be inspected: ipra_iteration_barriers_
2026-11-12.zip, ipra_prefix_conditional_2026-11-12.zip, and
ipra_selfseed_injectivity_2026-11-12.zip. No exhaustive priority claim is made.
The inspected upstream materials retain their included ProveIt license.
