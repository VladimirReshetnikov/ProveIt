# Guarded resultants and early projection for Diophantine consistency

Research prepared for Vladimir Reshetnikov, 26 October 2026 (UTC).

This release supplies explicit ordinary polynomial equations, complete fixed
coefficients, constructive maps, ordinary proofs and reproducible finite checks.
For each stated domain, the proof establishes in ZFC that absence of solutions
is equivalent to syntactic Con(ZFC), at the explicitly retained calibration.
Neither consistency nor existence of a zero is asserted.

## Main results

- Thirteen unrestricted integers: degree 118 at 114 integer-leaf operations,
  or degree 120 at 112. Both improve the matched 13/152/119 and 13/156/117 points.
- Ten positive integers: 97 operations at degree 202, 111 at 198, or 119 at 190.
  These trade increased operation count for lower degree against 90/206.
  Early projection excludes the third main Pell index before sign recovery,
  permitting the squared transport used by the 190-degree form.
- Natural quartic: 201 variables, 153 residuals, 6,002 terms, height 1,860,103.
  Lower-variable companions have 165 or 164 variables at degree 6, and 139 or 138
  variables at degree 8. The 165-variable sextic improves the listed metrics
  of the preceding 200-variable octic; none of these companions is a quartic.
- Integer quartic: 209 variables, 149 residuals, 5,486 terms, height 2^44.
  Against the incoming 210-variable equation it saves one variable and row,
  but adds 204 terms and has 16 times the height. This is a tradeoff.
- A separately verified 212-variable scaled-pair packet is retained under
  integer212_control/. It is numerically superseded by the incoming 210 and
  is not a current-frontier claim.

Operations mean live binary addition, subtraction and multiplication over
integer leaves, including squares and fixed scalar products. Reuse is free.
Variables are all independently quantified coordinates, not selected registers.
All low-degree direct equations supply every collected coefficient. No global
minimum, bit-complexity bound or literature-wide priority is claimed.

## Read first

- report/main.pdf and report/main.tex: integrated article and editable sources.
- roots/PROOF.md: guarded quadratic trace elimination, including all exceptional
  denominator and signed-root cases before extraction.
- positive/PROOF.md: the early projector, signed centers and positive completeness.
- natural/PROOF.md: natural gate charts, exact contractions and domain restoration.
- integer/PROOF.md: the accepted even-affine horizon209 construction.
- reviews/: independent AI-assisted mathematical and finite-check evidence.

The base snapshot is ecb9a4b4dda617512952525d50f17343700aac52. The sole bounded
late comparison is c8187221a60df5baa0047c254a592a014491b60c. It introduced the 210
construction that superseded the preliminary 212 numerical endpoint. The final 209
result is a separately proved modification of that stronger source, not a blind
deletion of a positivity guard. The rejected odd-horizon proposal left a t=-1,
x=0,q=1 escape; the accepted t=4u+2 excludes both 0 and -1 before sign recovery.

The complete pinned low-padding2963 positive tuple uses 69,685 raw bytes, 942 tiles
and 978 physical positions, including its zero-weight marker 1005. It has its own
native proof and Pclp certificate, distinct from the historical 943-tile/radix67
calibration. Later block-mask printing preserves the exact tuple; this package
retains its authenticated recipe rather than mixing ports or certificates.

## Reproduce the release

Use Python 3.10 or later with its standard library:

    python3 -B verify.py

The top-level verifier authenticates the inventory, copies the release into
fresh temporary directories and runs every listed stage normally and under
optimized Python. It verifies exact coefficients, circuit identities, complete
leading forms, source pins, fixed numerals, printed residuals and actual
corruption rejection. It includes full retained-parent replays and an
independent handwritten reconstruction of both printed positive tuples.
Every sealed file must remain byte-identical. The actual final ZIP is freshly
extracted and replayed separately before delivery.

    python3 -B verify.py --mode normal
    python3 -B verify.py --mode optimized

FINAL_REPLAY.json records the performed sealed-folder replay. The delivery
receipt records the final ZIP hash; that hash cannot be included in its own ZIP.
No Diophantine zero search, blank-machine execution or consistency decision is run.

Some optional reviewer scripts in roots/review/ use SymPy as a second symbolic
oracle; they are not invoked by the standard-library release replay. Historical
review receipts retain their original source-layout paths. The two scripts run
from reviews/ by the top-level plan are portable and standard-library-only.

The pinned maintained-page builder has a documented gzip OS-header portability
difference in this runtime. This is not falsely recorded as a successful original
compressed-byte rebuild. Stored payload hashes, every raw integer, the native
finite controller and all new graphs are verified separately.

## Article and interpretation

The selected direct equations have equation.json, expanded_polynomial.json and
readable residuals. Circuit graphs contain every charged gate and all actual
coefficient payloads with finite recipes. Proof-only divisions, factorials,
variable exponents, Pell sequences and inequalities are not hidden operations
or further quantified witnesses in a final polynomial.

With a normal TeX Live installation:

    sh build_report.sh

Recompilation may change PDF metadata and bytes. The delivered PDF was rendered
and every page visually inspected; both full printed seeds and coefficient
recipes were independently checked. Mathematical data are controlled separately
from future PDF builds.

Ordinary unbounded proofs and finite artifact checks play distinct roles.
Inherited C222/ZF/ZFC or native/compiler/refutation calibration remains explicit;
its entire transitive proof-assistant development was not newly compiled here.
Reviews are separate checks within an AI-assisted workflow, not outside human
endorsements. No original repository or earlier sealed delivery was modified.
