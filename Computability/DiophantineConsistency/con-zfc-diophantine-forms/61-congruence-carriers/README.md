# Congruence carriers and a divided Pell norm

An explicit research proposal for ProveIt's ZFC-consistency Diophantine collection.

**Main results:** thirteen positive variables in degree **34**, and twelve
positive variables in degree **118**. The archive also gives a sextic in
**37 unrestricted integers** and an octic in **34 unrestricted integers**.

Read [the paper](report/congruence_carriers.pdf), whose complete source is
[congruence_carriers.tex](report/congruence_carriers.tex).

## What improves

The comparison snapshot is
[beb0192cb8dc36f78c369c080f2adfbc1887a486](https://github.com/VladimirReshetnikov/ProveIt/tree/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms).
Package 59's README reconciles its results with package 57's low-degree
positive forms. The historical integer packets are retained and checked.

| Domain | New variables | New exact degree | New binary operations | Inspected previous point |
|---|---:|---:|---:|---|
| Strictly positive integers | 13 | **34** | 93 | Degree 126, 91 operations |
| Strictly positive integers | 12 | **118** | 104 | Degree 242, 94 operations |
| Strictly positive integers, SOS companion | 12 | 172 | 103 | A separate cost/degree tradeoff |
| Unrestricted integers | **37** | 6 | Not claimed | 42 integers in degree 6 |
| Unrestricted integers | **34** | 8 | Not claimed | 36 integers in degree 8 |

The positive degree reductions are 73.016% and 51.240%; the literal
operation counts increase by two and ten. Lower-operation alternatives,
including 13/132/83 and 12/258/89, remain separate tradeoffs.
The octic uses 17 residual equations, compared with 15 for the older octic.
No improvement on every measure is asserted.

These results do not lower the repository's nine-positive-variable or
ten-unrestricted-integer-variable high-degree bounds. They do not establish
a globally simplest equation. Domains, degrees, circuit costs, and fixed
coefficient sizes are explicit.

## The structural ideas

1. A first Pell carrier simultaneously recovers the scale q³ dividing Y,
   a transport quotient, and its required sign. Its positive gap establishes
   C > 0 before the packed-index bound is used.
2. A second carrier uses divisibility by q⁵. Its q⁴ part recovers the
   exact first Pell index; only afterwards does the extra factor of q
   force q to divide X. This removes the old index quotient while preserving
   low-degree independent coordinates X,Y.
3. A divided auxiliary norm removes the strong Pell root and the auxiliary
   gap together, replacing two positive unknowns by one. A canonical
   odd-index congruence guarantees completeness. A modulo-four unit
   argument combines the three remaining residuals without squaring them
   all.
4. The integer reductions choose literal defining equations carefully.
   Eliminating X through D−ac−gamma(4a+3) instead of u²q removes
   two coordinates while keeping every residual cubic.

The paper gives full proofs of these new reductions and the signed
auxiliary-index lemma. It explicitly states the inherited native compiler
and K215/refutation interface used to conclude

    ZFC proves: no solution in the stated domain  <=>  Con(ZFC).

Here Con(ZFC) means the nonexistence of a finite syntactic ZFC refutation.
No coefficient is chosen by assuming consistency.

## Exact equations and fixed coefficients

- [positive/p13_degree34.json](positive/p13_degree34.json):
  13 positive witnesses, four residuals, sum of squares, 93 live gates.
- [positive/p12_product_split2.json](positive/p12_product_split2.json):
  12 positive witnesses, three residuals, unit-product finalizer, 104 gates.
- [positive/p12_sos_split2.json](positive/p12_sos_split2.json):
  the same three residuals with a sum-of-squares finalizer, degree 172,
  103 gates.
- [integer/sextic37.json](integer/sextic37.json) and
  [integer/octic34.json](integer/octic34.json):
  literal residual systems; each equation is the sum of their squares.

Every register in a positive DAG is an abbreviation, not another unknown.
The packet's supplied witness list is authoritative. Every coefficient
port is a fixed numeral.

The main positive equations use the **entire compact 590069-bit tuple**.
[positive/ACTIVE_BINDING.json](positive/ACTIVE_BINDING.json) gives direct
paths and hashes for the four compressed fixed integers. Its exact recipe,
literal transition input, compiler proof, and original manifest are in
[coefficients/compact44/](coefficients/compact44/). The four raw integers
occupy 295,388 bytes, delivered in 9,445 gzip bytes.

The integer equations use the **different whole mixed-parity-unrounded-
1064921 tuple** selected by their source quartic. Their direct binding is
[integer/coefficients_source/ACTIVE_BINDING.json](integer/coefficients_source/ACTIVE_BINDING.json).
That dossier includes all four raw and compressed integers, exact original
builders, an independent decoder, complete historical comparison packets,
and 30 authenticated source files.

In both families, **MF is already the shifted MF_source**.
Do not shift it again or mix ports between coefficient families.

## Reproduce the finite verification

From this directory, with ordinary Python 3:

    python3 verify_all.py

The verification uses only the Python standard library and no network. It:

- authenticates retained primary sources against Git blob and SHA-256
  identities;
- checks all compact coefficient bytes, bounds, congruences, and active
  polynomial bindings, then rebuilds the integers in a temporary directory;
- regenerates byte-identical main DAGs and checks the SOS companion;
- checks exact residual identities, cancellation-resolved degrees,
  leading coefficients, input/gate liveness, and operation counts;
- verifies all triangular integer eliminations by exact sparse expansion;
- authenticates the integer coefficient dossier and historical comparison
  packets, and runs its independent actual-coefficient decoder;
- runs the new algebra and dossier checkers both normally and under
  Python optimization, so their checks are not silently disabled.

The retained historical coefficient builders/decoder deliberately require
an ordinary, non-optimized Python invocation. The top-level script handles
that distinction. Python/zlib versions can change generated gzip headers;
the compact rebuild check authenticates the mathematical integer bytes
independently of the compression header. The shipped compressed payloads
themselves match their original recorded hashes.

The completed run is recorded in [VERIFICATION.json](VERIFICATION.json).
Individual receipts are next to their corresponding scripts.
These finite checks verify algebra and finite data. They do not run the
machine, search for a contradiction, prove consistency, or replace the
unbounded compiler/calibration theorem.

To rebuild the PDF:

    make pdf

This uses latexmk and a conventional LaTeX installation with the packages
listed in the preamble. The delivered PDF has been compiled and visually
inspected. The make target "verify" runs the finite checks.

## Files and review order

1. Read the paper's formulas, source interface, and soundness/completeness
   proofs.
2. Read [positive/AUDIT12.md](positive/AUDIT12.md),
   [positive/REVIEW_P13.md](positive/REVIEW_P13.md), and
   [positive/SIGNED_INDEX_LEMMA.md](positive/SIGNED_INDEX_LEMMA.md) for
   independent checks of the delicate steps.
3. Inspect the literal DAGs and exact checkers. Their leading coefficient
   certificates remain nonzero on the authentic fixed coefficient slice.
4. Inspect [integer/REDUCTIONS_PROOF.md](integer/REDUCTIONS_PROOF.md),
   [the source transport clarification](integer/SOURCE_TRANSPORT_CLARIFICATION.md),
   and the matching coefficient dossier.
5. Inspect [provenance/SOURCE_BLOBS.json](provenance/SOURCE_BLOBS.json),
   the retained source proofs, and the original attribution notices.

The positive directory also preserves the 14-variable degree-34
intermediate derivation in PROOF14.md and intermediate14/. It explains
the ordered scale carrier; it is distinct from the principal claims.

MANIFEST.json and SHA256SUMS identify the delivered files. Rebuilding a
PDF or rewriting a verification receipt may change that delivery snapshot;
source-identity and coefficient manifests remain the authoritative bindings.

## Proof status and license

This is an ordinary mathematical construction with exact finite algebra
certificates, using named inherited compiler and calibration theorems.
It is **not** a new end-to-end Lean/Rocq proof or an exported formal ZFC
derivation. It makes no assertion that ZFC is consistent and no claim of
global optimality or two-sided independence from consistency alone.

The package follows the repository's MIT No Attribution license. Original
licenses and notices are preserved in licenses/ and the integer dossier;
see [NOTICE.md](NOTICE.md). Retained upstream bytes are distinguished from
new material by their source manifests.
