# Removing Redundancy from Diophantine Consistency Equations

Research packet prepared for Vladimir Reshetnikov and ProveIt, 24 October 2026.

**Read report.pdf first.** Its source is report.tex with three companion
LaTeX input files. This packet supplies new explicit equations and ordinary
proofs that their unsolvability is equivalent, provably in ZFC, to syntactic
consistency of ZFC. The arithmetic-to-refutation calibration is inherited from
pinned ProveIt sources. No proof of consistency, global minimum, or new complete
Lean/Rocq/object-language ZFC derivation is asserted.

## Results

All comparisons use ProveIt commit
84e16e43092614bae262ca59651cb9d77e31a255.

| Domain and construction | Variables | Parent degree | New exact degree | Parent → new operations |
|---|---:|---:|---:|---:|
| Strictly positive integers, scaled base | 10 | 368 | **360** | 99 → **96** |
| Strictly positive integers, direct base | 10 | 340 | **332** | 105 → **102** |
| Unrestricted integers, quadratic trace | 13 | 536 | 536 | 135 → **126** |
| Unrestricted integers, rational carrier | 12 | 1200 | 1200 | 145 → **138** |
| Unrestricted integers, integral carrier | 12 | 1456 | 1456 | 141 → **137** |

One operation is a live binary addition, subtraction, or multiplication,
including multiplication by a constant; leaves and reuse are free.
These counts do not measure bit complexity.

| Quartic profile | Integer variables | Quadratic residuals | Collected monomials | Maximum absolute coefficient |
|---|---:|---:|---:|---:|
| Matched parent | 604 | 372 | 9676 | 2445790974704 |
| Principal new quartic | **589** | **371** | **8156** | **2445790974704** |
| Alternative projection | 595 | 377 | 7595 | 6956012 |
| Smaller coefficient alternative | 600 | 382 | 7075 | 964213 |

Every quartic has exact degree four. The principal equation is the sum of
the squares of all 371 supplied residuals. All 589 variables occur.
The savings are measured after complete integral monic projection,
with every deleted coordinate restored by a checked substitution.

## Main mathematical contributions

1. A square-gap calculation separates two Pell radicands without the previous
   weight 9. Elementary rationality and modular arguments handle the other
   pairs and exclude a zero signed radical sum.
2. The auxiliary Pell index must be at least five before transport is
   interpreted. Its growth makes the existing witness b a sufficient
   majorant, removing two more arithmetic gates. Exact degree also drops.
3. On r+s+1=B with an already established B>=1, the pair r>=0, s>=0 is
   equivalent to rs>=0. Six literal applications, followed by a strict
   bound from a repeated-square chain, reduce the quartic from 75 to 68
   sign predicates. Every omitted sign is restored before source semantics.
4. Denominator clearing and common scales give smaller evaluators of the
   identical integer polynomials. A symmetric 29-operation norm identity
   is proved independently; the preferred 28-operation schedule was found
   in, and is credited to, an existing pinned source.

Positive constructions change the polynomial and preserve existence of a
positive zero. Integer norm rewrites preserve the entire polynomial,
including degenerate inputs. Quartic transformations preserve the set of
arithmetic body tuples after fresh sign witnesses are quantified.
These are different claims.

## Exact equations and coefficient conventions

- **Displayed positive equation:** positive/bfs/equation96.json.
  Its companion is positive/bfs/equation102.json.
  The whole BFS compact44 tuple is in positive/coefficients_bfs/.
  Appendix A prints a complete finite recipe; reconstruct_constants.py
  reconstructs all four entire integers and checks their raw-byte hashes.
- **Original coefficient variants:** positive/equation96.json and
  positive/equation102.json, with positive/coefficients/.
  The 98- and 104-operation intermediate constructions are retained.
  Original compact44 K0 differs from BFS K0. Do not mix the tuples,
  identify their polynomial values, or shift MF a second time.
- **Preferred integer evaluators:** integer/compact_trace13.json,
  integer/compact_scalar12_rational.json, and
  integer/compact_scalar12_integral.json. All six coefficients are in
  integer/coefficients/. This is a third coherent tuple, whose beta is
  2^1064921-1. The symmetric alternatives cost one extra operation.
- **Principal integer quartic:** quartic/fused68/support8/equation.json
  lists every quadratic residual; polynomial.json lists every collected
  coefficient; projection.json records integral restoration.
  residuals.txt and polynomial.txt are complete plain-text versions.
- **Alternative quartics:** quartic/fused68/support32_quadratic_first/
  is the 595-variable profile; quartic/fused68/support16_affine2/
  is the 600-variable profile.

JSON monomials are lists of zero-based indices, with repetition for powers:
[7,7,9] means x7^2*x9; [] is the constant monomial. Each
[coefficient, indices] pair is one integer term. Variable order and all
circuit operations are literal in their files.

## Reproduce the exact checks

Requires Python 3.10 or later and only its standard library.
From the extracted directory:

    python3 verify_all.py

No network is needed. The checkers verify all norm coefficients, square-gap
identities, complete circuit graphs and leading forms, whole coefficient
payloads, source-row identities, integral restorations, and every collected
quartic coefficient. Results are in VERIFICATION_SUMMARY.json,
verification/*.txt, and the detailed child receipts.

Unbounded mathematical implications are proved in the report and PROOF
files. Finite checks do not decide existence of zeros. Modular evaluations
are only supplementary transcription controls.

Optional local commands:

    python3 positive/build.py --check
    python3 positive/verify.py --check
    python3 integer/verify_symmetric_norms.py
    python3 quartic/check_pair_guards.py
    python3 quartic/check_fused68.py
    python3 reconstruct_constants.py
    python3 export_quartic_text.py --check

To rebuild the report with a normal TeX Live installation:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

The PDF was compiled and visually inspected. SHA256SUMS.txt authenticates
all package files except itself. Re-running verification can rewrite
receipts; check the supplied manifest before rebuilding if an unchanged
archive check is wanted.

## Provenance and proof boundary

PROVENANCE.json records the snapshot and main claims.
POSITIVE_PROOF_PINS.json authenticates positive source proofs and coherent
BFS transfer documentation. The integer and quartic folders have their own
detailed source ledgers. Immediate upstream proof notes and the applicable
upstream license are retained.

The positive and compact integer equations inherit the ordinary native
compiler/K215/refutation calibration. The direct quartic uses the separate
C222 proof-certificate route. Its named logical endpoint composes
KEndpoint.c222_iff_zf_refutation with
ConstructibleChoice.zf_refutation_iff_zfc_refutation.
See quartic/CALIBRATION_DEPENDENCIES.md for the named arithmetic bridge.

The direct route uses neither K215 simulation nor Jones' universal
Diophantine expression. Immediate Lean endpoint files are copied and
authenticated; their transitive imports were not rebuilt.

Claimed novelty is relative to the inspected frozen repository, with no
worldwide priority claim for generic elementary identities. These are
concrete improvements with reproducible equations; the globally simplest
equation remains unknown.

