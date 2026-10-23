# Positive source coordinates: a smaller nine-variable candidate

This contribution refines the latest nine-positive-variable construction
in ProveIt snapshot beb0192cb8dc36f78c369c080f2adfbc1887a486 (23 October 2026).

**Result:** a fixed integer polynomial in **nine positive variables**,
with **exact total degree 1,797,796** and **465 live binary operations**
(159 additions, 22 subtractions, 284 multiplications).
The recommended specialization uses the complete compact native tuple
from package 44. A natural-domain translation and the original-tuple
specialization are also supplied.

**Scope:** this is an incremental arithmetic improvement, not a major
breakthrough, a global simplicity minimum, or a new variable bound.
The new algebra and encoding are proved and checked. The native compiler,
Pell/Jones theorems and semantic ZFC calibration remain inherited.
The current repository explicitly leaves the internal object-language ZFC
equivalence derivation open; this contribution does not close that
obligation or claim a new end-to-end Lean/Rocq certificate.

## Read first

- [Report (PDF)](report/report.pdf)
- [Report source (LaTeX)](report/report.tex)
- [Independent mathematical review](research_alternatives/NINE_CANDIDATE_REVIEW.md)
- [Pinned internal-ZFC status](upstream-status/OBJECT_ZFC.md)

The report defines the equation, gives all 22 source residuals and packing
positions, proves the positive changes, bounds and calibration, restates
the finalizer proof, and separates new results from inherited obligations.

## Comparison

| Form | Positive variables | Exact degree | Operations | Native port bytes |
|---|---:|---:|---:|---:|
| Package 59, free carrier | 9 | 1,910,404 | 473 | 533,099 |
| New source, original tuple | 9 | 1,797,796 | 465 | 533,099 |
| New source, compact tuple | 9 | 1,797,796 | 465 | 295,388 |
| Package 58 degree-24 parent | 15 | 24 | 90 | 295,388 |
| New transport companion | 15 | 24 | 89 | 295,388 |

The degree reduction is 112,608, approximately 5.89446%, with eight
operations saved. The compact tuple was already established in package 44:
its use here is a coherent composition, not a new native coefficient-size
record. Native payload bytes do not measure expanded coefficient size.

Each binary arithmetic operation is charged, including scalar multiplication
and multiplications implementing fixed exponents of polynomial registers.
Fixed integer leaves and register reuse are free. These are arithmetic
circuit sizes, not bit complexity or minimality proofs.

## Main specification

The nine positive unknowns are:

    b, g, h, s, w, C, i, j, n

The equation is:

    F9 = (Theta^2 - Omega^2 (a0 + 64 a1))^2
         - 256 Omega^4 a0 a1 = 0.

All registers are integer polynomial abbreviations defined in the report
and literal division-free JSON DAG:

- [Positive circuit](research_nine/compact_candidate/generated/gap_100_positive.json)
- [Natural circuit](research_nine/compact_candidate/generated/gap_100_natural.json)
- [Exact degree certificate](research_nine/compact_candidate/generated/gap_100_positive_certificate_degree.json)
- [Circuit audit](research_nine/compact_candidate/generated/INDEPENDENT_CIRCUIT_AUDIT.json)
- [Whole coefficient binding](upstream44/native/COEFFICIENT_BINDING.json)

There are no unknown program parameters or variable exponents. The natural
translation replaces all positive inputs by natural inputs plus one. It
has degree 1,797,796 and 472 operations. No nine-unrestricted-integer
claim is made.

## What is new

In the quadratic source let k = eta + zeta. Its old equations force
p = P-k > 0 and t = tau-p > 0. The two rows become:

    p - E*c + eta*E = 0,
    t^2 + 2*p*t - eta*p - zeta*p - 1 = 0.

The inverse P = p+eta+zeta, tau = p+t is a bijection on the complete
positive common zero sets. Supplying S = q^2 in place of L = q^2-1
gives another positive bijection. Together the changes reduce 89 records
to 86 and change an active square into an active pair.

The new packing has maximum coordinate exponent 100, kernel degrees
(1545, 1920, 1847), and convolution height 2047. All 22,451
degree-matched interactions are checked against complete monomial bases.
A separate exact certificate resolves the norm's leading cancellation,
with diagonal leading coefficient:

    2^186 * base_scale^898488 * threshold_scale^400 > 0.

The compact calibration is:

    base_scale = 2^1182967
    threshold_scale = 2^9463725

The separate original-tuple comparison uses powers 2134939 and 17079501.
Do not mix ports or scales between instances.

## Reproduce offline

Python 3.10 or newer and its standard library suffice. From this directory:

    python3 checks/verify_all.py

This rebuilds both coefficient/circuit specializations, runs independent
exact source and circuit audits, and checks the low-degree companion.
It writes checks/REPRODUCTION.json and per-command logs. Critical
independent checks also run with python3 -O, so their success does not
depend on enabled assert statements.

No optimization search, network connection, computer algebra package or
consistency witness is required. Modular evaluations are labeled
diagnostics; polynomial identities are checked exactly.

To build the report with a standard LaTeX installation:

    cd report
    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

## Suggested repository integration

Place this directory in the research collection as a new reviewed
contribution. This archive does not edit the repository or replace a
certified endpoint. A suitable index entry is:

> Positive source gaps and a square-register shift: nine positive
> variables, exact degree 1,797,796, 465 operations; coherent compact44
> tuple, plus a degree-24/89-operation 15-positive-variable companion.
> Ordinary arithmetic proofs and independent finite audits; inherited
> semantic bridge and internal-ZFC obligations remain explicit.

The independent source check starts from the authenticated current
60-operation source. It explicitly handles z_shifted = z_old - 1.
The new record file is not claimed to have the historical package-59
parent's hash.

Imported documents retain historical wording and relative paths.
The active bindings in the report and generated artifacts control this
contribution. See NOTICE.md and the preserved upstream licenses.
