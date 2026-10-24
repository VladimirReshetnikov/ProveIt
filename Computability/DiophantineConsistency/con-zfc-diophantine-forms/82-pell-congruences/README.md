# Pell congruences and smaller Diophantine consistency equations

Prepared for Vladimir Reshetnikov, 23 October 2026.

This contribution supplies explicit fixed-coefficient polynomial equations,
ordinary mathematical proofs of their consistency equivalence, literal
machine-readable definitions, and exact finite verification programs.
The comparison snapshot is ProveIt commit
`cf4a5218a5a4e4358d3f5314151b6b05d4aa384e` (after wave 10).

**Recommended entry point:** `report/report.pdf`, especially Section 6.
The main equation has **18 unrestricted integer variables, exact degree 32,
and six squared residuals**. Two useful alternatives have **20 integers at
degree 20** and **17 integers at degree 88**.

## Mathematical claim and boundary

For each delivered equation, with its stated domain and actual fixed
coefficient tuple, ordinary reasoning formalizable in ZFC establishes

\[
\exists x\;P(x)=0\quad\longleftrightarrow\quad
\text{the specified ZFC calculus has a finite refutation}.
\]

Negating this equivalence gives the requested equivalence with Con(ZFC).
No consistency assumption is made to prove the biconditional, and no
coefficient depends on waiting for a proof search to halt.

The native compiler, K215/refutation calibration, and named Pell rank
theorems are inherited, explicitly cited mathematical dependencies.
The new contribution is not a new end-to-end Lean/Rocq certificate or a
serialized derivation in the repository's object calculus. The verifiers
certify exact finite algebra, fixed coefficients, dimensions and degrees;
they do not decide consistency or replace the unbounded source proofs.
Internal independent audits are not external peer review. Global minimality
and literature-wide novelty are not claimed.

## New integer tradeoffs

All entries below quantify over unrestricted integers. Every JSON file
defines one polynomial as the sum of squares of its residuals. Ordered
polynomial abbreviations are expressions, not additional unknowns.

| Unknowns | Exact degree | Residuals | Primary literal file |
|---:|---:|---:|---|
| 37 | 4 | 24 | `integer/quartic37_direct.json` |
| 31 | 6 | 18 | `integer/sextic31.json` |
| 26 | 8 | 13 | `integer/octic26.json` |
| 24 | 10 | 11 | `transport/degree10_24.json` |
| 23 | 12 | 11 | `integer/degree12_23.json` |
| 22 | 16 | 10 | `transport/degree16_22.json` |
| 20 | 20 | 8 | `transport/degree20_20_rank_register.json` |
| 19 | 28 | 7 | `transport/degree28_19.json` |
| 18 | 32 | 6 | `transport/degree32_18.json` |
| 17 | 88 | 5 | `transport/degree88_17.json` |

Intermediate packets remain in `integer/` to make the derivation locally
inspectable. Their presence does not mean each is a final Pareto target.
The direct and affine versions of the quartic have the same counts; the
direct version has fewer expanded residual terms.

## Other completed results

These use **strictly positive integer variables**, a different domain.

| Construction | Variables | Exact degree | Binary arithmetic operations |
|---|---:|---:|---:|
| Saturated root transport | 11 | 269 | 111 |
| Adaptive saturated merger | 12 | 78 | 102 |
| Full-radical majorant | 9 | 1,158,228 | 726 |

The corresponding pinned source figures are 11/325/113, 12/82/102, and
9/1,379,730/478. The nine-variable result reduces degree while increasing
arithmetic circuit size; it does not improve the separate 443-operation
target. An operation is one live binary addition, subtraction or
multiplication, including squares and scalar multiplications. This is
not a bit-complexity claim.

## New mathematical mechanisms

1. The preliminary Pell rank proof already implies `c | f^2 - 1` before
   either auxiliary quotient is used. Consequently the two congruences
   `V = -c (mod f)` and `V = -R (mod c)` have the lossless one-parameter
   form `V = f*c*T - f^2*R - c`. This removes a quotient without imposing
   a stronger subprogression or assuming the later exact-rank conclusion.
2. The determinant guard and the affine residue orientation admit one
   common canonical witness family. Combining them saves three guard
   variables while retaining the orientation saving.
3. Centered Pell roots, a parity-forced half-centered root, and the
   source-68 shared-positivity lemma give the smaller integer endpoints.
4. Using the native coordinate `C` in place of `alpha` makes the transport
   equation monic in `F`. Its exact elimination saves another coordinate.
   Retaining the native rank `R` as one coordinate gives the 20/20 form.
5. The positive companions combine saturation with a smaller carrier
   modulus and a separate radical bound. The nine-variable companion
   constructs a majorant for the complete Pell radical and proves its
   inequality by an exact positive-coefficient certificate on the whole
   required cone.

## Reproduce the finite verification

Requirements: Python 3.10 or later, standard library only. No network,
SymPy, theorem prover, consistency assumption, or machine search is needed.

From this directory:

```sh
python3 verify.py
```

The top-level verifier works in a temporary copy. It authenticates the
retained sources, reconstructs all coefficient tuples, rebuilds the
integer and positive literals, compares them byte for byte, and runs the
independent algebra/degree checkers. The included `VERIFICATION.json`
records the completed release run. The normal entry point leaves the
delivered files unchanged. It also works under `python3 -O`.

Individual component entry points, which may refresh their own receipts:

```sh
python3 coefficients/verify.py
python3 integer/audit.py
python3 transport/check_transport.py
python3 positive/verify.py
python3 nine_full_radical/verify.py
```

`SHA256SUMS` is a complete file-integrity manifest except for itself.
To check it on a system with the usual utility, run `sha256sum -c SHA256SUMS`.

## Coefficients must not be mixed

The integer forms use the whole source-34 mixed/parity/unrounded tuple,
plus `cone_A=2^1113` and `cone_B=2^666104`. The six actual integers are in
`coefficients/payloads/`; `coefficients/BINDING.json` fixes every byte,
bit length, source-to-release name and mask convention. Their raw total
is 615,883 bytes. In particular `MF` already includes the source shift.

The eleven/twelve-positive companions use the separate compact source-44
tuple under `positive/native/`. The nine-positive companion uses the
original source-31 tuple under `nine_full_radical/upstream/31-sun10/`.
Source 31 and source 34 share a beta but use different transport shifts
and other coefficients. Their payloads are not interchangeable.

## Build the article

The finished PDF is included. To rebuild it, use a standard TeX Live
installation with `latexmk`, `pdflatex`, Latin Modern, AMS packages,
`mathtools`, `geometry`, `microtype`, `xurl`, `hyperref`, and the small
layout packages listed at the start of `report/report.tex`:

```sh
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The two included companion sections live in `positive/positive_reductions.tex`
and `report/nine_section.tex`. Further `.tex` files under inherited source
directories are preserved source documents, not required additional build
targets for the main article.

## Integration and provenance

The package is self-contained for the advertised offline finite checks.
`SOURCE_PROVENANCE.json` and component fetch ledgers bind the retained
source files to pinned upstream paths. Relative links inside unchanged
upstream prose refer to those original repository locations; consult the
provenance ledger for the corresponding pinned GitHub URL.

The report distinguishes fully supplied new arguments from imported
unbounded theorems. `certificates/` contains the independent review notes,
degree certificates and audit receipts. `NOTICE.md`, the component
notices, and retained licenses identify prior work. The archive is ready
to place in a new contribution directory; it does not edit the repository's
existing README or make a commit automatically.
