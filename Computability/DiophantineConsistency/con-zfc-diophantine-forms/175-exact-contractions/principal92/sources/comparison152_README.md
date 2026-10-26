# Lucas corrections and elimination of arithmetic witnesses

Prepared for Vladimir Reshetnikov and the ProveIt repository, 25 October
2026. Comparison snapshot:
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`.

**Primary compact proposal:** one polynomial in **ten strictly positive
integer variables**, with **exact degree 304** and an evaluator using **87
binary arithmetic operations**.

**Separate direct-calculus proposal:** a quartic in **248 unrestricted
integers**, and explicit projections including **153 integers at degree 8**,
**125 at degree 16**, and **102 at degree 256**. This route directly encodes
the C222 proof calculus and does not use a K215 simulation, Jones's universal
equation, or Sun's reduction.

For every equation, the ordinary mathematical proof, composed with the
identified inherited refutation calibration, establishes in ZFC:

> There is no solution in the stated domain if and only if Con(ZFC).

This proves an equivalence, without assuming or proving consistency. It
does not establish a global minimum or provide a new end-to-end Lean/Rocq
proof object. All claims of improvement are relative to the inspected,
pinned sources. AI assistance and the precise scope of separate reviews are
disclosed in `NOTICE.md`.

## Read first

- `report/report.pdf`: the complete paper and printed polynomial specifications.
- `report/report.tex`: the main LaTeX document, with included section files.
- `report/report_standalone.tex`: the same document with all section inputs
  expanded into one TeX file.
- `compact/PROOF.md`: the new unbounded Lucas-correction proof.
- `direct_quartics/PROOF.md`: the new unbounded front-sign recovery proof.
- `higher_degree/section.tex`: the exact polynomial-elimination theorem and
  its integer zero-set bijection.

The paper prints the entire compact formula, the complete finite recipe for
all four fixed coefficients, all 182 residuals of the principal direct
quartic, and all 913 row-to-coordinate pivot pairs defining the eight
higher-degree polynomials. There is no unspecified universal-polynomial
parameter or hidden variable in these specifications.

## 1. The new compact idea

The inherited native/Pell construction has a rank bound `R < q^4`. A prior
attempt to lower the scale to `Y = q s` yielded only a `q^3` congruence for
the index error. This package subtracts the next Lucas term:

```text
e6 = 6(k - R - 1) - v(R + 1)(R - 1)(R + 3),   v = X Y^2.
```

The exact cubic-difference identity strengthens the bounded index
congruence to `q^4`, including at primes 2 and 3. Once the index is fixed,
the full `q^6` divisibility follows, and the carrier recovers `q^2 | s`.
The proof separately handles the negative-rank branches before invoking
source positivity; omitting those branches would leave a soundness gap.

The final equation is

```text
Q (Z^2 - RG V^2) + (RG - Z^2) = 0,
```

with all polynomial abbreviations given in the paper and literally
implemented in `compact/equation_bV.json`. The ten inputs are exactly
`J,F,alpha,i,T,w,s,n,eta,zeta > 0`.

The cost breakdown is 53 multiplications, 18 additions and 16 subtractions,
charging squares and fixed scalar multiplications. Its degree-304 highest
homogeneous form is proved nonzero at the actual fixed coefficient tuple.
The complete tuple is inherited; its largest stored coefficient has 592,884
bits. Circuit operation counts are not bit-complexity claims.

The new 87/304 point improves the inspected 87/323 and 88/318 compact points.
Other tradeoffs, including 75/626, 84/328 and 89/288, remain relevant. The
86/410 circuit is included only as a diagnostic control, not as an improved
frontier point.

## 2. The direct arithmetic improvement

Replace two separate certificates that factorial-front coordinates `r,s`
are nonnegative by the single quadratic row

```text
(r + 1)(s + 1) = 1 + a^2 + b^2 + c(c + 1).
```

This row allows an unwanted branch `r,s <= -2`. The new proof authenticates
signed power requests first, proves the required bounds in both branches,
and lets the existing exact factorial binomial digit exclude the unwanted
branch. It does not assume factoriality to recover signs needed to prove
factoriality. The construction composes, and credits, the prior odd-square
radix restriction.

| Profile | Integer unknowns | Degree | Residuals | Collected terms | Exact height |
|---|---:|---:|---:|---:|---:|
| Matched incoming parent | 252 | 4 | 182 | 5,340 | 128,446 |
| Principal | **248** | **4** | **182** | **5,321** | **128,446** |
| Balanced projection | 246 | 4 | 180 | 5,048 | 195,955 |
| Dimension projection | 245 | 4 | 179 | 21,845 | 314,701 |

The principal file is
`direct_quartics/equations/integer248/equation.json`. It defines the sum of
the squares of its 182 quadratic residuals. Every coefficient of each
collected quartic is supplied. Exact source edits, monic restorations and
integral translations accompany each profile.

## 3. Eliminate defined arithmetic coordinates

Each selected source row has the form `epsilon*x_v + f = 0`, where
`epsilon` is +1 or -1 and `x_v` does not occur in `f`. An acyclic selection
therefore defines the removed coordinates as integer polynomials in the
retained ones. Substituting these definitions into the remaining residuals
and summing their squares preserves the integer zero set by an explicit
polynomial bijection.

| Integer unknowns | Exact degree | Remaining residuals | Expanded height bound |
|---:|---:|---:|---:|
| 225 | 6 | 159 | < 2^27 |
| **153** | **8** | **87** | < 2^47 |
| 144 | 12 | 78 | < 2^50 |
| **125** | **16** | **59** | < 2^80 |
| 117 | 32 | 51 | < 2^144 |
| 111 | 64 | 45 | < 2^173 |
| **102** | **256** | **36** | < 2^691 |
| 94 | 65,540 | 28 | < 2^164870 |

The complete 153-variable octic expansion is included: **188,579 nonzero
monomials**, **exact height 750,273,658,864**. Its 87 substituted residuals
contain 3,476 monomials. Every variable in all eight equations is certified
to occur by a nonzero modular derivative witness. The largest literal
constant in their DAGs is 256; the expanded coefficients are larger, as
reported separately.

## Reproduction

Python 3.10 or newer and its standard library suffice for the finite
checks. From the package root:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --rebuild
```

The top-level verifier checks the sealed file hashes, binds the higher-degree
source to the actual principal quartic, checks the printed appendices, and
runs all independent finite component audits. `--rebuild` additionally
reconstructs the emitted equations byte for byte. No zero search or
consistency test is performed.

For the extra independently written higher-degree audit, put the receipt
outside the sealed release:

```sh
python3 -B review/review_higher_degree.py \
  --release higher_degree \
  --frozen-source direct_quartics/equations/integer248/equation.json \
  --output /tmp/conzfc_higher_degree_review.json
```

Rebuild the report with a TeX installation providing pdfLaTeX, Latin Modern,
AMS packages, `booktabs`, `longtable`, `microtype`, `xurl`, and `hyperref`:

```sh
python3 build_report.py
```

The report builder leaves TeX's intermediate files in a temporary directory.
It writes `report/report.pdf` and the single-file TeX edition. Run the sealed
manifest check before an intentional rebuild; differences in a local TeX
engine can change PDF bytes without changing the mathematics.

## Proof and verification boundary

The compact module retains the actual fixed coefficients and the arithmetic
proofs/interfaces used by its new argument; it does not bundle every
transitive native-calibration proof. The direct module retains the unchanged
88-file parent component, including its arithmetic proof closure and named
logical interfaces. Neither is a standalone transitive Lean build.

The direct logical bridges are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The compact route
retains the whole indexed native/refutation calibration. The new ordinary
proofs are composed with those specific inherited theorems. Exact finite
checking authenticates the emitted algebraic artifacts and does not replace
those unbounded arguments.

Normal and optimized finite checks, actual-mutation rejection controls,
byte-exact rebuilds, and separate scoped mathematical reviews are included.
Source hashes and original attribution are preserved. See
`SOURCE_LEDGER.json`, `NOTICE.md`, and the component provenance files.

