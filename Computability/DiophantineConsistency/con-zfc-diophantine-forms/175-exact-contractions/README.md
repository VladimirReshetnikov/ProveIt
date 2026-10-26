# Exact integer projections for Diophantine consistency

Research report prepared for Vladimir Reshetnikov, 25 October 2026.

The principal deliverable is **one completely specified ordinary polynomial in
92 unrestricted integer variables, of exact total degree 692**, whose lack of
integer zeros is provably equivalent in ZFC to Con(ZFC), using the identified
inherited C222/ZF/ZFC calibration. Its complete finite definition is printed in
the accompanying report and supplied as an executable binary arithmetic graph.

The report and standalone source are `ConZFC_Exact_Contractions.pdf` and
`ConZFC_Exact_Contractions.tex`. The latter contains every source residual,
coordinate list, and unit definition needed to specify the principal polynomial;
it has no external TeX inputs.

## Main endpoint

| Measure | Value |
|---|---:|
| Unrestricted integer variables, all actually occurring | 92 |
| Residual squares | 29 |
| Exact total degree | 692 |
| Live binary arithmetic gates | 2,428 |
| Live nodes, including literals and inputs | 2,648 |
| Largest absolute literal scalar in this graph | 46,656 |
| Proved bound on the expanded coefficient height | strictly less than 2^1655 |

The expanded monomial count and exact expanded coefficient height of this
principal polynomial were not computed. A literal scalar, a graph size, an
expanded height, and a bound on that height are different measures.

The inspected direct-calculus construction in ProveIt package 152 has 94
unrestricted integer variables, exact degree 65,540, and 28 residual squares.
The new endpoint reduces both its dimension and degree, with one additional
residual square. Its larger literal scalar (46,656 versus 256) is an explicit
cost. The comparison of expanded-height bounds, 2^1655 versus 2^164870, does not
establish an ordering of the two unmeasured exact heights. The general
unit-pivot elimination method is inherited, not claimed as a new invention.

Other repository families have substantially fewer variables with different
degree, coefficient, domain, and ancestry costs. This release makes no global
minimality claim and no claim of exhaustive literature priority.

## What fixes the polynomial

Under `principal92/`:

- `circuit92.json` is the full polynomial graph: integer literals, 92 inputs,
  binary addition, and binary multiplication only.
- `sources/source191.json` contains 128 literal cubic residuals in 191 variables.
- `projection92.json` contains the ordered free-coordinate list, 29 retained
  source rows, and 99 acyclic unit definitions.
- `sources/bridge191.json` and `sources/source220.json` bind that source to the
  preceding exact 220-to-191 integral projection.
- `specification/` contains complete readable and LaTeX definitions.
- `audit_core.py` and `verify.py` independently verify the construction without
  importing its builder or search program.
- `evaluate.py` evaluates a specified tuple and can restore source coordinates.
- `PROOF.md`, `PROVENANCE.json`, and the independent review describe the proofs
  and source dependencies.

The principal equation is the sum of the squares of the 29 retained residuals
after the 99 polynomial substitutions. Names of substituted coordinates are
abbreviations, not additional quantified unknowns. No unknown coefficient,
variable exponent, factorial primitive, or external predicate is left in it.

The restoration satisfies the exact identity

    P220(restore220(x)) = P92(x)

for every integer tuple x. Coordinate projection and restoration induce a
bijection of integer zero sets. All eliminated coefficients are units +1 or -1;
there is no division by a nonunit or unproved sign restriction.

## Lower-degree alternatives

All entries below use unrestricted integer variables. Their literal residual
lists and exact projection certificates are in `equations/`. A fully collected
polynomial is also supplied where its term count and height are listed.

| Profile | Variables | Degree | Residuals | Collected monomials | Exact expanded height |
|---|---:|---:|---:|---:|---:|
| `integer191_degree6` | 191 | 6 | 128 | 13,074 | 3,268,176,223 |
| `integer193_degree6_lowheight` | 193 | 6 | 130 | 25,617 | 16,866 |
| `integer197_degree6` | 197 | 6 | 134 | 13,552 | 640,307 |
| `integer145_degree8` | 145 | 8 | 82 | 23,048 | 604,716,407,814 |
| `integer134_degree12` | 134 | 12 | 71 | 40,248 | 604,717,858,816 |
| `integer119_degree16` | 119 | 16 | 56 | 90,760 | 253,229,015,978,920,082,669,568 |
| `integer115_degree24` | 115 | 24 | 52 | uncollected | unmeasured |

The 193-variable sextic has cubic residual coefficients of absolute value at
most 64. The 191-variable sextic has fewer variables and collected terms, with
larger coefficients. The 115-variable form is fully specified by its residuals;
only the collection of their squared sum is omitted.

The JSON term `[c, [i,j,...]]` means `c*x_i*x_j*...`. Repeated indices are powers;
an empty index list is a constant. All indices are zero-based. The polynomial is
exactly the sum of the residual squares.

## Verify offline

Python 3.10 or later and its standard library suffice. From this extracted
directory:

```sh
python3 -B principal92/verify.py
python3 -B -O principal92/verify.py
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --components
python3 -B -O verify.py --components
python3 -B code/check_report.py
python3 -B check_manifest.py
```

The root verifier checks all seven lower-degree profiles, every substitution,
the literal endpoint, every supplied collected coefficient, and deliberate
corruptions. `--components` additionally runs the principal, compact,
oriented-pooling, and final factored-radix checks. These checkers use explicit
exceptions, so their requirements remain active under optimized Python.

To save a new receipt outside the sealed release:

```sh
python3 -B verify.py --components --receipt /tmp/conzfc-exact-fresh.json
python3 -B principal92/verify.py --receipt /tmp/conzfc-principal-fresh.json
```

The principal degree certificate is an explicit integer ray on which a retained
residual has a nonzero coefficient at degree 346 modulo 1,000,003. Its sum of
squares has exact degree 692 by noncancellation over the integers. A separate
modular derivative certificate proves actual occurrence of all 92 inputs.
Integer coefficient-norm inequalities prove the expanded height bound.

`code/check_report.py` independently parses all 128 printed residuals and all
99 pivot-table entries, checks dependency order, and confirms inclusion in the
standalone TeX source. The delivered PDF was compiled with resolved references,
checked for overflow, and visually inspected.

These are finite algebra checks, not procedures for finding a refutation or
deciding consistency. The unbounded arithmetic and logical proof dependencies
are described below and in Section 4 of the report.

## Evaluate a supplied tuple

`tuple.json` must contain an array of exactly the declared number of integers.

```sh
python3 -B principal92/evaluate.py tuple.json
python3 -B principal92/evaluate.py tuple.json --residuals
python3 -B principal92/evaluate.py tuple.json --restore191
python3 -B principal92/evaluate.py tuple.json --restore220
python3 -B evaluate.py integer191_degree6 tuple191.json --restore
```

The root evaluator supports every name in `PROFILES.json`. Restoration checks
the exact pullback value, not merely whether a sample is zero. To project an
existing 220-coordinate tuple, use:

```sh
python3 -B principal92/evaluate.py old_tuple220.json --project220
```

## Supporting mathematics and honest scope

`compact/` supplies a ten-**positive**-integer construction with 85 arithmetic
operations and exact degree 232. The late incoming archive already contains its
`bV` version, so that graph and its 85/232 measures are not new claims here.
The distinct contribution is the proved replacement of its transport factor
by `b^2`, including soundness, the sign-recovery order, and completeness. It
reduces the numerator degree from 57 to 21 and the degree of `QZ^2` from 194 to
122; the total degree remains 232. Unlike the principal result, this branch
retains the inherited native/K215 coefficient calibration. The exact generic
and radix47 coefficient tuples are included. Radix47 is not asserted to be the
current coefficient-storage record.

`research/oriented_pooling209/` supplies the proved five-signed-base rational
error certificate and its 209-variable degree-24 implementation. The source
already suggested the oriented-weight idea; this work completes its bounds,
zero-base handling, and explicit compilation. It does not improve every
projection profile above.

`research/factored_radix/` supplies a different semantic change,
`(BH)^x = B^x H^x`, with a reduced semantic square frame and a proof allowing
larger bases. It is mathematically completed supporting research, not a claimed
improvement of the 191-variable sextic endpoint. Superseded exploratory frames
and unproved target counts are excluded from this release.

## Logical calibration, provenance, and parent replays

The principal route is the direct C222 proof-calculus route. It uses neither a
K215 simulation nor Jones's universal polynomial. The source chain passes
through the 225-variable pooled-power equation and the exact 220-variable
integral projection. The lower-height 193-variable sextic has its separate
217-variable parent, retained in the separated-radicals archive.

The named inherited logical interfaces include
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Their ordinary proof
uses completeness, model constructions, well-founded parts, and constructible
Choice transport, formalizable in ZFC. It is not represented as a theorem
proved merely by finite arithmetic or by the new Python checkers. No external
standardness or transitivity assumption is added to the main equivalence.

This package is not a newly compiled end-to-end Lean/Rocq proof or a serialized
object-language ZFC derivation. It supplies exact finite algebra, explicit
ordinary mathematical proofs, and identified, retained inherited dependencies.
It proves an equivalence, not Con(ZFC) itself.

Initial comparisons are pinned to
`35fa5f6bc659e83f2b2034126c4bcf8e023fbe1c`; the late comparison snapshot is
`0d75e561a8cefc8c30fc4224605a8984c810ad1c`. `SOURCE_LEDGER.json` and the
component provenance files record exact source and archive hashes. The three
original parent ZIPs are retained under `inherited/`, together with the
calibration review. Their original README files describe full parent replays.
For example, after separately extracting the separated-radicals archive, its
`integer/verify_all.py --parent` checks the retained integer construction and
parent arithmetic. The fresh result of that run is preserved in
`verification/LATE217_PARENT_REPLAY.json`.

Receipts identify which stages were freshly executed; old included receipts are
not relabeled as fresh replays of the entire transitive development. Independent
reviews mean separately implemented checks and distinct review tasks within
AI-assisted research, not external human refereeing.

## Rebuild the report

Install a standard TeX Live distribution with the packages named in the source:

```sh
python3 -B build_report.py
```

This regenerates the readable inputs, checks the printed definition, and runs
`pdflatex -no-shell-escape` three times in a temporary directory before replacing
the PDF. The standalone `.tex` can also be compiled directly. Rebuilding can
change PDF metadata and therefore the sealed manifest hash; mathematical
coefficient identity is checked separately. See `INTEGRATION.md` for additive
repository integration and formalization targets.

The release uses the MIT No Attribution license. Original inherited notices and
licenses are preserved; see `NOTICE.md`.
