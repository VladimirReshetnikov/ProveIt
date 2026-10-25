# A descending-binomial quartic in 233 nonnegative integers

Let `s_0,...,s_181` be all 182 literal residuals in `equation.json`, in
the file's stated order. The single equation is

    P(x_0,...,x_232) = sum_{j=0}^{181} s_j(x_0,...,x_232)^2 = 0,

with every coordinate independently ranging over
`N = {0,1,2,...}`. The domain is part of this specification.
`expanded_polynomial.json` contains every collected integer coefficient.

| Measure | Released endpoint |
|---|---:|
| Independent nonnegative variables | 233 |
| Quadratic residuals | 182 |
| Exact total degree of P | 4 |
| Nonzero collected monomials | 7,313 |
| Coefficient height | 86,543,666 |

Every variable occurs. A sparse term is encoded as
`[coefficient, [coordinate indices]]`; indices start at zero, repeated
indices are repeated factors, and an empty index list denotes a constant.
There are no factorial, binomial, exponentiation or floor primitives in
the final polynomial.

The ordinary theorem, composed with the explicitly retained numerical
C222/ZF/ZFC refutation calibration, is

    ZFC proves: P has no zero in N^233 if and only if Con(ZFC).

The constructive statement in both directions is that a zero exists
exactly when a finite syntactic ZFC refutation exists. This equivalence
does not assume consistency and does not establish it. The construction
uses the direct numerical calculus, without a K215 simulation or Jones
universal-polynomial specialization.

## What changes

The starting comparison is package 129 at ProveIt commit
`1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`, together with its retained
arithmetic ancestry. The new branch keeps the Cantor syntax, six exact
power requests, eleven modular binomial requests, consecutive Pell
ordinates, the semantic anchor and the dominant common denominator.
The new changes are the following.

**Descending factorial certificate.** For integers `t>=3`, `F>=2` and
`F^2-1>=t`, the ordinary arithmetic identity is

    F = floor((F^2-1)^t / binom(F^2-1,t))  iff  F=t!.

The graph uses `F=f_0+2`, the nonnegative polynomial
`F^2-1=(f_0+1)(f_0+3)`, and the natural remainder rows
`V_0=BF+r`, `B=r+s+1`. The first carry-free binomial is recovered before
the identity is used. Its same value B is the product of the descending
reciprocal moduli `d_i=F^2/i-1`; these are pairwise coprime and have no
prime divisor at most t. Their index row is `C+1=F^2+Bq_C`.

**One row at the semantic anchor.** At the existing derived syntax-label
index H, the cap and index-error condition become

    Y_H(A) = H + sum_i (y_i-k_i)^2 + (A-1)Q,  Q in N.

The cap and growth frame bound actual indices before the error residue is
decoded. In completeness, increasing the encoded a-column by N^2
preserves all required CRT congruences and makes H dominate twice every
other requested index. The nine representatives still satisfy the
included aggregate bound of 10N^2. This is a completed combination with
the earlier one-row cap and semantic-anchor ideas, with their attribution
retained.

**Horizon floor 12.** The actual horizon is `t=t_0+12`. The emitted local
majorant is `E=2^23`, and the derived-label majorant is `ell=2^22`.
Exact inequalities at `12!=479001600` justify the same unbounded growth
and carry estimates for every later horizon. The number 12 is a proved
floor for this construction, not a finite search cutoff.

The complete new ordinary argument is in
`../report/natural_section.tex`, included by `../report/report.tex`.
`REVIEW.md` independently examines the unbounded factorial, CRT, cap,
sign and horizon chronology.

## Comparison

All three rows below concern direct quartics over nonnegative integers.

| Construction | Variables | Residuals | Monomials | Height |
|---|---:|---:|---:|---:|
| Package 129, recommended | 234 | 183 | 9,019 | 87,741,134 |
| Package 129, denser companion | 233 | 182 | 50,762 | 88,674,690 |
| This component | 233 | 182 | 7,313 | 86,543,666 |

The improvement is relative to these identified endpoints and metrics.
No global minimum or literature-wide priority is asserted.

## Files and proof boundary

- `equation.json`, `expanded_polynomial.json`, `METRICS.json`: the final
  residual system, complete polynomial and measured endpoint.
- `source/semantic.json`, `source/local_majorant.json`: the generated
  arithmetic graph, exact interface metadata and local growth certificate.
- `source/equation.json`, `source/expanded_polynomial.json`: the affine
  export with 339 natural coordinates and 288 quadratic rows.
- `elimination_certificate.json`, `VERIFICATION.json`: 106 subsequent
  contractions and their exact independent replay.
- `check_affine_export.py`: an independent gate, dependency-closure,
  nonnegative affine-restoration and coefficient checker.
- `check_contraction.py`: independent rational sum-of-squares certificate
  expansion and occurrence-list substitution, importing no producer.
- `build.py`, `verify.py`: the current constructor and verification entry
  points for this endpoint.
- `engine/`, `ENGINE_MAP.json`: the included arithmetic engine and its
  source-path/hash relocation map.
- `REPLAY.json`, `INDEPENDENT_REPLAY.json`: recorded exact finite checks
  with their scopes; `REVIEW.md` supplies the separate ordinary review.
- `review_arithmetic_controls.py`: independent bounded controls, including
  2,197 factorial cases, ten reciprocal products and 2,452 cap tuples.

The affine checker verifies 626 defining gates, 400 nonnegative affine
restorations, the dependency closure, every one of the 288 exported rows,
and all 5,000 collected source coefficients. The contraction checker
then verifies all 106 eliminations and all 7,313 final coefficients.
Two restorations with negative coefficients have exact rational
sum-of-squares certificates of nonnegativity. These finite identities
preserve solvability; they do not supply the unbounded number-theoretic
interpretation of the graph by themselves.

## Reproduce offline

Use Python 3.10 or newer. The current verification and reconstruction
paths use the standard library. From this directory:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --rebuild
python3 -B review_arithmetic_controls.py
```

`verify.py` checks the complete finite algebra, the exact endpoint,
selected architecture interfaces, all 97 engine hashes and a deliberately
corrupted coefficient whose claimed hash has been updated. It runs its
own bounded arithmetic controls; the separate review script has the
larger controls listed above. Explicit exceptions are used, so optimized
Python does not disable the checks. Add `--receipt /path/to/receipt.json`
to save a fresh verification receipt.

`--rebuild` constructs the source and endpoint in a temporary directory
and requires byte-identical reproduction of nine released mathematical
files. It leaves the released files unchanged. To retain an independently
generated output tree instead, choose a new output directory:

```sh
python3 -B build.py --output /path/to/new-output --syntax cantor --support-cap 64 --dominant --semantic-anchor --coordinates consecutive
```

The output contains `raw/`, `natural/` and `SUMMARY.json`. These flags
select the reviewed endpoint. Other constructor options do not inherit
its stated metrics or its complete reviewed composition merely because
they are accepted by the command-line parser.

## Included engine and logical scope

The engine retains the direct compiler, numerical-calculus input,
ordinary predecessor proofs and named Lean interface files. Its directory
ancestry has been shortened for a portable archive. `ENGINE_MAP.json`
records each retained path, its pre-relocation input path and hash, its
released hash, and whether path text was rewritten. Those pre-relocation
inputs are the staged adapted engine, not a claim that every file is
unchanged from the comparison Git commit. The mathematical adaptations
are described in `NOTICE.md` and the current report.

Historical READMEs, proofs, report fragments and runnable scripts inside
`engine/` document their original parent constructions. They may state
old metrics, a rising-factorial ceiling, a different cap or old source
paths. Use this directory's `build.py`, `verify.py`, this README and the
current report for the released descending-factorial endpoint.

The named logical endpoints are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Their inherited
calibration and the ordinary compiler proofs are used explicitly; this
component does not rebuild the full transitive Lean development or emit
a new encoded object-language ZFC proof. Independent reviews here are
separate agent reviews within the research workflow, not external human
refereeing. No program in this component decides consistency or searches
for a contradiction or polynomial solution.
