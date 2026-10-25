# Pooling exact power certificates for Diophantine consistency

**A fixed quartic in 225 unrestricted integer variables.**

Prepared for Vladimir Reshetnikov and the ProveIt research program, 25 October 2026.
The source comparison is pinned to repository commit
`a0ef2df5bb1f73c35cd334bbc7f53553350ef06a`.

## The delivered equation

For independent integer coordinates `x0,...,x224`, define

```text
P225(x0,...,x224) = R0^2 + R1^2 + ... + R161^2.
```

The 162 literal quadratic residuals are fully specified in
`equation/equation.json`, printed in `equation/residuals.txt`, and displayed
in Appendix A of `report/report.pdf`. Every coefficient and coordinate index
is explicit. The full collected quartic is also supplied in
`equation/expanded_polynomial.json`.

The accompanying ordinary mathematical proof, composed with the identified
inherited square-shell/C222/ZF/ZFC refutation calibration, establishes in ZFC:

```text
P225 has no integer zero  <=>  Con(ZFC).
```

This is syntactic consistency for the effective ZFC presentation in the
inherited calibration. The construction does not assume consistency or
inconsistency. It encodes a finite numerical proof calculus directly and
does not use K215 or Jones's universal Diophantine polynomial.

| Measure | Incoming Joint Norm parent | This equation |
|---|---:|---:|
| Unrestricted integer variables | 245 | **225** |
| Quadratic residuals | 181 | **162** |
| Exact total degree | 4 | **4** |
| Collected nonzero monomials | 5,304 | **7,867** |
| Maximum absolute polynomial coefficient | 128,446 | **128,446** |
| Maximum absolute residual coefficient | 256 | **256** |

The result saves 20 variables and 19 residuals at unchanged degree and
coefficient height. The increase of 2,563 collected monomials is a measured
tradeoff. It is an improvement within this explicit direct quartic family;
no global minimality or literature-wide priority claim is made.

## Main mathematical contribution

All power requests at one nonzero base `n` can share two quadratic equations
and two new integer coordinates, with no explicit modulus coordinate.
For already certified signed Pell coordinates `Xi,Yi,Zi=A*Yi`, put

```text
K - 2*sum_i Yi*(mi-Xi) - (2*A-n)*L = 0,
sum_i ((mi-Xi+Zi)^2-Yi^2) - n*K + L = 0.
```

These imply divisibility of the sum of squared Pell power errors by
`T=2*A*n-n^2-1`. The original square frame bounds the squares of all actual
bases, indices, and outputs by `W`, with `abs(A)>W^W` and `W>=258`.
After shifting every signed index by `b=floor(sqrt(W-1))`, the resulting
nonnegative error integer is both divisible by `T` and strictly smaller
than `abs(T)`. Every power is therefore exact; negative indices at nonunit
bases are excluded. Unit bases remain valid during the initial bootstrap.

The eleven requests at base `q+1` save ten variables, and the three at base
`q` save two. The three initial individual requests remain available for
the signed bootstrap. Tightening the cofinally chosen local horizon saves
four variables, replacing the beta base by `y=V-1` saves one, and exact
changes of private auxiliary coordinates save three. Integral Pell
difference coordinates reduce the density of the pooled polynomial.

## Read first

- `report/report.pdf`: complete exposition, theorem, proof, comparison,
  dependency boundary, all 162 residuals, and artifact identities.
- `report/report.tex`: editable LaTeX source. Its generated inputs are
  included in the same directory.
- `proofs/POOLED_POWERS.md`: the two-equation aggregate and the unchanged
  square-frame proof.
- `proofs/STRICT_HORIZON_AND_BETA.md`: the semantic changes, including
  cofinal completeness and the corrected zero-factorial bound.
- `proofs/PRIVATE_WIRE_BASIS.md` and `proofs/PELL_DIFFERENCES.md`: exact
  algebraic changes with maps in both directions.
- `proofs/INDEPENDENT_POOL_REVIEW.md`, `proofs/SECOND_POOL_REVIEW.md`, and
  `proofs/INDEPENDENT_HORIZON_REVIEW.md`: independently assigned AI reviews
  of the changed mathematics.
- `provenance/SOURCES.json`: pinned origins and exact dependency paths.

The retained parent source and arithmetic proofs are under
`inherited/joint_norm245/`. The square-shell syntax recoding proof and
constructor-source supplement are under `inherited/shell_recoding_supplement/`.
Original source files and notices are preserved. The full imported Lean
dependency closure has not been recompiled, and this is not a new
end-to-end Lean or Rocq certificate. Python verifies finite artifacts and
identities; it does not prove an unbounded semantic theorem or consistency.

## Reproduce the finite verification

Use Python 3.10 or later, with its standard library. No external Python
packages, network access, or proof assistant are required for these checks.
From this directory:

```bash
python3 -B verify.py --rebuild
python3 -B -O verify.py
python3 -B code/check_report.py
python3 -B -O code/check_pool_lemma.py
python3 -B -O code/check_pool_frame.py --equation equation/equation.json
python3 -B -O code/check_all_frame_atoms.py equation/equation.json
python3 -B -O code/check_input_validation.py
```

The main verifier imports no producer module. It checks the pinned parent,
every transformation boundary, 175 forward and 178 reverse private-wire
residual identities, the exact pooled rows and their retained Pell gates,
the 36 affine squares in the original frame, all fourteen pooled request
memberships, all fourteen inverse Pell coordinate maps, the beta
contraction, and every coefficient of the collected polynomial. All
225 declared coordinates are used. `--rebuild` regenerates all 20 stage
JSON files in a temporary directory and requires byte-for-byte agreement.

The public equation copies and the printed LaTeX appendix are checked
separately. The appendix checker parses its mathematical expressions back
to integer polynomials and compares all 1,177 residual terms.
The separate all-atom audit covers all seventeen retained power requests.
Receipts from the performed checks are in `verification/`.

The immediate parent's independent finite audit and rebuild also passed:

```bash
python3 -B inherited/joint_norm245/code/verify.py --rebuild
```

Its receipt is `verification/PARENT_REPLAY.json`. Earlier inherited receipts
remain in their original locations; they are not represented as new runs
of every historical proof or every imported formal dependency.

## Build and evaluate

Reconstruct the five construction stages:

```bash
python3 -B build.py --output /tmp/conzfc225-rebuilt
```

The default output is the supplied `stages/` directory; use a separate
directory for an audit. The principal stage is `principal225`.

Evaluate the polynomial at one explicitly supplied tuple:

```bash
python3 -B evaluate.py --values tuple.json
python3 -B evaluate.py --values - --residuals < tuple.json
```

The input must be one JSON array of exactly 225 integers. This evaluates a
specified tuple; it is not a consistency decision procedure or a root search.
The input-validation checks reject malformed coefficient lists and
noninteger or incorrectly sized tuples, including under optimized Python.

## Rebuild the report

The `.tex` source uses ordinary LaTeX packages distributed with TeX Live:
`amsmath`, `amssymb`, `amsthm`, `mathtools`, `lmodern`, `geometry`,
`booktabs`, `longtable`, `array`, `microtype`, `xcolor`, `enumitem`,
`fancyhdr`, `hyperref`, and `xurl`.

```bash
python3 -B code/export_equation.py
python3 -B code/check_report.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The final PDF was rendered and visually inspected. PDF bytes may differ
after recompilation because of build timestamps; the equation and stage
JSON files reproduce byte for byte. `SHA256SUMS` records the supplied
release, excluding the checksum file itself.

## Literal file identities

- Parent residual system SHA-256:
  `1a42dd3a148c3084cd95a367869d251ed92e2f9852397215e4909e70b03d278e`
- Principal residual system SHA-256:
  `fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56`

See `INTEGRATION.md` for a proposed repository entry and review order,
`equation/SCHEMA.md` for the exact sparse format, and `NOTICE.md` for
attribution and the division between inherited and new work.
