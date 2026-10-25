# Pooled digit budgets and a semantic Pell cap

An explicit direct C222 construction for Vladimir Reshetnikov's ProveIt
research program. All mathematical dependencies are pinned to ProveIt
commit `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`.

## Equations

| Equation | Domain | Variables | Degree | Quadratic residuals | Collected monomials | Coefficient height |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Principal | Nonnegative integers | 226 | 4 | 175 | 10,314 | 87,839,583 |
| Sparse companion | Nonnegative integers | 227 | 4 | 176 | 7,905 | 87,839,583 |
| Literal domain lift of principal | Unrestricted integers | 678 | 8 | 175 quartic residuals | Not expanded | Determined by supplied substitution |

The principal equation is exactly

    P226(x_0,...,x_225)=sum_(j=0)^174 R_j(x)^2=0.

Every residual and every coefficient is supplied in
`equations/natural226/`. There are no free coefficient ports or
uninterpreted arithmetic primitives. The ordinary mathematical theorem,
with the retained C222/ZF/ZFC calibration, is

    ZFC proves: P226 has no zero in N^226 if and only if Con(ZFC),
    where N={0,1,2,...}.

The same theorem holds for the two companions in their stated domains.
`PROOF.md` contains the complete new unbounded argument and its dependency
order. The construction neither simulates K215 nor instantiates Jones's
universal polynomial. It does not prove consistency or claim global
minimality or a new end-to-end proof-assistant certificate.

The principal equation improves package 129's 233-variable natural
quartic in all its listed metrics: 233/182/50,762/88,674,690 becomes
226/175/10,314/87,839,583. Relative to its sparse234 counterpart, the new
226-variable equation saves eight variables and eight rows with larger expanded
support; the 227-variable companion has fewer variables, rows and monomials than
that sparse 234-variable counterpart, at slightly greater coefficient height.

## Mathematical changes

Eleven separate remainder upper bounds are pooled into four bounds, grouped
by equal denominator. On the actual completeness witnesses the low binomial
digits are at most `q/N^2`; at most five requests share a group. Their sum
therefore fits in the same digit block. This assertion is stronger than
each remainder fitting separately and is proved explicitly.

The semantic Pell anchor already exceeds twice every other requested index
after its existing CRT representative lift. Consequently the cap and its
squared index-error congruence can be replaced by one natural equation

    Y_J = J + sum_i (Y_i-k_i)^2 + (A-1)Q,  Q>=0.

The sum bounds every actual Pell index in soundness; congruence identifies
the indices. Pell doubling proves the required slack is nonnegative in
completeness. The general one-row mechanism is credited to package128;
the semantic anchor is credited to package 129. The contribution is the
pooled-digit theorem, its actual radix budget, their compatible composition
and the materialized smaller equations.

## Reproduce offline

Python 3.10 or later, standard library only. No network or ProveIt checkout
is used. Run from this directory:

    python3 -B verify.py --rebuild
    python3 -B -O verify.py --rebuild
    python3 -B code/render_equations.py --check
    python3 -B reviews/independent_raw_rows.py

`verify.py` checks every retained upstream file against both its Git blob
identity and SHA256, reconstructs the original semantic-to-raw affine pass,
checks 92 inherited local semantic identities, independently derives all new
pooled/fused rows, replays both certified nonnegative projections, and checks
every collected coefficient. Corrupted row coefficients are rejected.
`--rebuild` additionally regenerates all 13 mathematical JSON artifacts in a
fresh temporary directory and requires byte-identical results. It leaves
the delivered files unchanged. A receipt can be written with `--receipt PATH`.

To generate another copy of the mathematical artifacts:

    python3 -B code/build.py --output /absolute/path/to/new-output

The reconstruction begins with the retained, pinned normalized source
graph. It is not a new build of the whole historical arithmetic compiler or
the full transitive Lean library. The source graph's semantic theorem is
retained in the inherited proof sources and logical interfaces.

## File guide

- `PROOF.md`: new ordinary proof, including both witness directions.
- `equations/source/`: changed 332-variable quadratic source, full expansion
  and transformation record.
- `equations/natural226/` and `natural227/`: literal equations, expansions,
  natural-domain projection certificates, readable text, TeX transcriptions
  and variable maps. A term `[c,[i,j]]` means `c*x_i*x_j`; an empty index list
  is a constant. Repeated indices mean repeated factors.
- `equations/integer678.json`: all 226 literal substitutions
  `x_i=a_i^2+b_i^2+c_i(c_i+1)` defining the integer companion.
- `code/`: deterministic constructor and readable transcriptions.
- `evaluate.py`: exact evaluation at a given JSON coordinate array, with
  `--variant natural226`, `natural227` or `integer678`. This is not a
  solvability decision procedure.
- `verification/`: actual normal and optimized replay receipts.
- `reviews/`: a separately tasked research-agent review and independent
  changed-row checker. This is not an external human endorsement.
- `upstream/`: selected unchanged source data, proofs, checker code and
  logical-interface files with their original licenses.
- `UPSTREAM_PINS.json`: exact repository paths and byte identities.

The upstream TeX files are retained historical mathematical source texts.
Their earlier full report layouts are not rebuilt by this component. The
integrating report supplies the new standalone LaTeX/PDF presentation.

New code and exposition were prepared with AI assistance. Original upstream
material keeps its source identities and notices. No repository write or
publication was performed in preparing this component.
