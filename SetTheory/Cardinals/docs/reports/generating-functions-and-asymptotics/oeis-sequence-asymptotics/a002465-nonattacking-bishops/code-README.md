# Report219: reproducibility code

This directory is self-contained. It enumerates **n indistinguishable,
pairwise nonattacking bishops on an n by n board** and reproduces the finite
algebra in the accompanying report. No network service or sibling directory is an input. It never edits the report.

## Requirements and a complete run

Python 3.10 or later; SymPy 1.14.0 and mpmath 1.3.0. The pinned dependencies are
in `requirements.txt`. For example, in a virtual environment:

```
python -m pip install -r requirements.txt
python test_contracts.py
python -O test_contracts.py
python reproduce.py all --out run-normal --with-diagnostics
python -O reproduce.py all --out run-optimized --with-diagnostics
python compare_receipts.py run-normal run-optimized
```

Run these commands **from this directory**, or use the absolute path to the
scripts from any working directory. Each `--out` must name a **new, nonexistent
directory**. No existing output is overwritten. A failed run has no PASS
manifest and may leave `failure.json`; choose a different fresh directory for a
retry. Output files are UTF-8 JSON, with sorted keys and a trailing newline.
They contain no timestamp, elapsed time, path, Python optimization flag, or
random data. Normal and `python -O` runs with the same inputs and dependency
versions have identical semantic receipts (and byte-identical JSON in our
checks). All mathematical and input guards raise explicit exceptions;
`assert` statements are not used.

The default `all` run performs:

- Angular formal generation through order 3, compared with independent affine
  generation through order 3 and the reusable exact formula data
- Direct Stirling versus Santos counts at every n from 0 through 17 and at
  20, 21, 50, 51, 100, 101, 200, 201, 400, 401, 599, 600
- Actual-board rook inclusion-exclusion for n=0,...,12
- Literal increasing-cell-subset enumeration for n=0,...,5, comparing **every
  piece count k=0,...,n**, not just the diagonal sequence
- Direct exact bivariate coefficient extraction for n=0,...,12
- Exact log-series reconstruction, parity selection, and inverse branch
  residual checks through order 3

`--with-diagnostics` additionally computes non-certified high-precision
asymptotic and cosine-interpolated inverse residuals at the checked n>=20.
Without this option the `all` run uses exact arithmetic only.

## CLI and input contract

```
python reproduce.py coefficients --order 3 --out coefficients-run
python reproduce.py counts --max-n 600 --targets 20,21,599,600 --out counts-run
python reproduce.py counts --max-n 600 --all-n --out every-n-run
python reproduce.py inverse --out inverse-run
python reproduce.py diagnostics --out diagnostic-run --precision 100
```

- Commands are `all`, `coefficients`, `counts`, `inverse`, and `diagnostics`
- `--order J`: any nonnegative integer; the angular engine implements the
  **arbitrary fixed-order** algorithm. Default 3. There is no hardwired order-3
  substitution in the generator. Symbolic expression size, time and memory
  grow rapidly; high orders are an explicit computational request, not a
  promise of practical feasibility or series convergence
- `--oracle-order K`: nonnegative integer, default 3; compare independent affine
  output through min(J,K). `--skip-oracle` omits this comparison and explicitly
  records its absence. The affine engine itself also accepts arbitrary fixed
  order as a Python function
- `--max-n N`: nonnegative integer, at most 10000, default 600. The full
  O(N^2)-entry Stirling table and Santos recurrences are constructed. Large
  integer memory costs grow much faster than the entry count suggests
- `--targets a,b,...`: selected nonnegative n values, each at most N; duplicate
  values are removed. Reference values through min(N,17) and small-board
  verification sizes are always added. The receipt lists exactly what was
  compared
- `--all-n`: compare the direct Stirling convolution and Santos recurrence for
  **every** n=0,...,N. Mutually exclusive with `--targets`; materially slower
  than selected targets. A selected-target run must not be described as an
  all-n numerical check
- Without either target option, use the standard default sizes listed above,
  restricted to N, together with N and N-1 when applicable
- `--board-max B`: actual-board inclusion-exclusion through B, default 12;
  0<=B<=min(N,20). This is exponential in diagonal count
- `--literal-max L`: literal cell enumeration through L, default 5;
  0<=L<=min(B,6). This is exponential; 6 may be slow
- `--coefficient-max C`: rational bivariate extraction through C, default 12;
  0<=C<=min(N,20). This also becomes expensive
- `--precision D`: diagnostic decimal digits, default 80, minimum 40
- Diagnostic commands require at least one checked n>=20. `diagnostics` runs
  count checks and uses the supplied exact c0-c3 formulas. `inverse` uses the
  same formulas without recomputing angular coefficients. `all` uses the
  coefficients it just generated, with inverse/diagnostic checks through
  min(J,3)
- When choosing N<12, also lower `--board-max` and `--coefficient-max`, and
  lower `--literal-max` if necessary. Example:
  `python reproduce.py counts --max-n 4 --board-max 4 --literal-max 4 --coefficient-max 4 --out tiny`

Options relevant to a different command have no effect, except basic CLI
validation. Reusable Python functions accept nonnegative Python integers
(excluding booleans) for sizes/orders and reject malformed inputs. The CLI
places resource limits on the exponential finite checks, not on the formal
coefficient order. No computation uses a probabilistic fit.

## Files and methods

- `coefficients.py`: `angular_amplitudes(J)` and `angular_coefficients(J)` use
  the logarithmic falling-factorial expansion, Touchard polynomials, angular
  saddle phase, x*d/dx amplitude derivatives, and correlated Gaussian moment
  recursion. `affine_coefficients(J)` is the independent oracle: finite
  products and Newton differences for amplitudes, finite powers for log,
  integer partitions for exp, ordinary derivatives, affine contour Jacobian,
  and two independent Gaussian coordinates. The oracle does not import or
  call the angular engine
- `counts.py`: direct binomial-Stirling convolution; Santos/Ferrers row
  recurrences; actual-board diagonal-incidence inclusion-exclusion; literal
  cell-subset search with attack masks; direct rational bivariate coefficient
  extraction. The actual board methods do not assume Ferrers row lengths or
  Stirling identities
- `inverse.py`: exact logarithmic coefficients and formal inverse residuals;
  optional mpmath diagnostics
- `coefficients_c0_c3.json`: full exact rational functions at delta=0 (even)
  and delta=1/2 (odd), including both expanded c3 numerators
- `amplitudes_P0_P3.json`: full exact P0,...,P3 in x and signed d=delta
- `reproduce.py`: CLI, cross-checks, deterministic receipts
- `test_contracts.py`: quick regression and guard tests; use the complete run above for
  full order-3/n=600 coverage. Optional `--out NEW_DIRECTORY` writes a
  deterministic guard-test receipt
- `compare_receipts.py`: checks complete receipt-directory JSON equality

The JSON expressions use SymPy/Python syntax (`**` for exponentiation) and
rational constants, with no decimal coefficients. They are trusted bundled
mathematical data, not a general-purpose parser for untrusted expressions.
`r` is the unique root in (1,2) of r/(1-exp(-r))=2. The data normalize by
b*Gamma(n)*q**n, where q=2/(r*(2-r)) and
b=exp(r)/(2*pi*sqrt(r**2-1)). `d` ranges over -1/2, 0, 1/2 in the two amplitudes.

## Exact inverse checks and limitations

`inverse.json` reconstructs c from the formal logarithmic coefficients and
checks the cosine selector exactly on even and odd integers. It also constructs
separate smooth parity-branch inverse centers

```
x_p = t + h + a_1(p)/t + a_2(p)/t**2 + a_3(p)/t**3
A = log(q*t),  A*h = log(t)/2 - gamma_0
```

using formal log-Gamma asymptotics. Substitution makes the residual coefficients
through t^-3 vanish exactly. In particular a3(odd)-a3(even) is
-r**3/(4*(r+1)*A). This is a **branch inverse** statement: its coefficients are
constant on a chosen parity branch. It is not a claim that differentiating a
cosine interpolation can ignore the oscillation. Optional diagnostics solve
the report's cosine-interpolated equation directly and record its solver
residual and distance from integer thresholds y=B_n.

Finite checks validate implementations and conventions. They do not prove the
analytic all-fixed-order theorem, convergence of an infinite asymptotic series,
an effective remainder constant, or a finite onset. Numerical diagnostics use
ordinary high precision, **not interval arithmetic**. Their residuals are not
certified bounds. No unconditional single-ceiling inverse rule or numerical
threshold guarantee is asserted; the report's two-ceiling enclosure needs its
proved eventual error radius.

The exact counting identities and numerical sequence predate the report. See
the report's bibliography for source attribution and historical scope. This
package makes no priority claim.
