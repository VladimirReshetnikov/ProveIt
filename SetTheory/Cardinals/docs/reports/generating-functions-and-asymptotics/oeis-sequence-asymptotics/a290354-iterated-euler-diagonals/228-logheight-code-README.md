# Report228 finite reproduction

These files are a fresh public adaptation of the finite recurrence in the
Report226 reproduction and the exact finite algebra accompanying the endpoint
and logarithmic-height analysis. No research-directory imports, private data,
network access, or changes to either earlier report are required.

## Requirements and commands

Use CPython 3.11 or later. The distributed results were generated with CPython
3.12.14, mpmath 1.3.0, and SymPy 1.14.0. The recurrence and rational endpoint
coefficient generator use only the Python standard library. SymPy checks finite
symbolic inverse identities; mpmath computes unvalidated decimal diagnostics.
A pinned dependency list is provided in `requirements.txt`.

From the package directory:

```sh
python -m pip install -r code/requirements.txt
python -B code/reproduce.py --check --output-dir ../reproduction_run
```

To repeat the checks with optimization enabled and the smallest supported
CPython integer-to-decimal conversion limit:

```sh
PYTHONINTMAXSTRDIGITS=640 python -B -O code/reproduce.py --check --output-dir ../optimized_limit640
PYTHONINTMAXSTRDIGITS=640 python -B code/reproduce.py --check --output-dir ../normal_limit640
cmp results/reproduction.json ../optimized_limit640/reproduction.json
cmp results/reproduction.json ../normal_limit640/reproduction.json
cmp results/crossover_table.tex ../optimized_limit640/crossover_table.tex
```

Alternatively, use `python -B -X int_max_str_digits=640` in place of the environment
variable. The program never calls `sys.set_int_max_str_digits`. Its chunked
base-10 serializer supports arbitrarily long Python integers without changing
the global limit. Explicit checks include positive and negative 3001-digit
integers, a large rational, and exact-string JSON round trips. Every validation
and mathematical check uses an explicit exception, so it remains active under
`python -O`. Numerical work uses a private mpmath context and local Decimal
contexts; it does not change a caller's global precision.

## Outputs

Each run writes only these files in the chosen output directory:

- `reproduction.json`: all nine exact decimal integer counts, exact rational
  endpoint coefficients through rho_7, finite symbolic inverse identities,
  and numerical diagnostics
- `crossover_table.tex`: an include-ready `tabular` with columns n, lambda, m,
  R(n,m), its limiting value, and the lambda-based second-order approximation
- `checks.json`: test status, optimization flag, active integer digit limit,
  and number of explicit checks; this file intentionally differs between
  runtime configurations

`reproduction.json` and `crossover_table.tex` are deterministic for the listed
runtime/dependency versions. No timestamps or absolute paths are embedded in
these artifacts. The console summary includes the output location and SHA-256
of `reproduction.json`. Regeneration replaces these three known output files.
An explicit output directory is required. It cannot overlap any part of the
distributed package and must have no symlink ancestor; output symlinks and non-regular output targets are refused. Source
files are never selected as output targets.

## Exact recurrence and limits

The normalization is F_0(z)=z and

    F_(m+1)(z) = exp(sum_(j>=1) F_m(z**j)/j) - 1.

For input coefficients a_d of F_m, let b_k=sum_(d|k) d*a_d. Starting from c_0=1,
compute

    k*c_k = sum_(j=1)^k b_j*c_(k-j),

checking every division for exact integrality. The output is c_k for k>=1,
with its constant term reset to zero. Thus A(n,m)=[z^n]F_m for n>=1.
The separately defined conventional array entry A(0,m)=1 is not the constant
term of F_m. A second, finite-product implementation checks the recurrence
independently through degree 12 and height 12, and checks all three degree-20
table counts through height 89; its own degree cap is 20.

The inherited resource caps are **degree <=640 and height <=640**. Both caps
are enforced for direct calls, including lists of target heights; booleans,
negative indices, nonintegers and larger values are rejected. A cap is a
finite computation limit, not a theorem or a promise that every computation
near both caps is cheap. Formal coordinate orders are 0 through 12; endpoint
orders are 2 through 7. No command-line option raises these caps.

The distributed table uses n=20,40,80 and lambda=0.5,1,1.5. Its heights are
29,59,89; 73,147,221; and 175,350,525, respectively. Counts are computed with
exact integer arithmetic **at those displayed integer heights** and encoded as
JSON strings, never rounded numeric literals. The heights are computed as
floor(lambda*n*log n) using 80-digit Decimal arithmetic and cross-checked at
160 digits. Both evaluations agree and the numerical distance to the nearest
integer is recorded. This agreement is a computational check, not a certified
interval proof of the transcendental floor.

## Algebra and numerical scope

The endpoint generator uses rational truncated power series and a finite
multi-index sum after factoring out Gamma(2-t/3)^(-1). It checks rho_2 through
rho_7 against the report's rational values. The coordinate coefficients solve
the finite Abel identity with the zero-constant normalization

    Phi(w)=-2/w+log(w)/3+sum_(j>=1) a_j*w**j.

The symbolic inverse check uses x=1/chi_n, chi_n=log(n)/3-K, tau=-log(r), and
u=tau+C(x*u), beta=x*u. It verifies the defining identity through x^6, the
reciprocal identity through x^6, and the displayed beta and m/n signs and
powers. These are finite algebraic identities, not analytic remainder proofs.

All displayed values involving pi, Euler's constant, zeta, logarithms,
exponentials, normalized ratios, or asymptotic approximations are
**unvalidated high-precision numerical computations**. Working precision is
80 decimal digits and JSON displays 30 significant digits; the LaTeX table
rounds to eight decimal places. These digit counts do not certify accuracy.
No effective asymptotic onset or finite-n remainder bound is supplied.

The table normalization and its second-order approximation are

    R(n,m) = A(n,m)/(2*T**(-n)*m**(n-1)),  T=pi/2,
    R2(n,lambda) = exp(-1/(3*lambda)) *
      (1 + K/(lambda*log n) + (K**2/2+c2)/(lambda*log n)**2),
    K=(1-EulerGamma+log(T/2))/3-B,
    B=1/2-pi/6-pi**2/16-log(2)/6,
    c2=(9-pi**2)/108.

R2 is the explicit second-order **ratio** expansion, not the exponential of a
truncated logarithm. JSON additionally supplies the analogous expansion using
the actual beta=n/m, which retains the small floor effect. It also supplies the
exact rational ell_n=E_(n-1)/(n-1)!, the unvalidated Kaneiwa-normalized ratio
A(n,m)/(ell_n*(m-1)**(n-1)), and its second-order approximation using **K+1**.
The coefficient c2 is unchanged by that indexing shift. Finite-n agreement is
illustrative and is not evidence for an effective error guarantee, discrete
monotonicity, unique threshold height, or exact recovery by rounding.
