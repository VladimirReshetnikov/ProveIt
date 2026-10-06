# Report148 exact computational companion

This is a new Python standard-library implementation of exact identities and finite regression checks for the growing Euler crossover and its inverse. It was written for Report148 from the mathematical statements and component audits, without copying Report147 code. No installation, network access, data download, or third-party package is needed. Tested with Python 3.12.14 on Linux. The code requires Python 3.10 or newer; hardened certificate output creation additionally requires standard POSIX `O_NOFOLLOW`/`O_DIRECTORY` support.

## Files

- `exact_companion.py`: independent coefficient algorithms, small exact polynomial/series algebra, rational inequality witnesses, and certificate generation/verification
- `test_exact_companion.py`: 26 `unittest` tests, with all comparisons effective under normal Python and `python -O`
- `certificate.json`: deterministic, human-readable exact fixtures with a canonical-payload SHA-256
- `README.md`: these instructions and interpretation limits

## Run from an extracted report directory

The working directory for all commands below is the package root containing the `companion` directory. Each command was tested exactly in this form:

```sh
python3 -m unittest discover -s companion -p 'test_*.py' -v
python3 -O -m unittest discover -s companion -p 'test_*.py' -v
python3 companion/exact_companion.py --verify companion/certificate.json
python3 -O companion/exact_companion.py --verify companion/certificate.json
tmp_dir=$(mktemp -d)
python3 companion/exact_companion.py --write-certificate "$tmp_dir/certificate.json"
cmp companion/certificate.json "$tmp_dir/certificate.json"
```

Both test commands should finish with `Ran 26 tests` and `OK`. Both verification commands recompute the certificate, compare its entire contents and digest, and print `Exact certificate verified`. The last command is silent when the regenerated file is byte-for-byte identical. Generation is deterministic; there is no timestamp, random seed, machine-specific path, or floating-point value in the certificate. Output creation is exclusive: an existing output file is never overwritten, and symlinks in any output path component are rejected. The temporary-directory command ensures a fresh destination; use a new path to regenerate again. Final-file, dangling-link, and parent-directory symlink cases are regression-tested.

Alternatively, from inside `companion`, use `python3 -m unittest -v` and `python3 -O -m unittest -v`. The test runner and `require` checks use exceptions, never optimization-sensitive `assert` statements. Deliberate certificate tampering is tested and rejected.

## What is checked

### 1. Frozen Euler rows and semantics

For weights `w_j`, the product is

`product_j (1 - epsilon*x^j)^(-epsilon*w_j)`.

Two independent exact algorithms are compared:

1. The logarithmic divisor recurrence, with `B_d = sum_(j*k=d) epsilon^(k-1)*j*w_j` and `n*A_n = sum_(d=1)^n B_d*A_(n-d)`
2. Direct convolution of the separate generalized-binomial factors, whose coefficient at multiplicity `k` is `product_(i=0)^(k-1)(w_j + epsilon*i)/k!`

The full tests compare degrees 0 through 32, both signs, and frozen integer exponents `t=0,1,2,3,5,8`. The `t=0` cases are additional algebraic controls outside the theorem's positive-`t` statement. Every coefficient for these integer-weight rows is checked to be a nonnegative integer. The JSON stores eight rows through degree 18 with `t=1,2,3,5` and both signs; certificate verification independently recomputes both algorithms for every stored row.

Each row freezes the same weights `w_j=j^t` for every previous coefficient appearing in its recurrence. A deliberately wrong diagonal/rolling-`t` recurrence is included only as a negative fixture and is checked to disagree with `A(6,6)` for both signs. It must not be used as an Euler evaluator. Explicit small known rows also catch sign and exponent-convention errors.

The same two algorithms are compared for six rational-weight surrogate rows through degree 24. A sparse surrogate `(1+x^2)^(3/2)` has coefficient `-1/16` at degree 6. This detects the incorrect assumption that generalized distinct-color factors are nonnegative. The rational surrogates are formal algebra tests; they are **not** alleged to equal `j^t` for one shared noninteger real `t`, and the companion does not claim to evaluate arbitrary real powers exactly.

There are also 24 exact logarithmic-atom normalization checks, for `m=1,8`, `t=3,6`, all residues, and both signs. Here `x0=(m/3^t)^(1/3)` is rational. A third independent convolution expands every relevant logarithmic atom, removes only `(3,1)`, retains its collision atoms, and checks the profile sum with the exact falling-factorial cutoff against the normalized Euler coefficient. The identities `a^3=m^2*(8/9)^t` and `x0^r*L_r/(3^(mt)/m!)=c_r*a^q_r` are checked exactly.

### 2. Residue conditioning and pure-cloud identities

The companion checks:

- `q=(0,2,1)` and `c=(1,3/2,1)`, with `H_(q_r)=c_r`
- The residue equivalence `2K=r (mod 3)` iff `K=q_r (mod 3)`
- Minimum depletion indices `(0,1,0)` and the single-size-5 shifted classes `(2,1,0)` with minimum indices `(3,2,1)`
- `H_k` from its differential recurrence versus the independent factorial profile sum, through `k=60`
- Exact finite pure-cloud numerator polynomials from separate `(N_2,N_4)` profiles versus `H_K*P_ell(m)`, for `m=1,...,20` and all residues
- Exact rational polynomial identities for the first two moments of `X`, the two logarithmic coefficient polynomials, and the retained `E V` and `E V^2/2` coefficients
- The coefficient `-32/81+160/81=128/81`, and the logarithmic correction `128/81-(8/9)^2/2=32/27`
- The low-degree exceptional case `(r,D)=(1,1)` in the small-activity exponent check, on the explicitly finite scanned range

The pure-cloud numerator is finite because the falling factorial vanishes beyond the cutoff. This should not be confused with evaluating the entire infinite normalizer `F_q` or `Psi_r`.

### 3. Formal inverse and log-parameter coefficients

A tiny exact Laurent polynomial ring and truncated series ring perform the algebra without numerical substitution. The inverse uses `x=s0^(1/3)` and a formal symbol `w=s0^p`; its coefficient identities hold as Laurent polynomial identities in these symbols. All three residues are checked.

The series ring retains `1,u,u^2,v` and discards the ideal generated by `u^3,uv,v^2`. Direct substitution of the displayed inverse coefficients into the logarithmic finite model leaves exactly its constant term `-(8/9)*s0^(4/3)`. Expansion of the logarithm of the inverse gives the stated `t`-parameter coefficients, with the common `1/L` factor outside the rational algebra. Affine-in-`delta` exponent arithmetic checks that `p-1/3=(delta+1)/2` and `p-4/3=(delta-1)/2`.

This quotient is an algebraic bookkeeping device. The analytic justification that discarded terms fall within the required remainder belongs to the report. The tests separately check the needed rational exponent margins from `beta>5/8`.

### 4. Global falling-factorial formulas, checked on a finite domain

For every pair `1 <= m <= 48`, `0 <= ell <= 2*m+8`, the tests check exactly:

- `0 <= P_ell(m) <= 1`
- `0 <= 1-P_ell(m) <= ell*(ell-1)/(2*m)`
- The cutoff `P_ell(m)=0` for `ell>m`
- With `x=ell*(ell-1)/(2*m)` and `y=ell*(ell-1)*(2*ell-1)/(12*m^2)`, the global-form inequality

`abs(P_ell(m)-exp(-x)*(1-y)) <= 9*(ell^4/m^3+ell^6/m^4)`.

There are 2,784 checked pairs, including both sides of the cutoff. Certificate generation and verification rerun the depletion and second-order bounds on that same domain. No floating-point `exp` is used: whenever a coarse `[0,1]` envelope is insufficient, rigorous rational bounds on `exp(-x)` come from range reduction, alternating Taylor bounds on `[0,1]`, and repeated squaring. The error is bounded at both endpoints of that interval.

The constant 9 is a convenient explicit choice for the globally stated bound. For `ell<=m/2`, the logarithmic tail satisfies `0<=R<=ell^4/(6*m^3)` and `y^2/2<=ell^6/(72*m^4)`. The elementary estimate `abs(exp(-y-R)-(1-y))<=R+y^2/2` gives this branch. For `ell>m/2` and `ell>=2`, `abs(P-exp(-x)*(1-y))<=2+y<=9*ell^4/m^3`. The cases `ell=0,1` are exact. The tests also probe these rational branch bounds. This explains the global formula being checked; finitely many evaluations alone would not prove its all-integer validity.

### 5. Exact exponent-ordering witnesses

The JSON contains exact rational comparisons and integer cross-products. Using monotonicity of the real logarithm, they establish:

- `25/32 < (8/9)^2`, equivalently `2025<2048`, so `delta>2` and `beta>5/8`
- `(25/32)^5 > (8/9)^11`, equivalently `306455660244140625>288230376151711744`, so `delta<11/5` and `beta<3/4`
- `25/18>9/8`, equivalently `200>162`, so `log(5*sqrt(2)/6)>L/2` and `kappa>1/2`

Additional exact comparisons verify the positive small-activity powers used in the bad-atom bound. No decimal approximations to `delta`, `beta`, or `kappa` are needed for these conclusions.

## Interpretation limits

The algebraic identities and rational inequalities are exact. The listed coefficient rows, finite profile sums, cutoff probes, and rational-weight examples are finite tests. **They do not prove** analytic uniformity in `m,t,s`, the complete infinite bad-atom bound, control of every tail, an explicit eventual onset, exact-ratio monotonicity, uniqueness of exact crossings, a first/global crossing, or an integer-`t` threshold. The formal inverse tests concern the smooth finite model's coefficient algebra. Exact-ratio localization and the opposite `s`/`t` bracket orientations require the report's uniform approximation and continuity argument.

This companion deliberately contains no numerical experiment presented as an analytic certificate, no arbitrary-real-`t` exact evaluator, and no claim that a certificate hash itself validates a theorem. The hash detects changes; independent computations, unit tests, and mathematical proof have distinct roles.
