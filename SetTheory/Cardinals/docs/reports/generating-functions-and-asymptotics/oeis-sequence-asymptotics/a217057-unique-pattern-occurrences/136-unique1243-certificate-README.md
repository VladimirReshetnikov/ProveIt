# Report 136: exact finite reproducibility certificate

This directory is self-contained. Python 3.9+ and its standard library suffice.
It performs no network access and imports no external research files. It is a
finite computational companion to the report, not a replacement for its
all-size combinatorial proofs or uniform analytic arguments.

## Run

From this directory:

```
python3 -I -B verify.py check
python3 -I -B verify.py replay
python3 -I -B -O verify.py replay
python3 -I -B verify.py guard-test
python3 -I -B -O verify.py guard-test
```

Use the documented isolated launch: `-I` excludes the script directory,
current directory, user site packages, and PYTHONPATH from import lookup.
The verifier refuses a non-isolated interpreter immediately after importing
built-in `sys`, before any shadowable standard-library import. Do not run
the other Python files directly as verifier entry points.

All commands must exit zero. `replay` computes every mathematical check and
compares exact, typed data and canonical JSON bytes with `expected.json`.
`check` only checks integrity, fixture types, and output syntax; it does not
recompute the mathematics. `guard-test` exercises deliberate corruptions in
throwaway copies, including an unsealed shadow `argparse.py`: both normal
and optimized non-isolated launches must reject before its marker executes,
and isolated launches must reject the extra inventory without importing it. No validation relies on Python `assert`, so `-O` retains it.

An optional output must be a **new file outside this certificate directory**:

```
python3 -I -B verify.py replay --output /tmp/report136-replay.json
```

The parent directory must exist. Existing destinations, symlinks in path
components, parent traversal, and in-certificate output are refused. Writes
use exclusive creation and do not replace existing files. The default replay
writes nothing. Temporary guard-test copies are removed automatically.

## Exact definitions

For a three-row partition mu=(a,b,c), including trailing zeroes,

f(mu) = (a+b+c)! (a-b+1)(a-c+2)(b-c+1) / ((a+2)!(b+1)!c!).

Let T_p(lambda) sum f(mu) over horizontal p-strips lambda/mu. The strip
condition is lambda_1 >= mu_1 >= lambda_2 >= mu_2 >= lambda_3 >= mu_3 >= 0.
Set F_m(p,q)=sum_lambda T_p(lambda)T_q(lambda), and

H_h(i,j)=F_(h+2)(i+1,j+1)-F_(h+1)(i,j), for i+j<=h,
J_k(s)=sum_(j=0)^s H_(s+k)(k,j).

The report's exact formula is

b_n=sum_(k+s+t=n-4) J_k(s)J_k(t), with b_n=0 for n<4.

The positive finite partial sum certified here is

L_35=(1/972) sum_(k+t<=35) 9^(-t)3^(-k)(5k+24)(k+2)J_k(t)
    =55999844944982350869187286355724963 /
     90113598179756697647360591499090564.

Its 666 summands are positive. This is a **lower bound**, conditional on the
report's positive-series characterization of R. It is not a certified decimal
approximation to full R, has no computed tail error, and does not resolve the
suggestion R=149/160. The single (k,t)=(0,0) term is 4/81.

## What is actually checked

1. **Published coefficients:** every b_n for n=1,...,25 on
   <https://oeis.org/A224179>, accessed 2026-10-02, agrees with the tableau
   convolution. OEIS starts at n=1; the fixture's separate n=0 value is the
   combinatorial zero convention. No external page is needed during replay.

2. **Exhaustive objects:** every permutation for n=0,...,8 is examined.
   Direct four-index pattern testing checks both directions of the eligible
   greedy top-swap map, unique preimages, and low-skeleton preservation.
   Decreasing high fillings check West's bijection. Greedy, board-corner, and
   finite-neighbor mark tests agree. Each transported mark is checked against
   the eleven allowed cells, boundary decreases, shared decreasing spine,
   both standardized halves, explicit deletion/insertion inverses, and unique
   reconstruction from the two halves' forced position/value orders.
   Every (k,s,t) product count and q-refined half count matches F/H/J. The
   half pair maps are injective and cover the complete Cartesian product in
   each class. Direct suffix/minimum-value tests independently reconstruct
   every F_n(p,q) for n<=8.

3. **Independent tableaux:** hook dimensions, removable-corner recursion,
   and the generalized-binomial determinant agree for all three-row shapes
   through size 37. For sizes through 12, horizontal strips are separately
   enumerated as sets of removed cell columns. These cells plus corner
   recursion independently reconstruct the complete F matrices. H is checked
   for nonnegativity and exact zero support outside its triangle through
   index 35. Every diagonal Schur bound through outer size 37 is checked.

4. **23-index algebra:** the primitive B(a,b)=[z^b](1+z)^a is implemented for
   every integer argument, including negative a; B(a,b)=0 for b<0. Pascal's
   identity is tested on [-8,8]^2; the determinant is evaluated on [-3,6]^3;
   and strip indicators are compared with cells on [-1,2]^6. The full
   four-term alpha,beta expansion is evaluated through n=10 after exact
   delta pruning and distributive factorization of its inner E sums. Its
   surviving box triples are generated from coordinate bounds and sizes,
   not from the partition or F routines. It agrees with the shared-spine
   coefficients. This verifies the finite algebra and domain bookkeeping;
   it does **not** literally enumerate the infeasible (n+3)^23 box. The
   fixed index count is 23 and the expanded primitive-product bound is
   4*6^4=5184. This is not a computed recurrence or rational function.
   The optional 40-variable constant-term construction also receives a
   finite integer exponent-ledger check: all 11+11+1 geometric factors,
   both numerator choices, the Q size equalities and interlacing/boundary
   exponents, and z exponent 4+s+t+k are compared on 1,293 index tuples.
   Direct six-monomial Vandermonde extraction checks its dimension factor
   through size 12. This does not expand the giant Laurent series, integrate
   contours, or identify that rational period with a rational diagonal.

5. **Finite analytic diagnostics:** for common outer shapes through size
   12, every inner pair obeys |r-u| <= 3M_r(mu)+3M_u(nu), with the resulting
   tail-union implication. Row/column incidence degrees and exact Schur
   inequalities are tested. Shape-tail thresholds through size 37, and
   mismatch/triangular F entries through size 12, get exact rational
   Gaussian envelopes with c=1/100. They use exp(-x)>=1-x (0<=x<1), so no
   floating point is used: the output records a tail K envelope, squared
   mismatch K envelope, and triangular K envelope **only on these finite
   domains**. These values are not constants for the report's all-size
   bounds. No limiting interchange, endpoint summability theorem, or
   infinite-tail estimate is proved by these diagnostics.

6. **Profile constants, rational algebra only:** the leading coefficient
   a=(27/8)*5=135/8; the rational prefactor of sqrt(6/pi) in
   D is (81/16)*a^2*(3/2)=4428675/2048; and multiplication by
   4/9^4 gives 675/512. These tiny exact checks use the symbolic factors
   stated in the article. They do not compute an improper integral or
   certify a profile, cancellation, or infinite-tail limit. The current
   article separately proves the diffusive profile, endpoint-tail
   equivalent, and square-root cancellation; those analytic arguments
   are outside this finite verifier.

The output deliberately contains no full-amplitude decimal, timing-dependent
field, fitted asymptotic parameter, or claimed numerical certificate for R.

## Files and integrity

- `tableaux.py`: finite tableau, binomial-algebra, and diagnostic computation
- `objects.py`: independent object-level maps and geometry
- `verify.py`: explicit exception-based validation and replay runner
- `bundle.py`: optional integrated report staging/build/pack checks
- `fixtures.json`: closed, exactly typed reference data and fixed cutoffs
- `expected.json`: full deterministic mathematical output
- `manifest.json`: byte counts and SHA-256 of precisely the other seven files
- `README.md`: this documentation

The verifier refuses any missing or extra inventory entry, directory, symlink,
nonregular file, mismatched digest, duplicate JSON key, nonstandard JSON
number, wrong fixture key/value/type, or replay difference. JSON booleans and
floats cannot masquerade as integer fixtures. SHA-256 protects integrity
relative to the supplied manifest, not external authenticity; a malicious
party replacing both code and manifest is outside that guarantee.

## Sources and logical limits

The coefficient reference is the OEIS entry above. The report explains the
all-size exact reduction, positive-series theorem, and its dependencies.
West's underlying avoidance bijection is prior work; this certificate makes
no novelty claim. General binomial-sum closure and rational diagonals are
covered by Bostan, Lairez, and Salvy, *Multiple binomial sums*,
<https://doi.org/10.1016/j.jsc.2016.04.002> (author version
<https://arxiv.org/abs/1510.07487>). The current certificate checks the stated
encoding, not those general theorems. It does not treat two or more 1243
occurrences, prove a next asymptotic correction, or settle any amplitude
closed-form guess.

## Optional integrated report bundle

A report author can stage exactly root `Report136.tex`, `Report136.pdf`, and
`README.md`, plus this nested certificate. Other source-directory content is
not copied. The staged bundle has an additional `bundle-manifest.json` and a
closed recursive inventory. It includes no private research notes. Commands:

```
python3 -I -B verify.py bundle-stage --report-root /path/to/report-source --output /tmp/Report136
python3 -I -B verify.py bundle-check --bundle /tmp/Report136
python3 -I -B verify.py bundle-selftest --bundle /tmp/Report136
python3 -I -B -O verify.py bundle-selftest --bundle /tmp/Report136
python3 -I -B verify.py bundle-build --bundle /tmp/Report136 --output /tmp/report136-clean-build
python3 -I -B verify.py bundle-pack --bundle /tmp/Report136 --output /tmp/Report136.zip
```

All output paths must be new. The staging parent must exist. Integrated
self-tests check corruptions, a fresh extraction and byte-identical ZIP
repacking, and normal/optimized replay from the extracted certificate. ZIP
entries are stored uncompressed with fixed order, timestamp, mode, and prefix
`Report136/`. The archive is a portable deliverable, not an authenticity seal.

`bundle-build` additionally requires `pdftex` and `pdflatex`. It copies only
the report TeX into a fresh external directory, initializes a private LaTeX
format, uses private cache/config directories and the real installed system
TeX trees, disables shell escape, and runs two passes with fixed epoch
1790899200. It rejects overfull boxes, missing characters, unresolved labels
or citations, and a PDF different from the frozen bytes. Its external
`build-result.json` records both hashes. Byte reproducibility is tested with
the installed TeX distribution; it is not promised across TeX versions.
