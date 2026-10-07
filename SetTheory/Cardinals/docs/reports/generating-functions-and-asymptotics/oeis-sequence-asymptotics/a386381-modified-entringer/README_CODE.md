# Reproducibility and verification

## Requirements and trust boundary

Python 3.10 or later and its standard library suffice for the exact verifier,
regeneration, corruption guards, manifest validation, and packaging logic.
Building the PDF additionally requires an installed TeX distribution supplying
pdfLaTeX, kpsewhich, and the manuscript's packages; pdfTeX is needed if a private
format must be initialized. The builder neither downloads nor installs anything
and disables TeX shell escape.

The optional environment is pinned to SymPy 1.14.0 and mpmath 1.3.0, the versions
observed in the reproduction environment. These packages are not imported by
the core or required by the builder. Optional programs run only when separately
requested by the operator.

Exact computations establish the finite integer, rational, polynomial, and
Sturm identities actually tested. They do not establish analytic continuation,
parameter-uniform transfer, trace-class determinant identities, asymptotic
remainders, or historical novelty. Those mathematical statements have
conventional proofs in Report180.tex. No proof assistant is used.

## Run the core

From the package root:

```
python -I -S -B code/verify.py
python -I -S -B -O code/verify.py
python -I -S -B guard_tests.py
python -I -S -B -O guard_tests.py
python -I -S -B test_build.py
python -I -S -B -O test_build.py
```

- -I isolates Python from user environment and user-site settings
- -S disables site-package loading
- -B prevents bytecode cache writes
- -O demonstrates that validation does not depend on removable assert statements

The scripts use explicit validation failures. They read the committed reference
data rather than replacing it. The normal and optimized verifier result objects
must agree.

## Exact coverage

The core implements its algebra with integers and fractions.Fraction. Its
finite checks cover:

1. The original integer triangle, its diagonal for n=0,...,101, the 21 displayed
   OEIS terms for n=0,...,20, and independently generated rational ODE
   coefficients. The relation for n>=2 uses N=n-2; the two initial values are
   checked separately.
2. The marked integer triangle and independent formal-polynomial ODE for
   n=2,...,18. The n=2 base remains one; only subsequent boundary injections
   receive a factor lambda. Setting lambda=1 recovers the ordinary sequence.
3. Symbolic Frobenius recurrences in lambda and rho squared for H and G through
   degree 15, direct formal ODE residual checks, and Wronskian coefficients
   through degree 13. Two independent denominator-inversion algorithms check
   the conversion from falling-factorial to inverse-power corrections for
   scalar and marked coefficients through N^-6; explicit marked audit formulas
   are compared through N^-4. Normalized PGF correction multipliers are checked
   through N^-4.
4. The degree-eight P_10 polynomial, exact squarefreeness, coefficient positivity,
   and a Sturm chain. The sign variations at negative and positive infinity are
   7 and 1, respectively: exactly six roots are real and negative, and the
   remaining two roots are nonreal. Approximate roots are unnecessary here.
5. The four rational midpoint tail bounds and their combined Wronskian bound at
   M=420, checked against the recorded exact rational and 10^-44 target.
   It also checks that the reported short decimal interval rounds the frozen
   full interval outward.
6. Frozen reference/provenance integrity and consistency with the exact
   certificate schema and checked manuscript data.

The degree-420 bound concerns the convergent series used for the amplitude,
not a uniform bound on finite-N asymptotic error. The distinction is essential.
The core does not rerun the producer's multiprecision counts/ratios through
n=802, connection evaluations at three interior points, approximate roots, or
the finite interval arithmetic. A hash of such a reference records which bytes
were checked; it does not verify every numerical statement in those bytes.

## Regenerate without overwriting the reference

```
python -I -S -B code/regenerate.py --output /tmp/new.json --compare data/certificates.json
```

The output file must be new and outside the package, with an existing parent.
Existing files, symlinked parents, and traversal paths are rejected. The command
compares regenerated exact data with data/certificates.json and does not replace
the committed certificate. Use a different new output name for another run.

## The amplitude enclosure

Write rho=pi/2 and C(1)=A_1(rho). The amplitude is c=pi C(1). The report gives
the midpoint Wronskian identity and the analytic bounds behind the certificate.
For degree M=420 the exact absolute errors are:

```
epsilon_A = 200 / 2^(M+1)
epsilon_D = 200(M+1) / 2^M
epsilon_H = (8/3)(3/4)^(M+1)
epsilon_T = (16/3)(M+4)(3/4)^(M+1)
delta = (16 epsilon_A + 200 epsilon_T + epsilon_A epsilon_T
         + 2 epsilon_D + 200 epsilon_H + epsilon_D epsilon_H) / 2
```

Here delta is an error bound for C(1). The optional interval computation encloses
the finite series, exact rational inputs, pi, and multiplication by pi. Its
90-decimal-place interval arithmetic gives the shorter outward enclosure

```
25.5745196289574675215372323127353368945234275278994
  < c <
25.5745196289574675215372323127353368945234275279353
```

This numerical certificate relies on mpmath's interval implementation. The exact
core independently checks the displayed rational tail arithmetic and rounding
of the recorded endpoints, but does not independently implement pi enclosures
or replay the interval operations. The conventional tail proof and the trusted
interval calculation are separate parts of the claim. The more extensive
100-digit diagnostic strings are not certified in full by this enclosure.

## Offline PDF and release build

Choose a new output directory outside the package, whose parent exists:

```
python -I -S -B build.py --output /tmp/report180-build-one
python -I -S -B -O build.py --output /tmp/report180-build-two
cmp /tmp/report180-build-one/Report180.pdf /tmp/report180-build-two/Report180.pdf
cmp /tmp/report180-build-one/Report180.zip /tmp/report180-build-two/Report180.zip
```

The builder requires an explicit source inventory, snapshots it into private
temporary storage, and runs the core verifier and guard suites in normal and
optimized modes. It requires matching result objects. TeX runs in clean
temporary storage, with private caches, fixed metadata, and no shell escape.
Auxiliary files must stabilize; unresolved references/citations, overfull boxes,
missing glyphs, and an invalid PDF signature fail the build.

Fixed file order, timestamps, permissions, and uncompressed ZIP entries make
the release deterministic under the same installed Python/TeX stack. A different
software version may produce different bytes. The release ZIP contains source,
PDF, exact certificates, frozen references, optional programs, generated check
summaries, build information, and SHA256SUMS.json. Logs, caches, temporary files,
and empty directories are excluded.

The builder only creates the requested destination after checks pass. Existing
destinations, including dangling symlinks, are not replaced. It rejects source
descendants, traversal paths, and symlinked parent components, and preserves a
destination created concurrently. These protections are defensive packaging,
not a sandbox against hostile TeX or arbitrary concurrent filesystem changes.

## Extracted-release integrity and guards

In a clean extraction of Report180.zip:

```
python -I -S -B verify_manifest.py
```

The manifest covers every release file except itself and rejects additions,
removals, changes, symlinks, special files, unexpected/empty directories,
malformed paths/hashes, duplicate JSON keys, and nonfinite JSON constants.
The authoring tree has no finalized manifest. An intact extracted release can
be used as a build input. SHA-256 provides byte integrity, not authentication
against someone replacing both content and its manifest.

guard_tests.py deliberately corrupts checked mathematical/reference inputs and
checks rejection, ordinary/-O equivalence, and non-destructive regeneration.
test_build.py exercises accepted and rejected source/build/manifest cases,
including destination safety, deterministic archives, simulated compiler
failures, and disagreement between normal and optimized checks. Its fake
compiler tests complement, rather than replace, the actual TeX build.

## Reference provenance

data/references/ contains the frozen producer, independent-audit, and root-check
JSON results. data/PROVENANCE.json records original basenames, roles, SHA-256
digests, and packaged paths, including the one documented output-path adaptation
to the optional root script. Neither those hashes nor successful replay are a
priority claim. SOURCE_AUDIT.md lists the external mathematical sources and
the limits of the earlier-report review.

## Optical-length diagnostic and large-positive-mark scope

optional/check_length.py evaluates the nonsingular transformed integral

```
L = 2 sqrt(2) integral_0^(pi/2) sqrt(u cot(u)) dtheta
u = (pi/4) cos(theta)^2
```

at 50, 100, and 150 decimal digits, with the endpoint value u cot(u)=1.
Its frozen output is data/references/length_diagnostics.json. The ordinary
approximation L=4.2586174557 is not interval-certified. The standard-library
core checks this script and reference by SHA-256 only; it does not rerun
quadrature or infer a certified accuracy from numerical stability.

The report's separate real lambda-to-positive-infinity theorem is supported by
Liouville transformation, two normalized Bessel endpoint models, a bounded
Volterra perturbation estimate including derivatives, and Wronskian matching.
Its O(lambda^-1/2) constant is not numerically certified. It establishes no joint
large-N/large-lambda theorem, no complex-sector uniformity, no Weyl expansion,
and no first large-mark correction coefficient.
Growing lambda must not be substituted into the fixed-compact-mark expansion.

## Fixed limiting-law tail: analytic evidence boundary

A separate audited consequence of the summable positive Bernoulli product and
real-positive connection asymptotic is the limiting mass formula

```
Pr(J=m) = L^(2m+1) / [sqrt(2) pi C(1) (2m+1)!]
          * (1 + O(m^(-1/2)))
```

Equivalently its leading carrier is
K m^(-3/2)[e L/(2m)]^(2m), with K=L/[4 sqrt(2) pi^(3/2) C(1)].
The upper-tail/mass ratio is 1+L^2/(4m^2)+o(m^-2). The proof uses convex
secants, monotonicity, exponential tilting, and a uniform local estimate for
finite or countable Bernoulli sums. It does not differentiate an uncontrolled
asymptotic remainder and requires no complex-sector connection estimate.

For q_m=Pr(J>=m), the inverse is explicitly n(y)=min{m>=0:q_m<=y}. If
H(x)=2x log(2x/(eL))+(3/2)log x-log K and H(x)=log(1/y), the report proves
existence of A and a sufficiently small onset such that n(y) lies between
ceil(x-A x^(-1/2)/log x) and ceil(x+A x^(-1/2)/log x). The constants and onset
are not supplied as finite-input numerical certificates; exact threshold
rounding may require further evaluation near an integer.

These are conventional analytic results for the single limiting law as m
tends to infinity. No new script, numeric assertion, interval certificate,
or core computation is introduced for them. Existing exact checks retain
exactly their previous finite ranges. They do not certify the new analytic
theorem. No simultaneous finite-array-size/m tail limit, uniform finite-size
rare-tail estimate, all-orders mass/tail expansion, effective onset,
complex-sector theorem, or spectral Weyl expansion is claimed.
