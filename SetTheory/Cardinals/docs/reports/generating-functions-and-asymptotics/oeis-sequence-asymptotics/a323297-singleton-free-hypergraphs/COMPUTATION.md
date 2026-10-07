# Computational supplement to Report240

## Mathematical scope

The article proves asymptotic expansions and probability statements. The code
checks exact finite identities, verifies displayed symbolic coefficients, and
records finite numerical diagnostics. Finite tables do not establish uniform
remainders, a sharp asymptotic constant, or an effective starting point.

The objects are simple labelled 3-uniform hypergraphs with no pair of edges
meeting in exactly one vertex. Isolates are allowed for A323297 and forbidden
for A323296. Hyperedges are unordered triples; repeated edges are not allowed.
Components of a fixed labelled support have the following multiplicities:

- size 1: one isolate, if allowed
- size 2: none
- size 3: one single-edge component
- size 4: six pair-stars, four three-edge tetrahedra, one complete tetrahedron
- size m>=5: binomial(m,2) pair-stars

Let S,T3,T4 count the three exceptional types, K count all components, and E
count edges. For every object, D=E+2K-n=S+T3+2T4. Every directly enumerated
object is checked against this identity; it is not inferred from its total.

The exact EGF is exp(C(z)), with

    C(z)=z-z^2/2-z^3/3+5z^4/24+z^2 exp(z)/2.

For no isolates replace C by C-z. The classification and EGFs are Howroyd's
2019 contributions recorded in the two OEIS entries; they are not new claims
of this supplement. The frozen prefixes have respectively 24 and 25 terms,
from n=0 through 23 and 24:

- https://oeis.org/A323297
- https://oeis.org/A323296

Reproduction uses these copied finite prefixes and never makes a network call.

## Two independent count calculations

The rooted-component recurrence, with c_m the connected counts above, is

    A_0=1,
    A_n=sum_(m=1)^n binomial(n-1,m-1)c_m A_(n-m).

The second method independently expands the exponential of the dominant term.
Let i be 1 or 0 according as isolates are allowed, and t be 1 or 0 according
as tetrahedral exceptional components are allowed. Define

    H_n=sum_(k=0)^floor(n/2) binomial(n,2k)(2k-1)!!(k+i)^(n-2k).

Here (-1)!!=1 and 0^0=1. This is n![z^n] exp(iz+z^2 exp(z)/2), obtained by
expanding in powers of z^2 exp(z)/2. Define the signed coefficients P_n by

    P_0=1,
    P_n=-(n-1)P_(n-2)-2 binomial(n-1,2)P_(n-3)
        +5t binomial(n-1,3)P_(n-4),

where terms with negative indices are absent. These are the EGF coefficients
of exp(-z^2/2-z^3/3+5tz^4/24), and may be negative. The independent answer is

    A_n=sum_(j=0)^n binomial(n,j)P_j H_(n-j).

All arithmetic is integer arithmetic, including cancellation in this sum.
The two algorithms agree through n=640 in all four isolate/tetrahedron
specializations. In addition, A_n=sum_j binomial(n,j)B_j is checked through 640.
Each main route uses a quadratic number of large-integer arithmetic operations;
bit complexity and combination/factorial work are additional. The limit 640
is enforced before work, rather than making a practical unbounded claim.

## Independent literal enumeration

For n<=8, the verifier lists all binomial(n,3) actual possible hyperedges and
recursively selects subsets. A new edge is allowed only when its intersection
with every chosen edge has size other than one. This is enumeration of actual
edge sets, not enumeration of the asserted component types. Union-find on the
chosen edges then computes the components and the full (K,E,S,T3,T4) tuple.

The empty graph and n=0 are included. Every total and no-isolate total matches
the exact sequences; four joint-marker evaluations and all first/second K,D
moments agree with independent assembly calculations. The largest literal
case n=8 has 10,158 admissible edge sets, including 4,823 without isolates.

## Exact marked recurrences and identities

The component recurrence is evaluated with a weight u^K v^E s^S t3^T3 t4^T4
for every component type, with integer markers from 0 to 3 and n<=32. Zero
markers delete the corresponding exceptional types. These specializations are
checked through n=32; four mixed marker choices are compared with literal
edge sets through n=8.

One raw-moment calculation propagates six exact integer totals in the rooted
component recurrence: count, K, K^2, D, D^2, KD. Adding a component changes
(K,D) to (K+1,D+d_component), and the six update formulas follow by multiplying
out these expressions. This recurrence has no ratios or floating arithmetic.

The independent route uses EGF products. If A is the count sequence and K1 its
first component-count total, then

    K1_n=sum_m binomial(n,m)c_m A_(n-m),
    K2_n=K1_n+sum_m binomial(n,m)c_m K1_(n-m).

Put R_j=(n)_j A_(n-j), U_j=(n)_j K1_(n-j), interpreted as zero when n<j,
and let i=1 for A323297, i=0 for A323296. The remaining numerators are

    D1=i R_1+R_4/4,
    D2=i(R_1+R_2+R_5/2)+R_4/3+R_8/16,
    KD=D1+i U_1+U_4/4.

The fractional expressions are verified to be integral. Both routes agree
through n=640 for both models, including empty and impossible small sizes.
No division by a zero count is needed in these checks.

A separate marked recurrence propagates every mixed falling-factorial total
(S)_a(T3)_b(T4)_c of total order at most three through n=32. Adding a component
of one exceptional type increments just that variable, using
(x+1)_j=(x)_j+j(x)_(j-1). The results agree exactly with the finite-shift identity

    total_n[(S)_a(T3)_b(T4)_c]
      = i^a (n)_(a+4b+4c) A_(n-a-4b-4c)/(6^b 24^c).

This supplies exact checks of the marked identities underlying the Poisson
conditioning calculation. It does not itself prove the distributional limit.

## Exact symbolic verification

For fixed order ell, the E_ell algorithm enumerates nonnegative k_j satisfying
sum_(j>=3)(j-2)k_j=2ell. With M=sum j k_j, each term is

    (-1)^(M/2)(M-1)!! product_j kappa_j^k_j/(j!^k_j k_j! b^(M/2)).

The public implementation permits ell=0,...,4, with respectively 1,2,5,11,22
terms. The displayed E1 and E2 are checked against this formula and separately
against a direct truncated expansion of

    exp(sum_(j>=3) kappa_j (ix)^j h^(j-2)/j!).

The second calculation extracts a power of h and then integrates the resulting
polynomial by exact Gaussian moments; it does not call the composition enumerator.

The recurrence P_(j+1)=(z+2)P_j+zP_j' for derivatives of z^2 exp(z)/2 is checked
through P8 against direct symbolic differentiation. Exact marked derivatives
also check d=r+r^4/4, tau^2=r+r^4/3, and eta=r+r^4.

For inverse logarithmic coefficients, put t=1/L, ell=log L, c=log 2, and

    R=t^(-1)+a0+a1 t+a2 t^2,
    g(R)=R+2log R-c-1+3/R-4/R^2+20/(3R^3)+... .

The program formally solves the coefficients of
R+3log R-c+log(1+2/R)+log g(R)-1/t through t^2, defining
log R=ell+log(tR). Each new coefficient is checked to have unit pivot. It then
expands 1/(t g(R)) and verifies the displayed relative inverse coefficients
q0,...,q3, including every log(2) term. Analytic remainder control and the
integer-threshold caveat belong to the article, not this symbolic calculation.

## NONCERTIFIED floating diagnostics

`diagnostics.py` uses exact integer input counts and raw moments, then mpmath
floating roots, logarithms, exponentials, and normalized ratios. The default
precision is 60 decimal digits and the displayed sizes are 32,80,160,320,640.
The output contains:

- exact-saddle count factors and errors divided by (r/n)^(J+1), J=0,1,2,
  using each model's own saddle
- K and defect mean/variance/covariance diagnostics for both models
- exceptional likelihood and deletion diagnostics for A323297

For the last group, aggregate T3+T4 to Y~Poisson(5r^4/24), independent of
S~Poisson(r). The likelihood depends on the triple only through W=S+4Y, so
this aggregation preserves the exact total variation expression before
numerical truncation. The Poisson weights are generated by

    q_0=exp(-r-lambda),
    w q_w=r q_(w-1)+4 lambda q_(w-4), lambda=5r^4/24.

The exact-count likelihood is evaluated as

    h(w)=exp(r+lambda)(n)_w Aordinary_(n-w)/(r^w A_n)

for w<=n, and zero otherwise. The ordinary sequence deletes isolates and both
tetrahedron types. The cutoff is ceil(mu+20 sqrt(v)+100), bounded above by 5000.
The code reports truncated Q mass and conditioned mass along with truncated
TV and the L1 error of the quadratic likelihood correction. It does not provide
certified bounds on omitted Poisson tails. A printed mass rounding to one is
not a proof of exact normalization.

No observed trend is used as a pass/fail assertion. No decimal is an interval
certificate. In particular these tables do not certify a TV constant, an
asymptotic error bound, a range of validity, or an integer inverse threshold.

## Bounds, decimal conversion, and guard tests

The recurrence and large raw-moment routines accept n=0,...,640. Literal edge-set
enumeration accepts n=0,...,8. Fully marked counts and exceptional factorial
moments accept n=0,...,32. Marker values are integers 0,...,3. The verifier's
n is 24,...,640. Diagnostics and saddle roots use n=32,...,640 and precision
30,...,100. Cumulants allow orders 0,...,12 and a finite real radius 0<r<=20.
Symbolic E orders are 0,...,4. Booleans and equal-valued floats are rejected
where integers are required; model flags must be actual booleans.

All validation uses explicit exceptions, never assert. The finite suite checks
API and CLI boundaries, optimized execution, decimal-cap enforcement, exclusive
file creation, invalid output paths, symlinks, source-tree writes, manifest
corruption and omissions, unexpected files/directories, and malformed archives.
These guards are not a general security proof or protection against hostile
concurrent filesystem mutation.

Every public process sets sys.set_int_max_str_digits(640). Every Python child
command explicitly uses -B and an explicitly selected normal or optimized mode;
PYTHONOPTIMIZE is reset in its environment. Source-level cap and bytecode
settings remain effective if environment variables are ignored.

The n=640 counts exceed 640 decimal digits and are never rendered in decimal.
The digest encoding writes, for each integer: one byte for negativity, four
unsigned big-endian bytes for magnitude-byte length, and at least one unsigned
big-endian magnitude byte. Zero is encoded with one zero magnitude byte.
Bit lengths and SHA256 hashes give stable exact-count receipts.

## Immutable builds, freeze, and archive replay

The frozen package's manifest lists all files except itself. Verification
requires exactly these hashes, exactly the implied directory set, and no
symlinks or nonregular entries. Limits are 500 files and 32 MiB total source
bytes. New outputs must be outside the package with existing parents. Builds
write no source-tree caches, logs, auxiliary files, or archives.

TeX runs in a disposable source copy, creates a private format and cache, and
compiles three times. Every executable TeX invocation has -no-shell-escape,
with shell_escape=f and restricted openin/openout settings. The environment
fixes SOURCE_DATE_EPOCH=1791158400, FORCE_SOURCE_DATE=1, TZ=UTC, and LC_ALL=C.
The PDF must equal the frozen PDF byte for byte; the listed layout/reference
warnings are fatal. Mathematical and visual review remain separate obligations.

The authoring freeze is deliberately separate from the public build:

1. Finalize and review article sources and public code; run all four default
   verifier commands normally and with -O outside the source tree
2. Copy the matching JSON receipts to `code/*_receipt.json`
3. Create a new external log directory and call `build.compile_pdf(log_directory)`
   to obtain PDF bytes; after review, save them as `Report240.pdf`
4. Write SHA256 lines for every package file except `MANIFEST.sha256`, using
   sorted relative paths. Do not include a package ZIP or temporary files
5. Run `build.py --verify-only`, then a full external build, then actual-ZIP replay

`compile_pdf` is the sole authoring helper; it does not write the PDF or mutate
sources. The public build never refreshes a receipt, PDF, or manifest in place.
Any subsequent source edit requires a new reviewed freeze and replay.

ZIP members use sorted order, stored compression, fixed 2026-10-05 00:00:00
member timestamps, Unix creator metadata, regular-file mode 100644, and empty
extra fields/comments. Replay validates the actual archive, extracts two
independent copies, runs normal and -O builds, and compares all bytes, members,
metadata, PDFs, receipts and build checks. It verifies that source trees and
the original archive remain unchanged. Before executing extracted code, it
requires archive contents to equal the trusted package already running it.

SHA256 is an integrity mechanism, not a signature or proof of priority.
Reproduction depends on the installed recorded toolchain. There is no claim
of PDF-byte equality across arbitrary Python, SymPy, mpmath, or TeX versions.
