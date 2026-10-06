# Computational supplement to Report239

## Exact model and indexing

A symmetric n by n sign matrix has n(n+1)/2 independent entries. A -1
outside the diagonal becomes an edge between the corresponding vertices. A -1
on the diagonal becomes an edge from that vertex to a new vertex, labelled
n+1. Thus its ith row sum is n-2d_i, so nonnegative row sums mean
d_i<=floor(n/2) for precisely the first n graph vertices. The new vertex is
unrestricted. In particular A027832(n)=U_1(n+1,floor(n/2)).

The published record begins at n=1 and contains 17 displayed terms, through
n=17. `oeis_prefix.json` records the official record/mirror URLs and revision.
The verifier regenerates every one of these terms; it does not count reading
or hashing a term as an independent arithmetic check. The empty order n=0 is
added separately with value 1.

## Grouped-cap recursion

For a sorted list of remaining degree capacities, delete one vertex of
capacity c. Divide the other vertices into groups of equal capacity j and
size g_j. Choose t_j neighbours in each group, with
0<=t_j<=g_j and sum(t_j)<=c. The choice has multiplicity
product(binomial(g_j,t_j)); chosen vertices lose one unit of capacity.
Recursively count the remaining graph and sum with these exact multiplicities.
Negative capacities are never produced: zero-cap vertices are removed first,
since they cannot be incident to an edge. Capacities larger than the number of
remaining possible neighbours are clipped. An entirely unrestricted residual
graph has the closed count 2^binomial(r,2). Sorting is a relabelling symmetry;
the binomial factors retain the number of labelled choices.

The recursion uses integer arithmetic and a bounded per-computation cache.
At most 200,000 states and 8,000,000 completed transition branches are allowed;
exceeding either limit raises an explicit exception. These are operational
stops, not theorem hypotheses. The default receipt records actual usage.

Independent checks enumerate all symmetric sign matrices for n=0..5 literally,
including each diagonal entry once in its row sum. A second enumeration runs
through all edge subsets for every M=0..6, every legal uniform cap, and every
f=0..M. It compares with the recursion. For M=2..12 and every f, the verifier
also checks the integer forms of

    B <= U_f <= 2^binomial(M,2)
    U_f [sum_{d<=k} binomial(M-1,d)]^f <= B 2^((M-1)f)

at k=floor((M-1)/2). It verifies the all-free identity exactly.

For b=1..32, r in {1/10,1/4,1/2,3/4,9/10}, and every cap k, it verifies
Var(Bin(b,r) | X<=k)<=b/4 using unnormalized integer weights
binomial(b,d) a^d (D-a)^(b-d), where r=a/D. If their partial moments are
T, T1, T2, the checked inequality is 4(T2*T-T1^2)<=b*T^2. These finite
checks corroborate the article's proof; they do not replace its general bound.

## Rational constant certificate

No floating-point operation participates in `constant_certificate.py`.
All interval endpoints are `fractions.Fraction` values. Let

    F(x)=exp(-x^2/2)-x[sqrt(pi/2)+integral_0^x exp(-t^2/2) dt].

Its positive zero is exactly the positive solution of phi(x)=x Phi(x).
Moreover F'(x)=-2x exp(-x^2/2)-sqrt(pi/2)-integral_0^x exp(-t^2/2)dt
is negative on x>=0. The program certifies opposite signs at 1/2 and 51/100
and then uses exact rational bisection. Every branch requires a strict sign
from the enclosing interval; an inconclusive sign raises an exception.

Machin's identity pi=16 arctan(1/5)-4 arctan(1/239), with 96 alternating
terms in each arctangent series and the following term as remainder bound,
supplies a rational interval for pi. Square roots are enclosed on the grid
10^-90 by integer square root; both rational endpoint bounds are retained.
Exponential and integrated Gaussian series use 64 terms and the first omitted
term, with alternating remainders of known sign. Positive exponentials are
computed by reciprocal intervals for negative arguments. The internal domains
are |x|<=2 for exponentials and 0<=x<=1 for Gaussian integrals; the needed
expressions stay in these domains. Interval operations conservatively keep
endpoint dependence rather than treating dependent expressions as independent
point estimates.

The program encloses ell, Phi(ell), its reciprocal, and

    q=Phi(ell) exp(-ell^2/2)
    Z0=exp(5ell^2/4-ell^4/2)/sqrt(1+2ell^2)
    J=-4ell^2/(1+2ell^2)
    v=(1-2ell^2)/4

as well as the odd/even prefactors and the critical-window coefficients
ell^2/[2(1+2ell^2)] and 2ell/(1+2ell^2). Output decimal endpoints are rounded
outward with integer floor/ceiling. The default has 30 decimal places and 160
root bisections. The certificate covers the constants only; it does not certify
an asymptotic error, an onset, or an inverse counting threshold.

## NONCERTIFIED diagnostics

`diagnostics.py` uses Python binary64 floating point and the platform libm.
Its capped binomial weights are separately rescaled on the full and truncated
supports before computing moments. Its finite-M saddle solves

    E[Bin(M-1,r) | X<=k]=(M-1) r^2/[r^2+(1-r)^2]

by a bounded bisection with r=1/2-L/(2 sqrt(M)) and k=floor((M-1)/2).
The reported residual is a floating diagnostic, not a certified root interval.
The program reports the one-free leading ratio through n=17 and finite critical
window comparisons for M=8..18 with f equal to 1, floor(sqrt(M)), or twice that
integer. It compares both the exact-saddle-S expression and the explicit Phi
expression with exact integer graph counts. Its values are small-order
illustrations and cannot establish uniform relative errors or an asymptotic
regime. Large-M saddle rows are not large-M exact graph counts.

## Public bounds and preflight

Every type/range check uses an explicit exception and rejects bool where an
integer is required. `sign_matrix_count`: n=0..17; `capped_graph_count`: a
list/tuple of at most 12 capacities, each integer 0..M-1 (0 for M=0);
`mixed_graph_count`: M=0..18, 0<=f<=M, and 0<=k<=min(8,M-1), with full
k=M-1 also allowed. For the empty graph, k=0 is used. `brute_sign_matrices`:
n=0..5; `brute_mixed_graphs`: M=0..6, with all legal k and f.
`verify`: largest n=1..17. `capped_moments`: b=1..2000, 0<=k<=b, finite
0<r<1; `fixed_saddle`: M=8..2001 and the specified central cap only.
`diagnostics`: largest M=21..2001. `certified_constants`: decimal digits=20..40.
Validation occurs before enumeration, series evaluation or output creation.

All Python processes set the integer decimal conversion limit to 640 digits.
Every Python child command explicitly supplies both -B and
-X int_max_str_digits=640; environment variables repeat these settings and
clear ambient optimization before the desired normal/-O command is chosen.
The exact counts here are short enough for decimal receipts. Large temporary
rational numerators used by the constant certificate are never converted to
decimal strings; only rounded endpoints are rendered.

Guard tests cover invalid API and CLI inputs, bool/float confusion, both
recursion budgets, output reuse, source-tree output paths, live/dangling
symlinks, dot components, missing parents, manifest corruption/omissions,
unlisted files/directories, and malformed ZIP members. They also check the
absence of assert-based validation. They are finite tests, not a general
security proof or protection against hostile concurrent filesystem mutation.

## Immutable build and actual ZIP replay

The manifest lists every frozen file except itself. Verification requires an
exact match of hashes, file names, and implied directory names. Source inventory
work is capped at 1,000 entries, 500 files and 32 MiB before hashing beyond
those limits. Symlinks and
nonregular entries are rejected. Source bytes and directory inventory are
checked before and after building. Outputs are exclusively created outside
the package. The build creates no source cache, TeX auxiliary file or archive.

TeX builds a private format and compiles a disposable copy three times. Every
TeX executable command has -no-shell-escape; shell_escape=f and restricted
openin/openout settings are also used. SOURCE_DATE_EPOCH=1791158400,
FORCE_SOURCE_DATE=1, TZ=UTC and LC_ALL=C fix time and locale. Every receipt and
the PDF must match its frozen version. The specified layout/reference warnings
are fatal. Visual review and mathematical review remain separate requirements.

The ZIP uses sorted members, stored compression, a fixed 2026-10-05 00:00:00
member timestamp, Unix creator metadata, mode 100644, and empty comments/extra
fields. Actual archive replay extracts two copies, rebuilds normally and with
-O, and compares every member byte/metadata field, complete ZIP bytes, PDFs,
four receipts, and build checks. All seven top-level output files must agree.
Only an archive whose members match the trusted source tree is executed. This
is an integrity check, not a digital signature, and cannot authenticate an
unknown package by itself. Reproduction uses the installed recorded toolchain;
it promises no cross-version or cross-platform PDF identity. Builds perform
no network access or package installation.
