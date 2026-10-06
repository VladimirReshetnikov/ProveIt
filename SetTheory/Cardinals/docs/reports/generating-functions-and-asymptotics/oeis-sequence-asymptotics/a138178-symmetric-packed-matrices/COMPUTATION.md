# Computational supplement to Report238

## Scope

The article proves the all-order expansions and probability limits. This package
checks finite identities independently, verifies the displayed initial
coefficients algebraically, and records finite numerical diagnostics. No finite
table establishes a uniform asymptotic remainder. In particular, the decimal
moment data do not prove total variation convergence or identify an effective
onset for it.

All dimensions are ordered. Matrices differing by simultaneous row/column
permutation remain different objects. Off-diagonal entries contribute twice to
total sum. The trace marker records the sum of diagonal entries. R counts
individual diagonal cells whose entry is at least two; S counts upper-triangle
off-diagonal cells whose entry is at least two, one per symmetric pair. Neither
statistic counts the number of extra units beyond one.

## Exact recurrence and transform

Let f_n(k,v) be the coefficient of z^n in

    (1-vz)^(-k) (1-z^2)^(-k(k-1)/2).

For v=V/D define the integer polynomial Q_n(k)=D^n n! f_n(k,V/D).
Logarithmic differentiation and multiplication by (1-vz)(1-z^2) give

    Q_(n+1) = V(k+n) Q_n
              + n D^2 (k^2-k+n-1) Q_(n-1)
              - V D^2 n(n-1) (k^2+n-2) Q_(n-2),
    Q_0=1, Q_1=Vk.

The last term is absent when n=1. At V=D=1 this reduces to

    Q_(n+1)=k Q_n+n(k^2+n-1)Q_(n-1).

For integer u, write P_j(u)=sum_d S(j,d)d!u^d. The independent recurrence

    P_0(u)=1,
    P_j(u)=u sum_(r=1)^j binomial(j,r) P_(j-r)(u)

computes the ordered-Bell transform. If Q_n=sum_j q_(n,j) k^j, then

    A_n(u,V/D) = sum_j q_(n,j) P_j(u)/(D^n n!).

The program uses Python integers and Fraction; no numerical approximation enters
these calculations. It does not evaluate the infinite auxiliary-dimension sum.
The main routines are quadratic in polynomial-array operations; large integer
bit costs and stored coefficient arrays add substantial resource requirements.
The limit 640 is enforced before work begins.

## Independent checks

The stars-and-bars coefficient at fixed auxiliary dimension k is

    sum_(t+2m=n) binomial(k+t-1,t) binomial(k(k-1)/2+m-1,m) v^t,

where a zero-cell factor is one only for zero units. Binary cells instead give
binomial(k,t)binomial(k(k-1)/2,m). Inclusion–exclusion deletes zero lines:

    packed dimension d = sum_(k=0)^d (-1)^(d-k) binomial(d,k) f_n(k,v).

Summing with weight u^d gives a calculation independent of the polynomial
recurrence and ordered-Bell transform. The default receipt compares unmarked
counts through n=32; four rational dimension/trace marker choices through n=16;
and the published A138178 prefix through n=24.

The collision numerator factors

    [1+(w-1)v^2z^2]^k [1+(zeta-1)z^4]^(k(k-1)/2)

provide a second exact marked calculation. The zero markers w=zeta=0 agree with
binary inclusion–exclusion through n=12 and with the A135588 prefix on that
range. Unit markers agree with the nonnegative counts. Direct enumeration of
actual upper-triangle cells through n=6 independently checks the full joint
(dimension, trace, R, S) distribution, three mixed rational marker choices,
binary specialization, trace parity, and moment formulas.

Sources for the copied finite sequences:

- https://oeis.org/A138178, prefix n=0,...,24
- https://oeis.org/A135588, prefix n=0,...,12

Both were checked while this supplement was prepared. No live network access is
needed for reproduction; these finite checks are frozen in the source.

The involution recurrence J_n=V J_(n-1)+D^2(n-1)J_(n-2), with J_0=1 and J_1=V,
is independently compared through n=640 with the explicit factorial sum

    J_n=sum_(j=0)^floor(n/2) n! V^(n-2j)D^(2j)/((n-2j)! 2^j j!).

The four trace choices include zero and nonintegral rational values.

## Collision moments

Let T(p)=sum_j [k^j]p(k) P_j(1), and Z_n=T(Q_n)=n! A_n. Write (n)_a for the
falling factorial, interpreted as zero when n<a. Then

    E R = (n)_2 T(k Q_(n-2))/Z_n,
    E S = (n)_4 T((k^2-k) Q_(n-4))/(2 Z_n),
    E (R)_2 = (n)_4 T((k^2-k) Q_(n-4))/Z_n,
    E (S)_2 = (n)_8 T((k^4-2k^3-k^2+2k) Q_(n-8))/(4 Z_n),
    E RS = (n)_6 T((k^3-k^2) Q_(n-6))/(2 Z_n).

A separate exact checker chooses distinguished diagonal and off-diagonal cells
at each k, uses (k)_r (k(k-1)/2)_s f_(n-2r-4s)(k,1), then deletes zero lines by
inclusion–exclusion. All five moments agree through n=12, including nonzero
second off-diagonal moments. The direct enumeration supplies another comparison
through n=6. Exact rational moments are converted to floating point only in the
explicitly noncertified diagnostic script.

## Symbolic coefficient checks

The first derivation substitutes the coupled gamma/Cauchy saddle into the local
logarithm and applies independent centered Gaussian moments with variances 1 and
1/2. Through h^2, h=n^(-1/2), it retains the gamma and angular normalization
corrections. In particular E(H_1)=v/4 is subtracted in the quotient expansion.
The second derivation uses factorial-degree moments of the leading logarithmic
atoms and does not reuse the Gaussian averaging operation. The results agree
exactly for C_1, C_2 and D_2=C_2-C_1^2/2.

The collision first correction is also checked symbolically:

    C_1^* = -v(a L+2c L^2)+v^3 L^2/3,
    a=(v^2-1)/2+(w-1)v^2,  c=(2 zeta-1)/4.

Its unmarked and binary specializations and the mean-correction polynomial at
v=1 are checked. An independent expansion of the exact involution recurrence
verifies the initial logarithmic involution coefficients. A rational lower and
upper bound for log(2), obtained by eight terms of its atanh series and an
explicit geometric tail, certifies 1<log(2)+log(2)^2<2. This last inequality is
the only numerical enclosure certified by this script; no decimal remainder
diagnostics are thereby certified.

The finite symbolic program verifies the displayed initial coefficients. It
neither implements nor claims that arbitrary requested orders can be computed
practically. The article's finite formal prescription at each fixed order and
its analytic remainder proof are mathematical statements distinct from this
bounded implementation.

## Decimal diagnostics

`diagnostics.py` defaults to 60 decimal working digits and evaluates n=32, 80,
160, 320, 640. Three positive dimension/trace choices compare exact counts with
the first two asymptotic corrections. Collision diagnostics display means,
variances, covariance and scaled first-mean errors. All integer inputs and
moments are exact before conversion; all displayed logarithms, exponentials,
normalized errors and decimals use mpmath floating point. They are diagnostic,
not interval-certified, and no observed trend is used as a test assertion.

## Bounds and validation

Public routines reject nonintegers, booleans, negative sizes and over-limit
sizes before computation. There are no caches. Limits are n<=640 for recurrences,
transforms, involutions and collision moments; n<=32 for plain deletion; n<=12
for collision deletion; and n<=6 for direct enumeration. Dimension marker u is
an integer 1..4; trace numerator V is 0..4 and denominator D is 1..4; collision
markers are integers 0..3. Diagnostic n is 32..640 and precision is 30..100.
These are verifier domains, not restrictions on the theorem's complex markers.

Every validation uses explicit exceptions, never assert. The test suite checks
normal and optimized execution, invalid API and CLI inputs, strict booleans,
file reuse, live and dangling symlinks, dot components, source-tree outputs,
manifest corruption/omissions/extra files/extra directories, and malformed ZIPs.
The tests are finite guards, not a general security proof or protection against
hostile concurrent filesystem mutation.

## No large decimal conversions

The integer decimal-conversion limit is fixed at 640 digits. All Python child
commands include -B explicitly and set PYTHONINTMAXSTRDIGITS=640; an ambient
optimization setting is cleared before the intended normal/-O mode is applied.
The n=640 count has more than 640 decimal digits and is never rendered as such.
The SHA256 sequence encoding is, for each integer: one byte for negativity,
four unsigned big-endian bytes for magnitude-byte length, then at least one
unsigned big-endian magnitude byte. Zero uses one zero magnitude byte. Digests
and bit lengths allow stable receipts without weakening the conversion limit.

## Immutable builds and actual archive replay

All frozen files except MANIFEST.sha256 are listed in that manifest. Verification
requires exactly that file set, its hashes, and exactly its implied directory
set. Symlinks and nonregular entries are rejected. Outputs must be new and
outside the sources, with existing parents. No cache, log, TeX file or archive is
written into the package during verification, building or replay.

TeX builds a private format and compiles a disposable copy three times. Every
TeX invocation specifies -no-shell-escape; shell_escape=f and restricted
openin/openout settings are also set. SOURCE_DATE_EPOCH=1791158400, FORCE_SOURCE_DATE=1,
TZ=UTC and LC_ALL=C fix time and locale. PDF bytes must equal the frozen PDF.
Layout/reference warnings listed in build.py are fatal. Visual quality and the
article's mathematical content additionally require human-level review.

The ZIP uses sorted member order, stored compression, a fixed 2026-10-05 00:00:00
member timestamp, Unix creator metadata, regular-file mode 100644, and empty
extra fields/comments. The external actual-archive replay compares all members,
metadata, complete ZIP bytes, PDF, receipts and build checks across two clean
normal/-O builds. It checks that both extracted source trees and the original
trusted package remain byte-identical. It will only execute an archive whose
contents match the trusted package already running the verifier.

Hashes establish consistency, not authorship. Reproducibility depends on the
installed, recorded toolchain. The package makes no cross-platform PDF-byte
promise and performs no network access or package installation during a build.
