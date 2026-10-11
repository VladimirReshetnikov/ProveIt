INDEPENDENT POLYNOMIAL HURWITZ RESOLVENT DIAGNOSTICS
=================================================

Target
------
The polynomial master transform and weighted Stieltjes generator in
sections/02_weighted_transform.tex of
Barnes_Resolvents_and_Harmonic_Identities. In particular, the labels are
bhr:eq:weighted-master, bhr:eq:Bpoly, and bhr:eq:weighted-stieltjes.

Files and reproducibility
-------------------------
Requirements: Python 3 and mpmath (the recorded run used Python 3.12.14
and mpmath 1.3.0). There are no nonstandard local imports except the
companion main script used by the tail diagnostic.

Run from any working directory:

    python /path/to/check_weighted_transform.py
    python /path/to/check_tail_backend.py

Each script writes its JSON results next to itself. The main run took
about 54 seconds in the recorded environment. The tail check is shorter.
No manuscript evaluator is imported.

Independent representations
---------------------------
The first side forms U_j and V_j directly as the subtracted double sums
displayed in the article. For 1 <= n <= 105, it sums 1 <= m < 256
explicitly and expands the remaining inner tail in powers of n/m.
The k=0 term cancels identically. Terms k=1,...,48 have the common
Hurwitz factor zeta(s+j+k,256). For U_j the coefficient is
(-1)^k (j)_k n^k/k!; for V_j it is (-1)^k (s)_k n^k/k!.
The latter coefficient is differentiated by its product recurrence.
The derivative of the Hurwitz factor is included in both sums.

The tiny Hurwitz tails are evaluated with 40 Euler--Maclaurin terms,
factoring out M^(1-p):

 zeta(p,M) approximately equals
 M^(1-p) [1/(p-1) + 1/(2M)
          + sum_{k=1}^{40} B_{2k}(p)_{2k-1}/((2k)! M^(2k))].

The first order derivative is calculated analytically from this same
scaled expression. Polylogarithms and their order derivatives are
ordinary convergent q-series with the same outer truncation n=105.

The second side is direct x-quadrature of the actual Hurwitz zeta
integrand, of its first spectral derivative
-zeta_order_prime(1-s,x), or of gamma_0(x)=-digamma(x).
The quadrature interval is split at 0, 0.1, 0.35, 0.65, 0.9, and 1.
The analytic spectral derivative of Gamma(s) times the bracket uses
Gamma(s) [B'(s)+digamma(s)B(s)]. The Stieltjes check uses
c/q [B'(0)-EulerGamma B(0)] and independently checks B(0).

Recorded main results
---------------------
All calculations below used 65 decimal digits of working precision.
The Cayley coordinate is z = epsilon*i*pi*(1+q)/(1-q).

 P    epsilon  q             s             test             abs residual
 x    +1       .2+.1i        1.7+.2i        value            2.39e-69
 x    +1       .2+.1i        1.7+.2i        first derivative 1.04e-68
 x^2  -1       -.25+.05i     2.3-.15i       value            1.79e-66
 x^2  -1       -.25+.05i     2.3-.15i       first derivative 8.15e-66
 x^2  -1       -.25+.05i     0              Stieltjes m=0    5.32e-63

The additional B(0) identity residual was 8.71e-64.
The main script requires every scaled residual to be below 1e-30.

Why the scaled tail evaluator matters
------------------------------------
An initial version passed tiny complex Hurwitz tails directly to
mpmath.zeta at the main working precision. In this setting that backend
can have an absolute error floor much larger than a tiny tail itself.
Multiplication by the binomial factor n^k then amplifies the error.
For example, at p=50.7+.2i and M=256 the unguarded 65-digit call has an
observed relative error about 9.1e50 against a guarded 250-digit call.
The scaled Euler--Maclaurin version has relative residual 4.6e-67 for
the value and 1.8e-67 for the first derivative in that same test.

check_tail_backend.py reproduces three comparisons, including both
complex spectral directions and a moderate-order control. The largest
relative residual of the scaled values or derivatives in those three
tests is below 4.0e-66. It requires residuals below 1e-60.

Interpretation
--------------
These are independent floating-point diagnostics, not interval
enclosures, certified error bounds, or substitutes for the proof.
Numbers near the working-precision floor must not be interpreted as
certified digits. The sampled cases comfortably exceed the requested
25-digit diagnostic agreement, exercise both half-plane phases, and
test the pole-removed Stieltjes coefficient as well as ordinary
spectral values and derivatives.
