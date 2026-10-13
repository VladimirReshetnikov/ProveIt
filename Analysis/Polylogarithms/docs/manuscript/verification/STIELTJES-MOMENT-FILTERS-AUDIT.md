# Algebraic colors, logarithmic identities, and finite dilation filters

This research continues the published character-moment release
`13f23f675e9fcd3c2da4b71592c6dfd95e423c9c`. The new material belongs to
Volume III, after the nonprincipal-character section. The collective
author remains ProveIt Contributors. No incoming source or original
evidence is modified by these additions.

## Algebraic order-fifteen point

The earlier bounded theorem excludes *consecutive* vanished tails through
order eight. The new point proves that an individual nonalternating
unit-circle tail can vanish at a positive real shift. It does not disprove
the consecutive-tail conjecture or extend the bounded exclusion theorem.

The Cayley recurrence generates U15 and V15 as polynomials in
X=(a-1/2)^2 and Y=t^2. Their primitive integer forms have a resultant
proportional to H7(Y) P(Y), where H7 has positive coefficients and degree
seven. P has degree 42. Its coefficients are negative in degrees 0--31
and positive in degrees 32--42. Since P(1)<0<P(2), Descartes' rule proves
one positive root, counted with multiplicity, hence a simple root.

The linear penultimate subresultant supplies a rational lift N/D. After
cancellation and reduction modulo P, its numerator and denominator have
degrees 37 and 36. The coefficient certificate is explicit, and the
manuscript also specifies the polynomials by the recurrence and resultant
construction. No irreducibility or minimal algebraic degree is asserted.

The independent verifier reconstructs the original Lerch numerator
recurrence in (omega,a), rather than using the discovery recurrence in
Cayley coordinates. It verifies both identities D^7 U15(N/D,Y)=0 and
D^7 V15(N/D,Y)=0 modulo P. Exact rational interval Horner evaluation
isolates the positive root, proves D nonzero there, and proves the lift
lies in the printed positive X,Y rectangle. Strictly positive real
components of the neighboring tails establish A14 and A16 nonzero.

This is an exact existence certificate at the specified point and its
conjugate. The preceding scalar theorem gives the ordinary integral

    integral x^15 C15^omega(x,a) dx = -partial_s Phi(omega,-15,a).

The vanished leading tail and nonzero next tail prove that exactly one
extra positive-integer moment exists. No direct high-order quadrature at
the algebraic point is claimed. Its proof uses the exact algebraic
hypotheses and the already proved analytic Mellin theorem.

The research verifier was hardened before publication: checks do not
disappear under Python optimization, polynomial strings use a restricted
arithmetic parser, interval arrays have exact arity, all mathematical
certificate fields are checked, duplicate JSON fields are rejected, and
an unsuccessful run cannot leave a stale passing receipt. These changes
strengthen reproducibility; they do not repair a mathematical flaw in the
original certificate.

## Logarithmic moments and real isolation

At any vanished tail A_q=0, the common ordinary Mellin neighborhood
around u=q+1 allows every logarithmic weight. The quotient
Q_(q+1)(q+1+h)/Q_q(q+1+h) is analytic and vanishes at h=0. Comparing
Taylor coefficients gives the complete triangular logarithmic hierarchy.
Its first coefficient is

    kappa_q = integral (t/(exp(t)-1))^(q+1) dt
            = (q+1) sum_{r=0}^q (-1)^r e_r(1,...,q) zeta(r+2).

The positive integral follows by a nonnegative exponential expansion
and Tonelli. Thus the identity integral x^q [log(x/c) C_(q+1)-kappa_q C_q]=0
holds for every c>0, with each term itself absolutely integrable. The
explicit first logarithmic moment of C_q involves the first and second
order derivatives of Phi. The finite harmonic corrections are checked
symbolically; numerical checks at an alternating low-order example are
separate from the exact order-fifteen root certificate.

Separate simplicity in each complex variable does not by itself prove
isolation in the real parameter plane. The additional calculation uses
the determinant with coordinates (a,theta), omega=exp(i theta):

    J = 15 Re(conjugate(A14) A16)
      = 15(1+Y)/4 [U14 U16 + X Y V14 V16].

An independent Cayley reconstruction and rational interval evaluation
prove -5*10^20 < J < -4*10^20. The real inverse-function theorem therefore
gives local isolation among positive real shifts and unit-circle colors.
This is a local statement, with no complete order-fifteen locus claimed.

## Finite dilations and principal characters

The scalar balanced Stieltjes transform and its original report remain
attributed in the manuscript. For a finite Dirichlet polynomial
D(s)=sum c_j h_j^(-s), direct scaling multiplies the scalar Mellin
transform by D(1-u). The kernel is sum (c_j/h_j) C_q(x/h_j,a); its
Laurent definition must subtract D(1)/z. Dropping this scalar subtraction
would make the principal-character completion incorrect.

The full tail expansion proves that an extra ordinary integer moment
at m exists exactly when D(-k) zeta(-k,a)=0 for every q<=k<=m-1. A first
nonzero complex tail has a nonzero real or imaginary component and makes
the ordinary integral diverge. A zero block gives absolute convergence
at both endpoints and permits evaluation by the removable Mellin value.

Taking D(s)=P_(q,r)(lambda^(-s)), with
P_(q,r)(y)=product_{ell=q}^{q+r-1}(1-lambda^(-ell)y), cancels r prescribed
tails for every a>0. The new moments reduce to Bernoulli-polynomial
values times log(lambda), because the factor D supplies the zero. If
the Bernoulli value also vanishes, the ordinary moment is zero. The
special q=0 factor is simply 1-y; no division by 1-lambda^0 is used.

For uniform cancellation on an open interval of shifts, each Bernoulli
coefficient is a nonzero polynomial. A Vandermonde argument then proves
that r+1 distinct positive scales are necessary. The statement does not
claim minimality at exceptional fixed shifts with Bernoulli zeros.

For principal characters, inclusion--exclusion identifies the finite
residue-class kernel with the dilation kernel at a=1. The subtraction
is phi(d)/(d z). Negative even zeta zeros give precisely one extra
moment at each positive even order; odd orders have none. At order zero,
d=1 has none, a prime-power modulus gives -log(p)/2, and a modulus with
two or more distinct primes gives zero. The next tail is nonzero, so
these order-zero blocks have length exactly one.

The root researcher and an independent reviewer checked all signs,
normalizations, convergence assertions, minimal-scale scope, and the
explicit digamma and first-index Stieltjes examples. Classical inputs
were verified in DLMF 25.11.14 (Hurwitz values) and 25.4.2 (zeta reflection):
https://dlmf.nist.gov/25.11.E14 and https://dlmf.nist.gov/25.4.E2.
No historical-priority claim is inferred from these targeted checks.

## Evidence boundaries

Reproduction from the manuscript directory:

```powershell
py -O verification/check_stieltjes_order15.py
py -O verification/check_stieltjes_order15_consequences.py
py verification/check_stieltjes_logarithmic.py
py -O verification/check_stieltjes_dilations_exact.py
py verification/check_stieltjes_dilations_numeric.py --output verification/check_stieltjes_dilations_numeric60.json
py -O verification/check_stieltjes_dilations_numeric.py --precision 75 --em-n 84 --em-r 62 --tail-order 120 --cutoff 80 --output verification/check_stieltjes_dilations_numeric75.json
```

The root researcher replayed the order-fifteen verifier (35 exact checks
and 20 rejected corruptions), the independent consequences checker
(66 exact checks), and the finite-dilation checker (980 exact checks
and four rejected wrong formulas), all under Python optimization.
The optional `generate_stieltjes_order15.py --output PATH` was also
replayed into scratch; its fresh exact subresultant construction
reproduced the canonical certificate with identical normalized bytes.
That separate result is recorded in `stieltjes-order15-regeneration.json`.

The logarithmic diagnostics compare the coefficient at q=1,4,15 through
both its finite zeta sum and positive integral at 50 and 65 digits.
Eight ordinary low-order logarithmic integrals were evaluated at those
precisions, with maximum residuals 6.69e-52 and 5.94e-67. All four
wrong-sign/missing-coefficient controls were rejected. These are tests
of the general formulas at an alternating low-order point, not numerical
evaluation of the algebraic order-fifteen integral.

The dilation diagnostics independently evaluate the finite scalar kernels
and their tails. Eleven ordinary moments were checked at 60 digits
(Euler--Maclaurin parameters 72/52, tail order 100, cutoff factor 64),
then at 75 digits (84/62, 120, 80). The maximum residual improves from
8.59348880991e-62 to 2.76357393763e-75. The examples cover three digamma
moments, nonintegral shifts, first- and second-index Stieltjes kernels,
and the principal-character zero and positive-even cases. Corresponding
computed values differ by at most 8.60e-62 between runs. The final
scripts, preserved scalar evaluator, and receipt hashes agree.

The new conclusions have written analytic proofs and finite exact
certificates where indicated. They have not been formalized in Lean.
Floating-point quadratures use independently evaluated kernels and
Euler--Maclaurin tails; they are diagnostics, not interval certificates.
Release compilation, PDF inspection, visual review, receipt integrity,
and Git publication are recorded separately in VALIDATION.md.
