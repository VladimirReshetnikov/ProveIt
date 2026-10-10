# Independent audit of the Mellin–Lerch calculus

Snapshot reviewed: `fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`.
Reviewed main manuscript chapters `07-integration.tex` and `08-differentiation.tex`;
the latter already contains the elementary-symmetric harmonic derivative ladder.

## 1. Formula and safe parameter

Define

    J_N(a,s,z) = integral_0^infinity x^(a-1) Li_s(-zx)/(1+x)^N dx.

For N a positive integer, -1 < Re(a) < N, and z in C minus the nonpositive
real axis, this is jointly holomorphic in a,z and entire in s.
Let E f(s)=f(s-1) and

    P_(N,a)(X) = product_(k=1)^(N-1) (k-a-X).

The identity verified algebraically is

    J_N = -pi/[Gamma(N) sin(pi a)] *
      { z^(N-a) P_(N,a)(E) Phi(z,s,N-a) - P_(N,a)(E) Li_s(z) }.

The apparent poles at a=0,...,N-1 are removable. The Hurwitz/Lerch parameter
N-a has positive real part throughout the integral strip; this avoids
crossing parameter poles while iterating the rational-kernel recurrence.

Proof: integration of d[x^a Li_s(-zx)/(1+x)^N] gives

    J_(N+1) = ((N-a)J_N - J_N(s-1))/N.

Starting from N=1 in the common strip, the first term of the operator product
has P_(N,a)(n+1-a)=(-1)^(N-1)n falling-factorial (N-1). It annihilates the
first N-1 Lerch summands. Shift n by N-1, obtaining the parameter N-a and the
extra power z^(N-1); analytic continuation gives the full strip.

Writing q_j(a)=[X^j] binom(X+a-1,N-1), this is equivalently the article's formula

    J_N = (-1)^N pi csc(pi a) sum_j q_j(a)
      [z^(N-a) Phi(z,s-j,N-a)-Li_(s-j)(z)].

## 2. Integer Mellin rows and logarithmic moments

For 0 <= m <= N-1,

    J_N(m,s,z) = (-1)^(N+m) sum_j q_j(m)
      [(s-j)Li_(s-j+1)(z) - log(z)Li_(s-j)(z)].

More strongly, writing a=m+delta,

    J_N(m+delta,s,z)
      = (-1)^(N+m-1) sum_j q_j(m+delta) J_1(delta,s-j,z).

Indeed the finite correction introduced in shifting N-m-delta to 1-delta
is annihilated since q_(m+delta)(k-delta)=binom(k+m-1,N-1)=0 for
1 <= k <= N-m-1. This yields all integer-a logarithmic moments by
ordinary differentiation of a polynomial times J_1.

Put ell=log z,

    A_r(s,z)=sum_(j=0)^r binom(r,j)(-ell)^(r-j)(s)_j Li_(s+j)(z).

If c_0=1 and c_k=2(1-2^(1-2k))zeta(2k) for k>=1, then

    d_a^h J_1(0,s,z)
      = -h! sum_(k=0)^floor(h/2) c_k A_(h-2k+1)/(h-2k+1)!.

At z=1, A_r=(s)_r zeta(s+r), interpreted by removable continuation.
In particular u*zeta(u+1) has value 1 at u=0, not zero.

## 3. Entire spectral order: a uniform justification

On a compact spectral set choose an integer r with Re(s+r)>0. In the
standard Fermi integral for Li_(s+r)(-zx), apply (x d/dx)^r under the
integral. The differentiated kernel is a rational function of
v=zx exp(-t). For z in a compact subset of C minus the nonpositive real
axis it is bounded by C min(x exp(-t),1). Hence Li_s(-zx)=O(x) at zero
and O((1+log x)^M) at infinity, uniformly on compact spectral/argument
sets. All derivatives in a insert only powers of log x. These uniform
bounds prove local domination on -1<Re(a)<N and justify joint
holomorphy, spectral differentiation, and logarithmic moments.

## 4. Positive-real argument branch cancellation

For z>1, the individual functions z^q Phi(z,u,q) and Li_u(z) have the
same lateral jump 2 pi i (log z)^(u-1)/Gamma(u), up to orientation.
The residues at t=log z in their integral representations are identical.
Consequently the displayed difference has no positive-axis jump.

At z=1 the stronger local identity is

    z^q Phi(z,u,q)-Li_u(z)
      = sum_(k>=0) [zeta(u-k,q)-zeta(u-k)] (log z)^k/k!,
      |log z|<2 pi.

The common Gamma(1-u)(-log z)^(u-1) term cancels. Initially derive this
away from integer spectral resonances; the difference extends to every
u by analytic continuation. Each Hurwitz-zeta difference is entire in u.

## 5. Independent negative-order check

For r>=0 and z=1,

    J_N(a,-r,1) = sum_(k=0)^r (-1)^(k+1) k! S(r+1,k+1)
                                      B(a+k+1,N-a),

where S denotes Stirling numbers of the second kind. This follows from
Li_(-r)(w)=sum k! S(r+1,k+1) [w/(1-w)]^(k+1), followed by the beta integral.
For r>=1 the rational polylog decays at infinity, extending the actual
integral to Re(a)<N+1 after the beta-pole cancellations; this larger
strip is not a common entire-s strip.

## 6. Numerical evidence

`code/verify_mellin_rows.py` performs independent quadrature after x=t/(1-t),
without using Lerch values in the integrand. It tests N=2,3,5, every
integer Mellin row m=0,...,N-1, spectral orders 0,-1,-2, and z=.4 or 2.
Additional rows use complex spectral order .7+.25i. Complete recorded
results and achieved errors are in `results/mellin_rows.json`.
No numerical check is used as a substitute for the analytic proof.

## 7. Optional complementary beta–harmonic family

Not required for the Mellin derivation, and not asserted historically new.
Set e_r(n)=[y^r] product_(k=1)^n(1+y/k). For Re(a)>0, integer p>=2,

    sum_(n>=0) e_r(n)/(n+a)^p
      = (-1)^(p-1+r)/[(p-1)! r!]
           d_a^(p-1) d_b^r B(a,b)|_(b=0),

where the derivative d_a^(p-1) annihilates the 1/b pole before b=0 is
substituted. This supplies a finite gamma/polygamma reduction of the
entire nonalternating height-one harmonic family at arbitrary shifts.
It follows from the binomial series for (1-t)^(b-1), then the beta
integral and p-1 derivatives in a. For instance

    sum H_n/(n+a)^2
      = (psi(a)+gamma)psi'(a) - psi''(a)/2.

This yields sum H_n/(n+1/2)^2=7 zeta(3)-pi^2 log 2.
Direct quadrature independently confirmed the formula at a=1/2 and 1.3
to 39 digits. Literature searches indicate extensive prior beta-function
and shifted Euler-sum work, so this should be described as an organized
classical beta reduction unless a precise prior-art comparison is made.

## 8. Final-manuscript proof audit (sections 02 and 03)

Independently read the complete root-authored `sections/02-mellin.tex` and
`sections/03-jets.tex` in `output/ProveIt_Mellin_Dilation_2026-10-10`.
No mathematical formula error was found. Specifically checked:

- cancellation of the positive-axis Lerch jump, the unit-argument expansion,
  the safe parameter N-a, and continuation to Re(a)>1;
- the operator recurrence and its signs, integer-resonance reduction,
  every displayed logarithmic-moment coefficient, and removable zeta products;
- the coefficient-table determinant, both by the stated finite-difference
  proof and exact rational computation for N=1,...,8;
- the negative-order beta sum and the rational-kernel rescaling factor b^(a-k);
- gamma/polygamma product-rule coefficients, both Stieltjes transforms,
  all listed resonant and third-pole examples;
- the anchored first and repeated primitives, their normalization at a=0,
  and the cancellation of exceptional spectral parameters.

One proof-precision clarification was identified in the delta-germ expansion:
first derive it at |z|<1, then continue the combined coefficient products
at z=1 and spectral resonances. Root reports adding this qualification;
the underlying formulas were correct. No further unresolved analytic gap
was identified in the audited sections. The proof of entire spectral order
uses a valid uniform differentiated-Fermi-kernel bound, not only a pointwise
large-argument asymptotic.

Four additional independent quadratures evaluated the general master
formula at 30-digit working precision, all at s=0.7+0.25i:

| N | a | z | scaled discrepancy |
|---|---|---|---|
| 2 | -0.3+0.15i | 0.4 | 2.5590771e-25 |
| 3 | 1.4+0.2i | 1 | 6.9726112e-32 |
| 5 | 3.2-0.15i | 0.4 | 6.8904164e-32 |
| 5 | 2.6+0.25i | 1 | 8.6336671e-32 |

All passed the declared 1e-22 tolerance. The first case has a stronger
integrable endpoint singularity and correspondingly fewer accurate digits;
the recorded discrepancy is reported rather than rounded down. The other
three explicitly test the region 1<Re(a)<N. Reproducible source and complete
results are `code/verify_mellin_master.py` and `results/general_master_checks.json`.
Together with the earlier integer-row audit, this records 21 numerical
checks. These are consistency evidence; the analytic arguments establish
the formulas.
