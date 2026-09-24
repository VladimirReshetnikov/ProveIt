# Share the ratio product with the first Pell norm: 104 operations

The unit-scale construction in `PELL_UNIT_SCALE_PROOF.md` has an
equivalent certificate of 104 operations: 57 multiplications and
47 additions, with the same 34 positive unknowns and 22 equality
tests. The fixed index and all numerals have exactly their previous
status. The executable checker is
`../verification/round19_1980_shared_ratio_product_certificate.py`;
its JSON contains the full primitive and source-residual receipts.

Only the first Pell index equation changes as a polynomial in the
supplied unknowns. Its norm is evaluated by a different factorization,
sharing an already required interval product. Both positive witness
maps are established below; no changed approximation or encoding
theorem is assumed without justification.

## The changed index modulus

Keep the unit-scale notation

    N=n, R=r, U=wN^2, Y=sN^2,
    a0=Y(U+1), A=a0+4,
    D=UY, Q=UY^2=DY, P=2Q+1,
    J=2R+1, K=k, C=c.

Here D is the existing calculated register `UM`; neither D, Q nor P
is an additional supplied witness. Replace

    K=R+1+h_old Q

by

    K=R+1+h D, h>0.                             (1)

Retain exactly the same triangular norm and positive interval:

    tau(tau+1)=Q(Q+1)K^2,
    C=KY+eta, K=eta+zeta, eta,zeta>0.             (2)

The old modulus was larger than the new one by the factor Y. This
weakening still gives the exact first Pell index, as follows.

## Exact index and equivalence over positive witnesses

The coding bootstrap used in `PELL_UNIT_SCALE_PROOF.md` gives, before
any exponent relation or Pell approximation is invoked,

    N>=64, N<=R<2N^3, U,Y>=N^2,
    D=UY>=N^4>2N^3+1>R+1,
    A>J.

The new equation (1) gives `K>=R+2`, so the interval in (2) gives
`C>YK>J`. Thus the unchanged signed Pell block again proves

    C=psi_A(J), d=chi_A(J).

Set `T=2tau+1`. The norm in (2) is the ordinary positive Pell equation
for parameter `P=2Q+1`, and therefore

    K=psi_P(t), T=chi_P(t)

for a positive index t. Since `P-1=2Q=2DY` is divisible by D,
the elementary congruence `psi_P(t)=t modulo(P-1)` implies
`K=t modulo D`. Equation (1) and `0<R+1<D` now give

    t=R+1+vD, v>=0.

If v is positive, then `D>R` and Pell growth give

    C/K <= (2A)^(2R)/(2P-1)^(R+D)
         <= (2A/(2P-1))^(2R) < 1/2.

The last comparison uses the same unit-scale estimate

    (2P-1)-4A=4Y[U(Y-1)-1]-15>0.

This contradicts `C/K>Y`. Consequently

    K=psi_P(R+1), T=chi_P(R+1).                  (3)

No exponent relation or rounded binomial value was used in this
argument. In particular, the hypotheses of the unchanged later
unit-scale proof have been recovered noncircularly.

There are direct positive witness maps to the predecessor system.
Given its solution, define

    h=Y h_old.

Then `hD=h_old Q`, so (1) holds and h is a positive integer. Every
other witness is preserved. Conversely, (3) and the stronger Pell
congruence modulo `2Q` make

    h_old=(K-R-1)/Q

an integer. It is positive because `psi_P(R+1)>R+1`. It restores
the predecessor index equation, preserving every other witness.
Equivalently, the new h is a positive multiple of Y and the reverse
map is `h_old=h/Y`. Thus the two systems are exactly equivalent
over their declared positive domains. All exponent, rounding,
encoding, and remaining positivity conclusions can now be taken
from the restored unit-scale system.

## The shared norm identity and exact count

The unit-scale certificate already computes

    D=UY

for `a0=D+Y`, and it already computes

    H_ratio=YK

for the positive interval `C=H_ratio+eta`. The polynomial identity

    Q(Q+1)K^2
      =(UY^2)(UY^2+1)K^2
      =[(UY)^2+U](YK)^2
      =(D^2+U)H_ratio^2                         (4)

allows both products to be shared. Move the existing computation
of `H_ratio` before the norm. The former five instructions

    Q=D*Y,
    Qplus1=Q+1,
    QQplus1=Q*Qplus1,
    K2=K*K,
    norm_left=QQplus1*K2

are replaced by four:

    D2=D*D,
    coefficient=D2+U,
    ratio2=H_ratio*H_ratio,
    norm_left=coefficient*ratio2.

Both lists have one addition; the second has three multiplications
instead of four. The computation of `H_ratio` is moved, not copied.
The root-side instructions `tauplus1=tau+1` and
`norm_right=tau*tauplus1` remain unchanged.

The old index product `h_old Q` is replaced by `hD` at the same cost.
Consequently no remaining instruction or equality needs the computed
value Q, and its instruction can actually disappear from the global
schedule. The mathematical parameter Q in the proof is just the
displayed polynomial, not an uncharged arithmetic register.

The total is therefore 104 operations, with 57 multiplications and
47 additions. The checker verifies (4), the exact positive-witness
polynomial identity for `h=Y h_old`, every source residual and
serialized primitive, and the absence of the discarded Q registers.
It explicitly checks that only E11 changed as a source polynomial.
