# Bounded exploration: halving the even-index Pell coordinates

This is an exploratory note, not a new arithmetic-count claim. It concerns
E13 and E18--E20 of the 105-operation certificates. Fixed numerals are free.
Write A for the mathematical main Pell parameter, D=A^2-1, E=A-B, and
F=D-E^2=2AB-B^2-1. The fixed exponent L=2^32 is even.

## A valid transformation of three surrounding equations

The canonical coordinates at the even index satisfy

    kappa=2K, mu=2v+1.

This does not require A even. Modulo2, the recurrence for psi gives
psi_A(t)=t mod2 for every integer A, and chi_A(2t) is odd.
The Pell norm becomes

    v(v+1)=D K^2.

Its cost is four operations, equal to the original norm's cost.

The gap may be weakened to

    c=K+phi, phi>0,

at its original one-operation cost. To prove this sufficient, reconstruct
kappa=2K and mu=2v+1 only mathematically. The norm supplies a positive
Pell index t. Independently, the signed block has already given
c=psi_A(J), with J=2R+1 odd. Hence c is odd and kappa is even, so
kappa cannot equal c. If kappa>c, monotonicity gives

    kappa>=psi_A(J+1)>(2A-1)c>=3c,

contradicting kappa=2K<2c. Thus kappa<c, as required by the source
index lemma. No exact-index conclusion for kappa was assumed here.

The index congruence may become

    K=L/2+Delta0*(A-1), Delta0>0,

at the original two-operation cost. Sufficiency reconstructs the old
Delta as 2Delta0. For necessity, psi_A(L), considered as an integer
polynomial in A, has all coefficients even when L is even. Thus
psi_A(L)/2 is an integer polynomial taking value L/2 at A=1, and

    psi_A(L)-L is divisible by 2(A-1).

Therefore Delta0 is a positive integer at the canonical index. Positivity
follows from psi_A(L)>L for A>1 and L>1. All three transformations are
valid without first assuming A is even, and together retain their
original total cost of seven operations.

## The remaining obstruction is the exponent congruence

The unchanged congruence is

    mu=q+kappa*E+rho*F.

After q=B^L is recovered, q and B are even, while F is odd. The parity
of the norm coordinates therefore makes rho odd. The positive
reparameterization rho=2r-1 covers every positive odd rho, including1.
Its exact transformed congruence is

    v=K*E+r*F+q/2-(F+1)/2.                    (a)

If rho>1 is established for a necessity construction, rho=2r+1 instead
gives

    v+1=K*E+r*F+q/2+(F+1)/2.                  (b)

The v+1 register in (b) is already used by the triangular norm. Neither
formula, however, makes its two half-values free arithmetic operations.

For example, a complete direct realization of (a), using supplied integer
auxiliaries for q/2 and (F+1)/2, costs eleven operations in place of the
old exponent block's seven: compute E,E^2,F,K*E,r*F (five); compute F+1
and impose twice its half-value equal to it (two); impose twice q/2=q
(one); and combine the four signed terms on the right (three). The
half-value constraints are legitimate reversed arithmetic instructions,
but they must be counted. The same-cost norm, gap, and index changes
do not offset these additional operations.

Using (F+1)/2=(B/2)(2A-B) also introduces computations not already
available in the certificate. Merely assigning half-values or changing
the names of positive witnesses does not remove those computations.

No lower bound on all possible implementations is claimed. The valid
three-equation transformation above isolates the only remaining place
where this parity approach might save an operation: a better joint
realization of the final exponent congruence.
