# Bounded search around E18--E20

This note records exact accounting for several transformations of the
112-operation certificate. It proposes no smaller certificate and does
not modify the frozen arithmetic or positive-domain proofs.

Use A=a^2-1, u=a-B, D=A-u^2, K=kappa, and M=mu. The current equations are

    M=q+u*K+rho*D,
    M^2=A*K^2+1,
    K=L+Delta*(a-1).

With A and a-1 already available elsewhere, these blocks cost 7, 4,
and 2 arithmetic instructions, respectively. This includes computing
u and D. All comparisons are free equality tests.

## Shifting the first coordinate

The positive coordinate V=M-u*K is the most direct candidate. It
reduces the congruence to V=q+rho*D, saving two instructions. Computing
M=V+u*K for its norm adds those same two instructions. Expanding the
norm directly instead gives

    V^2+2*u*K*V-D*K^2=1,

which has more arithmetic than reconstructing M. The cheaper congruence
alone is therefore not a saving for the joint block.

The preceding Pell denominator T=a*K-M is positive for the intended
index L>1. It changes the congruence and norm to

    B*K=q+T+rho*D,
    T*(2*a*K-T)=K^2-1.

The congruence costs the same as before, and the second equation costs
six operations in this representation, versus four for the existing
norm. Selecting an adjacent Pell index also needs a separate argument
for the upper-index bound; it is not an automatic witness substitution
for every other Pell equation.

Writing M=V+1 or M=V-1 preserves a four-operation norm through
V*(V+2)=A*K^2 or V*(V-2)=A*K^2. However, it introduces q-1 or q+1
in the congruence. Neither is available in the present certificate.
The existing q^2 and the geometric equation do not make these affine
values available without an additional instruction.

## An alternative index modulus

The final congruence may use a+1 instead of a-1 without changing its
count:

    K=L+Delta_plus*(a+1).

Here L=5^16 is odd. For every nonnegative t, the elementary recurrence
gives psi_a(t)=(-1)^(t-1)*t modulo a+1 (with t=0 interpreted directly).
The norm and 0<K<c=psi_a(J) give K=psi_a(t), 0<t<J. The established
growth bounds give J+L<a+1. Consequently the new congruence implies
t=L: for odd t, both t and L lie in [0,a+1), while for even t the only
possible equality would be t+L=a+1, excluded by the strict size bound.
Conversely psi_a(L)-L is a positive multiple of a+1, so Delta_plus is
positive for the intended solution.

This alternative permits the natural computed coordinate a+1 when
one perturbs a from M0*(U+1) to M0*(U+1)-1, where M0=r*s*n^2.
Its factored norm coefficient costs one operation less, but a-B then
costs one more. Shifting the first coordinate by +/-K moves this extra
addition between the congruence, its modulus, and the norm; it does
not remove it from the joint computation.

## A useful exact factorization with no saving here

The modulus has the identity

    D=2*a*B-B^2-1
     =(B-1)*(2*a-B-1)+2*(a-1).

The factors B-1 and 2*a-B-1 are not both available. Even though a-1
is shared, forming them and adding 2*(a-1) costs more than the current
two instructions u^2 and A-u^2 after u is known. This identity should
not be assigned a lower count by treating its affine factors as free.

These are failures of specific constructions, not arithmetic-circuit
lower bounds or evidence of global optimality.
