# A same-cost half-parameter kernel for odd mask indices

This is a conditional extension of the retained Pell kernel, not a
reduction below the proved 90-operation universal certificate or the
81-operation finite-history component. It removes a parity obstacle
for possible alternative masks. It is not substituted into round42,
whose canonical packed index r is even.

The arithmetic comparison below uses the historical round42 schedule
of 82 operations. The direct-length round43 subsequently removes one
multiplication independently of these auxiliary signs; no improvement
to that 81-operation count is asserted here.

Use the published notation A=a+2, D=A^2-1, J=2r+1 and retain

    R=i*c^2, K=R^2=D*(f^2-1),
    K*(u^2-y^2)=1-y^2.

Replace just the two constructions of u by

    u=j*c-J,
    u=o*f-c.                                      (1)

The original even-r version used u=J+j*c=c+o*f. The two products,
two additions/subtractions, and five norm operations are unchanged
in number. The retained kernel still costs 43 operations. Applied
formally to the full round42 arithmetic list, it still costs
82=45 multiplications+37 additions/subtractions.

## Sufficiency is unchanged, including potentially negative u

The independent main and auxiliary arguments first give
c=psi_A(p), f=chi_A(m), c|m, 0<2p<=m, c>J>1 and R>1,
exactly as in `HALF_PARAMETER_PELL_92_PROOF.md`. They do not use
either version of the equations for u.

The norm is (Ru)^2-(R^2-1)y^2=1. Here u is an integer register,
not a supplied positive unknown. It can be negative in a putative
solution of (1). It cannot be zero. Pell classification gives an
odd s=2h+1 and a sign epsilon such that

    u=epsilon*Q_h(R^2),
    chi_X(2h+1)=X*Q_h(X^2).

The same integer-polynomial identities as the published proof give

    Q_h(1-A^2)=(-1)^h*psi_A(s),
    Q_h(0)=(-1)^h*s.

Modulo f, equation (1) now gives
epsilon*(-1)^h*psi_A(s)=-c. Squaring it and using the chi doubling
identity still yields chi_A(2s)=chi_A(2p) modulo chi_A(m).
The unchanged step-down proof gives s=+/-p modulo c. Modulo c,
the other equality in (1) gives epsilon*(-1)^h*s=-J. Hence again
J=+/-p modulo c. The bounds 0<J,p<c and parity of psi_A(p)
exclude J+p=c and prove p=J. All subsequent first-index, exponential
and binomial arguments are unchanged.

## Positive necessity when r is odd

Let r be odd, so J=3 modulo 4. Starting with the canonical main
pair c=psi_A(J), d=chi_A(J), choose

    m=2cJ, f=chi_A(m), R=D*psi_A(m), i=R/c^2,
    y=psi_R(J), u=chi_R(J)/R.

The existing addition identities make i and u positive integers.
The two polynomial congruences now have negative signs:

    u=-J modulo c,
    u=-psi_A(J)=-c modulo f.

Therefore j=(u+J)/c and o=(u+c)/f are positive integers satisfying
(1). The norm is automatic. As in the published proof, R>A and
Pell growth give u>c>J; this also makes positivity explicit.
All other canonical first-Pell witnesses are available without
any assumption that r is even. Thus the modified kernel supplies
the odd-r branch at the same arithmetic cost.

## What this does and does not save

The usual periodic mask M=2(L-1)/3 tests digits zero or one, with
r=P modulo two. The complementary mask M=(L-1)/3 tests digits
zero or two; its canonical P is even and its corresponding r is
odd. The variant above removes that parity obstruction.

However, the direct conversion P -> 2P costs one multiplication
and merely replaces the multiplication used for 2lambda. It ties
the original total. A saving would require a compiler that supplies
the doubled-digit words natively, including its row-marker and raw
input interfaces, without spending that operation elsewhere.

`../verification/explore_odd_index_pell_signs.py` checks all 20
modified source residuals and the unchanged 82-operation count.
It also constructs exact positive auxiliary witnesses for five
small odd-r examples, including J=7. These examples check only
the auxiliary construction, not the full large-index bootstrap
or a universal machine history.
