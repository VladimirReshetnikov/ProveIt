# Shared positive projections give a 102-operation polynomial

The fixed complete75 compiler has a single-polynomial representation with
**20 positive witnesses**, exact degree84, and evaluation cost
**102=50M+52A**. Its arithmetic certificate costs **76=41M+35A** with
nine equations. This improves the
[105-operation polynomial](complete75_bounded_packing_elimination105.md)
by replacing the input Pell-index gap with a positive decomposition of
the main projection quotient. The best comparison-certificate bound
remains75; no optimality, publication, or formalization claim is made.

Applying only the same quotient decomposition to the original bound gives
a useful second choice: a **75-operation certificate with21 positive
witnesses and10 equations**, and a **104-operation polynomial of degree84**.
It retains the best certificate operation count while reducing the
positive-elimination source's witness and equation counts by one each.

## 1. Exact change and witness domain

Keep the105 construction's strengthened raw bound and computed packed R:

    C+F+alpha+2d*x=q,
    R=(q^2-Z-qF)(q^2-1)+(MC+q*(MF+B-1))*J.

Keep its positive definitions of q,C,k,a,c,kappa and both Pell roots.
Replace the supplied main quotient gamma by

    gamma=rho+sigma, sigma>0,

and delete the input gap equation `c=kappa+phi` and its positive witness
phi. The root definitions are now

    D=X+ac+(rho+sigma)H,
    mu=W+a*kappa+rho*H,

where `A=a+2`, `H=4a+3`, `Delta=A^2-1`, and
`kappa=2d*x+b+delta*Delta`. Both roots remain positive polynomial
expressions on every positive retained assignment. This choice of which
quotient to retain is what permits both root eliminations to survive.

The20 supplied positive coordinates are

    J,F,alpha,z,f,h,i,j,o,s,w,tau,eta,zeta,y,Z,W,delta,rho,sigma.

The nine residuals are exactly those in the105 note with its input gap
residual omitted and `gamma=rho+sigma` substituted everywhere. The final
polynomial is their sum of squares. No additional comparison is implicit.

## 2. Soundness restores the omitted positive gap

Take any positive retained assignment where this polynomial vanishes.
The105 proof restores R>0 from the retained raw bound and restores
`alpha_old=alpha+F>0`. Every outer equation and all ten strong
half-binomial kernel equations hold, independently of the missing input
gap. Thus the established kernel theorem gives

    X=2^R, c=psi_A(R), D=chi_A(R), X>q>W.

The retained input norm, positive kappa, and positive root mu give
`kappa=psi_A(v), mu=chi_A(v)` for an integer v>=1. Put

    E_A(j)=chi_A(j)-a*psi_A(j).

This sequence is strictly increasing for j>=0: it has initial values
1,2 and recurrence `E_A(j+1)=2A E_A(j)-E_A(j-1)`. Since A>=2,
positivity of each successive difference follows inductively from

    E_A(j+1)-E_A(j)
      =(2A-2)E_A(j)+(E_A(j)-E_A(j-1))>0.

The two retained projection identities imply

    E_A(v)=W+rho*H
          <X+(rho+sigma)*H=E_A(R).

Hence v<R. Strict growth of the Pell psi sequence now gives
`phi=c-kappa>0`. This restores precisely the deleted input gap, with
the positive main quotient `gamma=rho+sigma`. All original complete75
equations have positive witnesses, so its universal soundness theorem
applies. No input-index decoding was assumed to recover the gap.

The computed phi need not be positive on arbitrary retained assignments;
its positivity is proved only after all nine residuals vanish. Likewise
the computed R uses the retained raw bound. These are conditional positive
definitions, not unrestricted positive substitutions.

## 3. Completeness has a strictly positive sigma

Choose the canonical complete75 witnesses with the stronger raw slack
proved in the105 note. The original input theorem gives the exact odd
index `u=2d*x+b>=3`, with u<R. Since R is also odd, R>=u+2.
The original main and input projections give

    H*(gamma-rho)=E_A(R)-E_A(u)-X+W.                    (1)

For every positive index j,

    psi_A(j)<E_A(j)=2psi_A(j)-psi_A(j-1)<=2psi_A(j).

For u>=1 the recurrence and `psi_A(u-1)<psi_A(u)` give

    psi_A(u+2)-2psi_A(u)
      >(4A^2-2A-3)*psi_A(u)>A,                         (2)

since A>=2. Therefore R>=u+2 implies

    E_A(R)-E_A(u)>psi_A(u+2)-2psi_A(u)>A>X.

Equation(1) proves that `sigma=gamma-rho` is a strictly positive
integer. Set this new witness, discard gamma and phi, and retain every
other coordinate. Both root definitions recover their original values,
and all nine equations hold. Thus every accepted ordinary input has
positive witnesses for the new polynomial, using unchanged fixed
compiler numerals and the actual packed index.

The quotient inequality actually holds for every complete75 solution;
only the stronger raw bound restricts completeness to the canonical
subfamily. No astronomically large auxiliary coordinate is borrowed
from a different kernel tuple.

## 4. Exact circuit and degree

In the105 certificate, remove the one addition `pell_gap=kappa+phi`.
Before the existing product `gam=gamma*H`, insert
`gamma_sum=rho+sigma`, and use this sum as its first operand. This adds
one addition and removes one, so the certificate still has76 operations.
Its gap comparison disappears and no new comparison replaces the gamma
definition. Twenty positive witnesses and nine comparisons remain.

Nine subtraction gates, nine squares and eight sums give the single
polynomial evaluation cost

    76+9+9+8=102=50M+52A.

The new gamma has degree one, just as before. Removing the gap residual
of degree17 leaves residual degree bounds

    1,5,26,9,22,22,34,6,42.

The input norm and its unique degree42 part are unchanged. Consequently
the highest-degree part of the final polynomial remains

    16*(B-1)^60*delta^4*w^10*s^10*J^60,

so its degree is exactly84 for every fixed admissible B>1. Compiler
numerals have degree zero; the input and20 positive witnesses have degree
one. There are no residual variables or unchecked equality gates.

## 5. The 75-operation alternative with21 witnesses

Apply `gamma=rho+sigma` and delete `c=kappa+phi` directly in the
[107-operation positive-elimination source](complete75_positive_elimination.md),
without adding F to the raw bound and without eliminating its positive
packed-index witness R. The two one-addition changes cancel exactly.
This leaves **75=41M+34A operations**, **21 positive witnesses**, and
**ten equations**. Its sum-of-squares polynomial costs

    75+10+10+9=104=51M+53A,

with exact degree84. Its witness list is the20-coordinate list in Section1
with R added. The original `C+alpha+2d*x=q` bound is retained, and alpha
requires no change when restoring the old source.

The same soundness argument in Section2 restores phi>0; here R is already
a supplied positive coordinate. Section3 proves sigma>0 for every old
complete75 solution, so this alternative does not require the105 bound
or its canonical-subfamily restriction. Projection and restoration give
a bijection of positive solution sets with the original75 source after
the earlier eight definitions.

| Construction | Certificate operations | Positive witnesses | Equations | Single-polynomial operations | Degree |
|---|---:|---:|---:|---:|---:|
| Original positive elimination |75|22|11|107|84|
| Gamma dominance with original bound |75|21|10|104|84|
| Gamma dominance with stronger bound |76|20|9|102|84|

Neither of the last two rows dominates the other in every measure.

## 6. Evidence and scope

The [checker](complete75_gamma_dominance_elimination102.py) records
the entire102-gate DAG and exact operation histogram. It checks local
rewiring and register availability, and independently replays the old
nineteen-equation source on256 arbitrary assignments after restoring
gamma, phi, R and the old bound slack. The restored phi and R may be
signed in these algebraic identity tests; the soundness argument above
supplies their positivity on the full zero set.

Separate exact Pell fixtures verify positive gamma-rho, the restored
gap, both norms and projections, and the two-step growth inequality.
They are main/input interface fixtures, not full compiler or binomial
tuples. The actual sparse compiler bound checks are replayed from105.
The degree fixture verifies84 and its asserted leading coefficient.
The75-operation alternative has its own literal104-gate schedule,
128 old-source identity replays and a separate degree fixture in the same
checker and receipt.
The parametric proofs establish universality; the finite and symbolic
checks corroborate the implementation. Independent proof/source review and
default replay passed for both102 and104. Additional independent checks
covered364 integer-norm projection pairs and600 matrix-powered dominance
pairs; these finite checks corroborate the parametric growth proof.

From the repository root, with the pinned verification dependencies installed:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_gamma_dominance_elimination102.py
