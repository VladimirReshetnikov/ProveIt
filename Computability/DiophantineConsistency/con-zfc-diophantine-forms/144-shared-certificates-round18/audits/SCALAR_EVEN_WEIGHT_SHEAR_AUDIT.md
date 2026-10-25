# Independent audit: even radical weights and integral shears

**Accepted for the new weights 8 and 32**, subject to the inherited scalar
calibration and saturation lemmas explicitly retained in
`scalar/source/LINEAR_COFACTOR_ROUND17_PROOF.md`. That complete proof was read
for the sign, nonvanishing, squareclass, auxiliary-integrality, carrier and
constructive-completeness hypotheses. This review concerns the new unbounded
equivalence, not the separate exact degree/cost calculation.

Retain all parent arithmetic abbreviations, including

    delta=Q-1, Da=delta*Cy, Cstar=B*Df*Da,
    Z=S(n+Psi)-Ac,
    pa=delta Z^2, pb=delta S^2 P,
    pc=L^2 S^2 B Df Cy,
    N=(pa+pb-pc)^2-4pa*pb.

Here L is a fixed nonzero even integer. Psi is any integer polynomial in the
other ten coordinates, **independent of n**. The four emitted centers satisfy
this requirement and introduce no new quantified coordinate. Negative L would
give the same polynomial as positive |L|; the actual constants are 8 and 32.
L=0 is excluded, and an arbitrary polynomial that depends on n is not a
bijective shear.

## 1. Unchanged unconditional hypotheses

The parent proof establishes before any squareclass inference that delta is
odd and nonzero; P is nonzero and P=1 modulo4; Ac is nonzero; Da is positive;
and at a zero S is nonzero, hence B is nonzero. These statements involve none
of L, Psi or n. Indeed at S=0 the new norm remains delta^2 Ac^4, nonzero.
Cstar is nonzero; its only possible negative case has c=0, delta=-1 and
Cstar=B. All these claims therefore survive the modification unchanged.

## 2. The even-weight squareclass argument

Factoring the displayed norm over a field containing the square roots gives

    delta*Z/S = +/- L sqrt(Cstar) +/- delta sqrt(P).

The left side is rational. If exactly one radicand is negative, its nonzero
imaginary contribution cannot cancel. If both are negative, the unconditional
description above gives c=0, delta=-1, Cstar=B. Cancellation of imaginary
parts would require L^2 B=P. The left side is zero modulo4, while P is one
modulo4, a contradiction. Thus both radicands are positive.

Write them as alpha^2*d and beta^2*e with d,e positive squarefree integers.
If distinct nontrivial squareclasses occur, their square roots are linearly
independent over Q. If exactly one is nontrivial, its nonzero irrational
contribution cannot disappear. If both have the same nontrivial squareclass,
the coefficient from L*alpha is even. Since P is odd, beta and e are odd,
and delta is odd, so the coefficient from delta*beta is odd. Their signed
sum cannot be zero. Therefore both Cstar and P are integer squares.

This is exactly the role of the original weight two. Every nonzero even
weight has the same force. No requirement that L itself be a square or a
particular power of two is needed.

## 3. Integer reconstruction

The unchanged pairwise-coprimality identities for B,Df,Da and the mod3 sign
argument now give positive integers u,f,e with

    B=u^2, Df=f^2, Da=e^2.

Likewise P=tau^2*g^2 with positive integer tau,g. The parent adjacent-coefficient
denominator descent proves y=e/delta integral (with the separately handled
c=0 case unchanged). Hence the normalized roots are

    Z/S = +/- L*u*f*y +/- tau*g,

all integers. Since n and Psi are integers, this implies S divides Ac.
The carrier divisibility, restored scale, signed-rank argument, and eventual
literal calibrated source restoration are thus identical to the parent.
There is no new division-by-zero or integrality premise.

## 4. Constructive completeness and what is bijective

The parent's canonical construction chooses the outer witness, guard s/g,
one fixed strong Pell pair, cofactor u/r, intersective residue, and supported
interpolated auxiliary data in that order. It supplies Ac/S integral and
the same u,f,y,tau,g above, independently of L and Psi. Set

    n=Ac/S+L*u*f*y+tau*g-Psi.

This is an integer and makes one norm factor zero. Thus every finite
refutation supplies a zero for each new even-weight equation.

For a fixed L, replacing the center Psi by another center Theta is the
literal integer coordinate bijection

    n_new=n_old+Psi-Theta,

with all other coordinates fixed; its inverse exchanges the two centers.
Changing L preserves zero existence through the soundness/completeness
construction. This audit does not assert that changing L is itself the same
coordinate shear or a specified bijection of arbitrary zero sets.

The completed `scalar/PROOF.md` states the stronger equality of the projected
zero sets on the other ten coordinates. This is also accepted: from any new
zero the integral roots and Ac/S allow one to retain those ten coordinates
and set n_old=Ac/S+2ufy+tau*g-(2Delta+1)UV, yielding an actual parent zero.
From any parent zero the same recovered data and the displayed n_new formula
give a new zero with all ten coordinates unchanged. Choosing the plus branch
in both constructions need not recover the original n, which the new proof
explicitly and correctly disclaims.

## Scope and exact-file evidence

The emitted c316/c308/c304 centers use L=8; c300 uses L=32. A separate
dependency scan of all literal circuit nodes verifies that their `shift`
registers do not depend on n and that the only independent coordinates are
the eleven declared inputs. See `SCALAR_SHEAR_DEPENDENCIES.json`.
Exact center cancellation, full attained degree and live binary-operation
counts are separate finite algebra checks, not supplied by this squareclass
argument. No new end-to-end logical kernel certificate, optimality theorem,
or consistency proof is claimed.
