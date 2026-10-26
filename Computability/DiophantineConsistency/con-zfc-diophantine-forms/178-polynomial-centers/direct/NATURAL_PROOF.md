# Three fewer natural coordinates through natural restoration on the zero set

## Statement and source

The source is package 164's literal natural206/equation.json at ProveIt commit
fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb. It has 206 independently nonnegative
integer variables and 158 quadratic residuals. The target natural203 has 203
independently nonnegative integer variables and 155 quadratic residuals. Its
single quartic is the sum of the squares of those 155 explicitly supplied
residuals. The intermediate natural204 is also retained.

The source's ordinary arithmetic/C222/ZF/ZFC calibration implies, within ZFC,
that its having a natural zero is equivalent to existence of a finite ZFC
refutation. We prove the same zero-existence equivalence for the targets.
The first two coordinate projections are complete for the canonical CRT
witnesses used to establish the source theorem. They are **not** claimed to
give a bijection from every source natural zero. The third projection gives a
bijection on all natural zero sets to which it is applied. The final optional
integer row operations give a pointwise equality of zero sets on unchanged
coordinates. No assertion of consistency or of global optimality is made.

## A general exact algebraic projection

Let q_1,...,q_m be integer quadratic polynomials in n coordinates. Let v be an
integer vector in the common kernel of their homogeneous quadratic Hessians,
and suppose v_p=1. In coordinates x=y+v*z with y_p=0, each q_i has the form

    q_i(y+v*z) = q_i(y) + a_i*z,

where a_i is an integer constant. If a_r is 1 or -1, solving the r-th row gives
z=-a_r*q_r(y). The remaining rows are the quadratic polynomials

    q_i(y) - a_r*a_i*q_r(y) = 0,    i != r.

Restriction y_i=x_i-v_i*x_p and the displayed restoration are inverse maps
between the complete integer zero sets. This algebraic statement alone does
not preserve a natural domain. Its natural-domain obligations are addressed
separately below. The independent checker constructs the projected rows by
this row-combination identity; the constructor uses shear and substitution.

## First projection: the modus-ponens product difference

Write A=mul.363, B=mul.369 and retain all other source coordinates. Put

    P=(Sp+1)(1+mul.361),
    Y=B-A.

The source's row basis.R062 is exactly A-P=0. The direction with entries 1
at A,B and zero elsewhere is a common Hessian-kernel direction. Delete A
and replace B by Y. The inverse is A=P and B=Y+P.

For every natural target zero, P>=0, so both restored coordinates are
nonnegative and every source residual vanishes. This establishes soundness
pointwise. For completeness, use the source164 canonical CRT representatives.
Section 3.2 of its natural/PROOF.md chooses the a representative sufficiently
large after choosing b and Sp, so that

    mul.368 > mul.363,
    mul.369=(1+mul.366)*mul.368 > mul.363.

Thus Y is nonnegative on every canonical witness supplied by that proof.
No strengthened representative choice or altered CRT modulus is required.

## Second projection: the generalization product difference

Write C=mul.372, D=mul.373. Put

    P2=(S+1)(1+mul.361),
    Z=C-D.

The source row basis.R069 is D-P2=0. The direction with entries 1 at C,D is
in the common Hessian kernel. Delete D, retain Z in the position formerly
occupied by C, and restore D=P2 and C=Z+P2.

Again every natural target zero restores nonnegative old coordinates. For
completeness, section 3.3 of the same source proof has Sp>S and

    mul.370-mul.361=F*(5+3*b+2*mul.36)>0.

It follows that C=(Sp+1)(1+mul.370) exceeds
D=(S+1)(1+mul.361). Hence Z>=0 on those same canonical witnesses. Both
projections use the exact same witness selection, and neither modifies any
original semantic coordinate or power request. They can therefore be composed.
The result is natural204, with 204 variables and 156 quadratic rows.

## Third projection: use a retained equation to recover nonnegativity

This step applies after the first two. Let

    U=mul.299, V=mul.304, T=add.302.

The literal defining rows are U=P3 and V=T*(T+1), where P3 is the following
polynomial with nonnegative coefficients, writing r=mul.232, s=mul.237,
t=mul.243:

    P3 = 4556 + 4320*r + 1024*r^2 + 512*r*s + 128*r*t
         + 1080*s + 64*s^2 + 32*s*t + 270*t + 4*t^2.

The vector with entries 1 at U and -4 at V is in the common Hessian kernel.
Set W=V+4U, delete U using U=P3, and restore

    U=P3,    V=W-4P3.

The expression for V has negative coefficients; coefficientwise positivity
would not justify this projection. However the retained V-definition becomes

    W-4P3-T*(T+1)=0.

Every target natural zero therefore restores V=T*(T+1)>=0. All other
coordinates remain nonnegative, U=P3>=0, and the exact algebraic inverse
restores every old row. Conversely every natural source zero has W=V+4U>=0.
Thus this third step is a pointwise natural zero-set bijection.

The difference from a polynomial-wide nonnegativity recognizer matters:
natural restoration only needs to hold on the target zero set. Here a retained
quadratic row supplies the necessary proof. The checker verifies its complete
coefficient array, including that T is a retained natural coordinate.

## Equation and verification scope

The target is P203=sum(q_i^2), i=1,...,155, using the complete coefficient
arrays in natural203/equation.json. Its collected expansion is supplied
separately and is recomputed independently. The inherited defining source,
every projection direction, every quadratic restoration, and every projected
row are literal data. The optional natural203_reduced performs only invertible
integer row operations; their inverses are checked in reverse order.

verify_direct.py verifies exact coefficient identities and the natural-domain
restoration conditions above. It does not compute a ZFC refutation or assume
one exists. The canonical CRT theorem and the retained logical calibration
are unbounded ordinary mathematical proofs, not consequences of finite tests.

Composing them gives

    ZFC |- (there is no x in N^203 with P203(x)=0) <-> Con(ZFC).

The result is a new reduction relative to the pinned inspected source.
Common-Hessian projection itself is inherited from packages159/163, and the
two canonical signs are inherited from164. We make no worldwide priority
claim for the projection method or natural-domain reasoning.
