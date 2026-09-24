# The combined-bound tradeoff: 96 operations with 34 witnesses

The system proved in `LINEAR_RADIX_96_PROOF.md` admits the same
96-operation certificate size with 34 positive unknowns and 22
equations. Replace its two positive gap equations

    S2+alpha_old=q^2,    ell+alpha2=q,
    S2=ell+e*q,

by the single positive gap equation

    ell+e+alpha=q.                            (1)

Every other equation, the fixed index, and every other positive
unknown is retained. Equation (1) takes two additions, exactly as
the two former gap equations did. The number of multiplications
remains 52 and the number of additions remains 44. This is a
witness/equation tradeoff at the same certificate size, not a new
operation-count reduction.

## Sufficiency and preliminary bounds

Positivity in (1) gives ell,e<q. More precisely,

    ell <= q-e-1,    e <= q-2,
    S2=ell+e*q <= (e+1)(q-1) <= (q-1)^2 < q^2.

Thus all preliminary coding bounds in the 96-operation proof still
hold. In particular, the two positive equations

    Omega=lambda-e,
    sigma=Omega*(q-C^2)

give C^2<q and sigma<q^3. The packed S and Tplus are positive and
less than q^7<n=q^8 by exactly the same estimates as before. No
Pell conclusion, coordinate bound, or canonical-code claim is used
to obtain these initial inequalities.

Equivalently, define the two old witnesses explicitly:

    alpha_old=ell*(q-1)+alpha*q>0,
    alpha2=e+alpha>0.

They are positive integers and restore the complete original
96-operation system while preserving every other witness. Its full
noncircular Pell, code, unit, and circuit-decoding proof therefore
applies. This establishes sufficiency directly, and not merely an
arithmetic resemblance between the two schedules.

These maps also have exact polynomial identities. Writing
`F=ell+e+alpha-q`, the old first residual after substitution is q*F,
and the removed last residual becomes F. All other old residuals
are unchanged. The primitive checker verifies these identities in
addition to its complete comparison of the new source equations.

## Necessity and the reverse witness map

For the canonical codes of the linear-radix proof, ell_0(T) has
coefficients zero or one, and e_0(T) has coefficients zero, one or
two. Both have degree less than K. Since B>64, adding the two
evaluations has no base-B carry: all resulting digits are at most
three. Consequently

    ell_0(B)+e_0(B)<B^K<B^L=q.

The final strict inequality follows from L>3K+2. Thus

    alpha=q-ell_0(B)-e_0(B)>0

is a positive integer. The canonical coding construction and all
subsequent positive Pell witnesses in `LINEAR_RADIX_96_PROOF.md`
are unchanged. This proves necessity for exactly the same fixed
index, without increasing H or L and without rechoosing any Pell
coordinate solely because of the combined bound.

There is also a reverse map from every positive solution of the
old 96-operation system. That system's proved sufficiency gives
q=B^L, ell=ell_0(B), and e=e_0(B), before decoding the represented
circuit. The displayed digit bound then proves (1) with the new
positive alpha. This map uses a proved consequence of the old
system; the converse map above used only elementary inequalities.
There is no circular use of the changed bound.

## Exact arithmetic change

Keep the already required registers e*q and S2=ell+e*q. Replace

    L1=S2+alpha_old,
    indicator_bound=ell+alpha2

and their two equality tests against q^2 and q by

    bound_sum=ell+e,
    L1=bound_sum+alpha

and the single equality test L1=q. These are two additions on each
side. Remove the unused positive unknown alpha2; the old alpha
position now holds the new positive gap. All other primitive
instructions and source residuals are unchanged. The independent
checker is `../verification/round31_1980_combined_bound_certificate.py`.

The result has 96 operations, 34 positive unknowns and 22 equations.
As throughout this project, fixed numerals and equality tests are
free, and the count is an upper bound rather than an optimality claim.
