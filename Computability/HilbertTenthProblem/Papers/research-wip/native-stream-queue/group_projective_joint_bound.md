# One bound for histories and selected outputs

The complete [padded-program compiler](group_projective_padded_program_margin.md)
can use one positive bound instead of two after changing the fixed radix
multiplier from8 to16. This saves **three polynomial operations, one
comparison and one positive witness**, at unchanged certificate cost and
unchanged exact degree. The input remains the ordinary positive integer x.

The wider radix costs the same one multiplication. It supplies enough
room for the sum of all four histories together with all selected outputs.
This is different from deleting the output bound: the joint inequality
restores both original bounds before any typing theorem is invoked.

## 1. The source change

Retain D=u+height_slack, u=alpha*x+beta+1 and origin C0=D-1. Set

    B=16D

in place of B=8D. Every other definition of the padded-program parent
is retained initially; call this the widened parent. The fixed-numeral
condition alpha+beta+1>=m still supplies B>m.

Write

    Hsum=H0+H1+H2+H3,
    Zsum=Zhat0+...+Zhat7,
    Zi=Zhati-1>=0.

The widened parent has two positive witnesses hbound and zbound with

    Hsum+hbound=P,
    Zsum+zbound=P+1.                              (1)

Replace them by the single positive witness b, retaining

    Hsum+Zsum+b=P+1.                              (2)

Use the same name `selection__bound_global` for b and erase
`history_bound`. The existing three additions computing Hsum and seven
computing Zsum remain. The two old final additions become
Hsum+Zsum followed by addition of b. Thus all twelve bound-schedule
additions remain paid, with one fewer comparison. The existing P+1
register is shared from the controller; no new constant offset is free.

The [source](group_projective_joint_bound.py) implements this as
`rewrite(packet)`, so the same change can compose with independent native
kernel rewrites. Its `build` wrapper uses the committed padded-program
parent. It changes no selector, port, controller or native Pell coordinate.

## 2. Restoring both positive bounds before typing

On a positive solution of (2), restore

    hbound=P-Hsum=Zsum+b-1,
    zbound=Hsum+b.                                (3)

Every Zhat is positive, so Zsum>=8 and hbound>=8. Also Hsum>=4, hence
zbound>0. Both equations (1) now hold. In particular P>=12, and the
computed edge repunit J>=0 becomes strictly positive from
P=(B-1)J+1 exactly as in the parent. This applies whether P is supplied
or computed. No dyadic or selection fact is needed to justify (3).

The complete widened-parent theorem therefore applies. Here is the
audit of widening: all original range and packing inequalities require
only B>2D-1 and the stronger transport margin 3D<B. Both hold at16D.
Its independent old history/output bounds still give the same bounds
below P before typing. The joined AND then makes P dyadic, tests
B AND(B-1)=0, and recovers P=B^t with t>=1 from the repunit. Since
B=16D, D is also dyadic. The range mask is still(2D-1)J, so every
history digit is in[0,2D), just as before. Each signed transport
coefficient has absolute value below3D<B. Thus the original controller,
selection and exact history proofs carry through without modification.

For completeness, choose any dyadic D larger than u and larger than
1+the absolute values in the finite accepted trace. Then B=16D and
P=B^t are dyadic, and the same outer histories and genuine selectors
have a full positive native extension at their actual joined scale.
The extra room proves positivity of the joint witness next.

## 3. Positivity of the joint witness on every widened-parent zero

After the widened parent is typed, each of the four history digits is
at most2D-1. At each time cell at most one of the eight physical
selectors is active, so the sum of the eight selected digits is also
at most2D-1. Writing J=1+B+...+B^(t-1), this gives

    Hsum+sum_i Zi <= 5(2D-1)J.                    (4)

The unique new witness from (2) is

    b=P-Hsum-sum_i Zi-7.

Since P=(16D-1)J+1, equation (4) yields

    b >= (6D+4)J-6 > 0.                          (5)

This holds on every positive widened-parent zero, not only a chosen
canonical extension. Erase hbound and replace its zbound by
zbound-Hsum=b. Conversely use (3). These maps are inverse positive
solution bijections with the widened parent at the same x. Its accepted
inputs are those of the original B=8D compiler by the complete trace
theorem and the independent large-D completeness choices. There is no
claim that the two radix conventions have identical supplied tuples.

The output-bound counterexamples cannot survive (2): its restored
zbound is strictly positive. This construction pays for the output
bound through a joint inequality rather than assuming it follows from
the transports.

## 4. Operation counts and exact degree

Keep epsilon=1 for optional controller-mask reuse, which requires m>=8,
and chi=1 for computed P. Set

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, or2m+10 if epsilon=1,
    nu=1+chi.

The new ledgers are

| Computed native fields | Equations | Positive witnesses | Polynomial operations | Exact degree |
|---|---:|---:|---:|---:|
|a,d,k,s|17-chi|m+33-chi|C+50-3chi|12nu L+16|
|a,c,d,k,r,s|15-chi|m+31-chi|C+44-3chi|nu(32L+4m+60)+38|

The certificate's multiplication and addition counts are unchanged.
The SOS loses one residual subtraction, one square and one summation
addition: **one multiplication and two additions**. For the illustrative
ten-letter table with both optional projections, this is258 certificate
operations,299 polynomial operations,14 equations,46 positive witnesses
and degree2974. The numerical universal alphabet remains uninstantiated;
the separate complete75/88 frontier is unchanged.

The new joint residual has degree at mostnu<=2 and does not determine
the SOS degree. With P supplied, the native computed fields that supplied
the parent's highest homogeneous terms are unchanged by the B multiplier.
With P computed, its highest homogeneous term becomes

    P*=16*(alpha*x+height_slack)*sum_e Ehat_e,

in place of the same expression with coefficient8. Substitute this
nonzero degree-two form in the parent's exact leading forms. Their
algebraic main-norm cancellation is independent of this coefficient,
and the resulting highest terms remain nonzero. In the four-field
case the dominating first-norm residual has degree6nu L+8; in the
six-field case the dominating three-unit residual has degree
nu(16L+2m+30)+19. Squaring gives the two exact degrees displayed above.
No equation is used to lower the degree in supplied coordinates.

## 5. Executable evidence

The [receipt](group_projective_joint_bound.json) keeps twenty compact
variant ledgers and one complete source example. Across1,280 assignments,
including320 signed assignments, the checker evaluates both full DAGs
and their entire SOS polynomials. Use the signed extension
hbound=P-Hsum and zbound=Hsum+b: the old history residual vanishes
identically, the old output residual is the new joint residual, and
all other residuals and the complete SOS agree. Four exact weighted
univariate polynomial evaluations cover the two field choices and the
supplied/computed P choices; the general leading-form proof is above.

Eight genuine outer fixtures use the reflected target36 at x=1,u=37
with B=16D. They verify the joint positive witness, independent joined
AND packing, restored positive old bounds, all four transports and
the other outer comparisons. Native Pell coordinates in these finite
fixtures are placeholders; their full positive extensions follow from
the theorem and are not claimed to have been numerically materialized.

Run the source normally to replay the deterministic receipt, or use
`--write` to regenerate it.

The author writer and an independent full proof/source/default review passed.
The independent review checked the widened-radix typing argument, positivity
restoration order, inverse joint slack, all ledgers and the changed leading
coefficient for computed P.
