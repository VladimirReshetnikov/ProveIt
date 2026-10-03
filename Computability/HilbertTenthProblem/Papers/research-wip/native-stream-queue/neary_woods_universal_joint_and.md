# One native AND for the complete recoder and four-tile history

The two prescribed-scale AND components in the raw
[population377 compiler](neary_woods_universal_population377.md) can be
replaced by one complete native AND. The new raw certificate costs
**246=118M+128A operations**, with **37 comparisons** and **64 positive
existential witnesses**. Its sum-of-squares polynomial costs
**356=155M+201A operations**, of total degree **at most580** including
the four positive program parameters and ordinary positive input.

The [source](neary_woods_universal_joint_and.py) and
[receipt](neary_woods_universal_joint_and.json) retain the exact fixed
U9 program, loader, recoder and selected-history outer equations. The
change concatenates their two AND relations and pays a new lower-output
bound. Equivalence is a projection onto the common outer coordinates:
the native auxiliaries are rebuilt by the complete AND theorem in both
directions. This is not an identity between the old and new polynomials
away from their zeros, or a bijection of their complete witness tuples.
The separate established75-operation certificate and87-operation
universal-polynomial bounds are unchanged.

## 1. The two scalar AND relations

Use q,Q,B,P,J,K for the recoder quantities, and ell for its positive
input duration. In the actual source J is the computed `duration_J`,
and Ahat is the computed `projected_Ahat`. The retained equations and
definitions include

    q=x+input_slack,       Q=q+z+power_gap,
    B=2^(D-1)*Q,          P=(B-1)*J+1,
    S=q*P,                S=(2B-1)*K+1,
    J=(B-1)*duration_quotient+ell,
    ell+duration_slack=B-1.                            (1)

D is the same fixed data width as in the parent, in particular D>=3.
The default computes ell=program_E+program_duration_gap; the optional
fifth program parameter gives the separate duration-bound interface.
All supplied coordinates are strictly positive. Before any equation,
Q>=3, B>1 and J>0. The computed output hat is

    Ahat=(Q-1)*(quotient_hat-1)+z+1>=2.                 (2)

The old recoder AND uses scale L=B*S and unpadded words

    Hr=B*x*J+ell,     Mr=B*K+ell-1,
    Zr=B*(Ahat-1).                                    (3)

Its literal ports are16Hr+12,16Mr+10,16Zr+8; the old native q
register is16L. None of the proof notation L,Hr,Mr,Zr is an added
arithmetic instruction.

For the selected history, write Ph for its packed scale parameter,
and Hh,Mh,Zh for its unpadded joined words. Its AND scale is

    Th=Ph^11.                                         (4)

These are the unchanged expressions from the
[slope-class construction](pcp_affine_slope_class_history.md), with
four tile selectors and three selected-product lanes. The
[shared arithmetic](neary_woods_universal_shared_history382.md) computes
the same expressions using154 history gates. There are three selected
lanes, four controller lanes, two range lanes and two reserved top lanes.

Crucially, Hh,Mh,Zh are nonnegative on every positive supplied tuple,
without any native equation. Each selector is Shat_i-1>=0, every
selected output is Zhat_i-1>=0, and their packed sums are nonnegative.
The history height is a sum of positive coordinates, its radix is a
positive fixed multiple of that height, Jh=sum_i(Shat_i-1)>=0, and
Ph=(Bh-1)Jh+1>=1. The range mask (height-1)Jh and all top-region
terms are also nonnegative. The computed initial history value remains
the positive loader output. Neither one-hot selection nor canonical
digits have been assumed here.

## 2. A paid lower-output bound and the joint predicate

Add one positive witness beta and the comparison

    Ahat+beta=S.                                      (5)

S is already paid, so this uses exactly one addition and one comparison.
Now apply one [complete prescribed-scale AND64](native_binary_masked_selection63.md)
to

    Scale=L*Th,
    H=Hr+L*Hh,   M=Mr+L*Mh,   Z=Zr+L*Zh.             (6)

The literal circuit folds the padding into the existing low ports. Let
q0 denote the old16L register and Apad,Bpad,F3low the old padded
ports. Rename their definition sites and compute

    qnew=q0*Th,
    Anew=Apad+q0*Hh,
    Bnew=Bpad+q0*Mh,
    F3new=F3low+q0*Zh.                                (7)

These seven gates cost4M+3A. They give exactly16Scale,
16H+12,16M+10,16Z+8. The full surviving native source consumes the
new registers under its original names. Its F0,F1,F2 and nineteen
other positive auxiliaries are fresh witnesses for this larger AND.
All its norm, ratio, index, checksum, input-port and positivity
requirements are retained. In particular F3new>=8 before any equation.

No unscaled concatenation, extra multiplication by16, or evaluation
of an enormous fixed numeral is omitted from the ledger. Equations
(3) and(6) are the mathematical interpretation of the folded source(7).

## 3. Soundness and the order of typing

At a zero of the new raw certificate, positivity and(1) give

    q>=2, B>1, 0<ell<B,
    0<J<P, 0<x<q, 0<K<S.

Thus xJ<S. Since these are integers,

    0<=Hr<=B*(S-1)+(B-1)<L,
    0<=Mr<=B*(S-1)+(B-2)<L.                           (8)

Equation(5), positive beta and Ahat>=1 give

    0<=Zr=B*(Ahat-1)<L.                               (9)

The words in(6) are nonnegative before native typing. The complete
AND theorem therefore yields Scale dyadic, H,M<Scale, and H AND M=Z.
Because L and Th are positive integer factors of Scale, both are
dyadic. Hence B,q,P and Ph are dyadic too: L=BqP and Th=Ph^11.
This conclusion does not assume either old AND relation.

For any dyadic L, nonnegative high words and canonical low words,

    (Hr+L*Hh) AND (Mr+L*Mh)
       = (Hr AND Mr)+L*(Hh AND Mh).                  (10)

The bounds(8)--(9) make the low and high parts of Z unique. Equation
(10) consequently recovers

    Hr AND Mr=Zr,       Hh AND Mh=Zh.                 (11)

Moreover H,M<L*Th imply Hh,Mh<Th; Zh=Hh AND Mh is also canonical.
High-block bounds need not be postulated before invoking the joint
native theorem. The original global history bound is retained for its
usual history-decoding role.

We now have precisely both old prescribed-scale AND contracts:
L dyadic with canonical Hr,Mr and result Zr; and Th dyadic with
canonical Hh,Mh and result Zh. Each has a full positive native extension
by the complete AND64 theorem. Choose those two extensions independently
and retain all other outer and geometry coordinates. This produces a
zero of the raw parent certificate.

In particular the population-width proof retains its independent
geometry core at Q and index(2^D-1)J. The decoded AND supplies its old
scale typing, so that proof recovers Q=q^D, the common exponent and
exact dyadic input duration. The history contract then recovers the
same chronological one-hot tile word and both affine transports. No
native theorem is used to establish a bound that was already needed
to apply that theorem.

## 4. Completeness and the ordinary input

Conversely start with any positive zero of the raw parent. Its two
complete AND relations give all the old dyadic scales, ranges and
(11). The recoder's low base-B block is zero at the dyadic duration,
so its upper block gives

    Ahat-1=(xJ) AND K<=xJ.                            (12)

The new positive slack exists. Indeed P>J, q>x, q>=2 and J>=1 imply

    beta=S-Ahat >= qP-xJ-1
         = q*(P-J)+(q-x)*J-1 >=2.                    (13)

Keep every common outer coordinate and the independent geometry
witnesses. The joint words(6) are canonical below the dyadic scale
L*Th and satisfy their AND relation by(10). Invoke the complete
prescribed-scale AND theorem once to choose all22 fresh positive
native auxiliaries. This proves completeness. The two old AND tuples
are discarded; they generally cannot be reused as a tuple for the
new larger native scale.

Both directions preserve x and every program coordinate exactly.
The actual U9-derived binary table still has1968 states, CTS
half-length59101 and period118202. The fixed tag parameter is1182020,
and the data width remains

    D=47946621298704238734708993009920.

All eleven fixed-numeral roles keep their existing recipes. The valid
physical input has64n+b_S cells and its exact least dyadic counter is
128n. Nothing here relaxes that initialization. For each recursively
enumerable set S, choose the same four positive program parameters as
in the parent. The resulting fixed polynomial G satisfies

    x in S iff exists y_1,...,y_64>0:
    G(x,A_S,B_S,T_S,E_S,y_1,...,y_64)=0.

The usual arbitrarily long leading-zero padding supplies completeness.
No claim is made that every positive program tuple describes a valid
program. The fifth-parameter option preserves the parent's independent
duration-bound interface and has the same operation and witness counts.

## 5. Literal ledger, degree bound and verification

Start from the actual raw parent302=147M+155A,52 comparisons and85
witnesses. Remove exactly the64-gate history native component
(33M+31A), its16 comparisons and22 witnesses. Add the seven gates(7)
and the one-addition bound(5), one comparison and one witness. This gives

    certificate: 302-64+8=246=118M+128A,
    comparisons: 52-16+1=37,
    positive witnesses: 85-22+1=64.

A literal sum of37 squared residuals adds37M+73A, giving
**356=155M+201A**. All numeral multiplications are counted. This
packet emits the raw sum-of-squares polynomial only; separately
normalizing or merging its native norms requires its own source audit.

The degree checker propagates conservative total-degree bounds through
every actual gate, treating every input, program parameter and witness
as degree one and each fixed numeral as degree zero. Q has degree one,
q0 degree three, the history Ph degree four and Th degree44. The joint
native scale has degree at most47. Its first-norm residual has degree
at most290, dominating the propagated bounds for all other residuals,
and the final polynomial consequently has degree at most580. No
leading-coefficient noncancellation or exact-degree claim is made.

The source checks the exact64 deleted history rows against the frozen
history subpacket, all16 native comparisons, all22 native witnesses,
and the absence of any external consumer or exported reference to
them. It guards the low port and output-definition rows, renames only
the four definition sites, and performs a stable topological sort.
Both program-bound interfaces are built and checked. Historical
`history_packet` metadata remains available for auditing that original
standalone component; `history_core_embedded=False` records that its
native core is no longer embedded. The actual retained prefixes are
`geo__` and `and__`. The previous boundary comparison count is retained
only as historical metadata, not as a decomposition of the new native
core into two independent subcertificates.

The writer and fresh default evaluate384 complete certificates and
polynomials,192 signed. An independently instantiated canonical AND64
source receives the explicitly constructed words(6); its16 residuals,
all unaffected parent residuals and the new bound reconstruct the
entire new output. Fixed-numeral roles receive consistent finite
substitutions, which test algebra without materializing the enormous
actual coefficients or asserting their cross-role identities. Another
1024 canonical split checks test(10) and reject incorrect output pairs.
Finally108 genuine recoder bit fixtures and genuine finite affine
paths produce positive lower-output slacks and correctly concatenated
AND words. These last two components are independently valid outer
fixtures, not necessarily one common loader/terminal instance, and
none of these finite checks claims to construct a full positive Pell
zero. Five malformed rewrite contracts are rejected.

```sh
python3 neary_woods_universal_joint_and.py
```

Author writer and fresh default pass. Root independently reviewed the
full proof and source, replayed the final default, and checked that all
22 surviving AND auxiliaries have no consumer or comparison outside
their native component; no findings remained. A second reviewer passed
the full proof/source/fresh replay and independently checked144 complete
canonical-core/residual/SOS identities,72 signed;1968 untyped lower-bound
cases;2000 canonical splits; and264 recoder/arbitrary-high-AND component
extensions. These are algebra and outer-component checks, not full
numerical Pell zeros. All six local links resolve. The sole wording
correction changed “low B-bit block” to “low base-B block”; no arithmetic
or receipt was changed.
