# Terminal-length restrictions without radix divisibility

Status: author and two independent complete proof/source reviews and fresh
verification runs passed on the strengthened28H theorem without findings.
The proof and arithmetic are frozen. All published certificates and omission
families are unchanged.

In the weakened104 source obtained by omitting q=Rv, every terminal length
is odd. For deletion number beta=1 the source is unsatisfiable. For beta=2,
the additional numerical condition R>=28H forces Lfinal=3. Thus terminal
nonmarkers5 and7, if they occur at all, must have R<28H.

The last condition is a theorem hypothesis, not an extra free comparison
or a proposed certificate operation. General beta=2 terminal classification
and the halting semantics of the weakened104 source remain open.

## 1. Retained sources and the decoding boundary

Use `EXPLORATION_TAG_RADIX_DIVISIBILITY_OMISSION.md` and the original
generic105 input convention. Write Li=Linit and Lf=Lfinal. The retained
equations include

    R=CA, H(R-1)=q-1,
    L=2Nsum+H,
    R[L+(B-1)M1]=Kh(L-Li+qLf),                         (1)

where K=3^beta, Kh=K/3, B=3^(a-1), a>=2, C is the fixed power of three
strictly greater than K,3^a,2U+3, and

    A>Li=3^ell>=K, Nsum>0, M1=2Q+S1>=0,
    0<Lf<K.

Positive H and geometry give q>=R even without q=Rv. Therefore the
generic105 preliminary bounds and its signed-content kernel bootstrap
continue to hold. They give q a power of three. The field recovery from
the concatenated q-blocks also still applies: its scalar bounds and
successive rejection of negative conceptual fields use q's power property,
the displayed positive equations, and R=CA, not R's being a power of three.
In particular M0=L-M1 and M1 are Boolean ternary words below q.

This is not an assertion of rowwise tag semantics at radix R. That later
part of the predecessor proof uses precisely the deleted divisibility
condition and is not imported here. The first two results below need only
q odd, containment, and M1>=0; the short-geometry result additionally uses
the recovered Boolean M0 and M1.

## 2. Odd terminal length without an odd-radix assumption

Since q,Kh,B and Li are odd, reduce the length source modulo2. Containment
gives L=H modulo2, so

    R H = H-1+Lf modulo2.

Meanwhile H(R-1)=q-1 is even. Subtracting gives

    Lf=1 modulo2.                                       (2)

Nothing in this argument assumes R or A is odd. In particular beta=2 leaves
only Lf=1,3,5,7 before applying any further condition.

## 3. Deletion number one is impossible

For beta=1, Kh=1 and 0<Lf<3. Equation(2) forces Lf=1. Subtract geometry
from the length equation and rearrange:

    (R-1)(L-H)+R(B-1)M1=1-Li.                          (3)

The left side is strictly positive because L-H=2Nsum>0 and R>1;
its second summand is nonnegative. The right side is negative since
Li>=K=3. This is a contradiction.

This agrees with the ordinary tag dynamics for this case: when beta=1,
both rules append at least one symbol, so a nonempty input never halts.
The assertion here is stronger than that dynamic observation, because it
proves the weakened arithmetic source itself unsatisfiable.

## 4. A necessary lower bound on H for terminal5 or7

Now beta=2, Kh=3 and K=9. Define mathematical abbreviations

    O=L+(B-1)M1, Delta=O-3LfH.

An exact consequence of length and geometry is

    R Delta=3[L-Li-Lf(H-1)].                            (4)

Before imposing a size bound on H, the scaled length source is

    D O=L-Li+qLf, D=(C/Kh)A=(C/3)A.

The fixed power C is at least27, so D is divisible by9. Both Li and q
are also divisible by9. Reducing this source modulo9 proves L=0 modulo9
unconditionally in beta=2. The addition M0+M1=L has no ternary carries,
since both summands are Boolean. Its two low trits can be zero only if
the corresponding trits of each summand are zero. Hence M0 and M1 are
both divisible by9, and so is O=M0+B M1. In particular Delta is a
multiple of three. No power property of R or Boolean property of H has
been assumed in this divisibility argument.

Now assume R>=28H. The paid input bound and C>=27 imply

    Li<R/27, R>=270, q=(R-1)H+1<=RH.

From the length source, positivity and Lf<9 give

    L<27q/(R-3)<28H.

Using Lf<=7 from(2), equation(4) therefore gives

    Delta<3L/R<84H/R<=3,
    Delta>-3Li/R-21H/R>-1/9-21H/R
          >=-1/9-3/4=-31/36>-1.

The upper bound on Delta is strictly less than3, including when R=28H:
strictness comes from L<28H. The only multiple of three in the open
interval(-1,3) is zero. Consequently

    O=3LfH, L=Li+Lf(H-1).                              (5)

Geometry gives H=1 modulo3 because q and R are divisible by3. We already
know O is divisible by9. Thus O=3LfH forces3|Lf. Together
with oddness and 0<Lf<9, this proves

    Lf=3.

The nonpower family with H=1+3^k and R=3^(3k)-3^(2k)+3^k lies well inside
R>=28H for large k. This conditional restriction helps explain why that
type of short geometry cannot supply the requested beta=2 nonmarkers.
It does not assume that every possible nonpower geometry has this form.

## 5. Exact verification and limits

`explore_tag_terminal_restrictions.py` freshly verifies the complete20
source comparisons and the104 count for both fixed-leading-symbol branches.
It expands the exact identities(3)--(4) and the scaled length identity,
exhausts their modulo-two parity
assignments including even R, and checks the short-geometry inequalities
using exact rational arithmetic. Its low-two-trit check enumerates all
Boolean M0/M1 residues modulo9. A separate complete residue check verifies
that the scaled length source forces L=0 modulo9. The rational check
includes R=28H exactly and explicitly tests that the only multiple of
three in the strict permitted interval is zero.

The remaining sign examples are explicitly illustrations of the proved
contradiction, not asserted full-source witnesses. No tuple with terminal5
or7 has been constructed or ruled out outside R>=28H, and no104 halting
equivalence or universal operation improvement follows from these lemmas.
