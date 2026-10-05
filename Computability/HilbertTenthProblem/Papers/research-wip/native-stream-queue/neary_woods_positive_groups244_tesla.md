# Two positive selector groups give a complete U9 compiler in244 operations

The accepted245 construction has a **244=129M+115A** successor with the
same43 positive witnesses and degree **at most936**. Both inherited
ordinary-input program interfaces retain the complete paid loader,
unbounded history, native predicates and endpoints. The separate
universal84 bound is unchanged.

Supply the second selector group G03 directly. Paying S0 into the global
size P costs one addition; deleting the former group sum and its shifted
J correction removes two. A nested-carry argument recovers both middle
and top controller conditions before restoring the old positive selector.
No frozen source is executed to derive this change.

## 1. Actual language and complete affine map

Use the frozen245 chart, already supplying S0>0,G12>0 and Shat1>0. Set
S1=Shat1-1. On valid loaded U9 matching words, the first two tiles are
P_c,D_b by the accepted247 language proof. In particular the other group
G03=S0+S3 is strictly positive because S0>0. This makes it legitimate in
the completeness direction to replace supplied Shat3 by supplied G03.
It does not presume a match on rejecting inputs.

The child computes

    J=G12+G03,
    P=HU+HV+ZU+ZV0+ZVhat1+g+Shat1+S0.             (1)

The second extra selector contribution S0 is paid. All eight summands
of P are positive, so P>=8 and both S0,S1<P before equations. No subset
condition or bound by J is assumed for S0 or S1 at this stage.

The map into the old245 polynomial is

    Shat3_old=G03-S0+1,
    g_old=g+S0,                                   (2)

with all other supplied coordinates and all ten fixed numeral recipes
unchanged. The global slack is automatically positive. The former
selector hat might be zero or negative until Section3 restores its sign.

The old linear_group164=S0+Shat3 becomes G03+1. Its only consumer is
selector_sum6=G12+linear_group164. Therefore the old J subtraction gives
J=G12+G03 exactly. Delete linear_group164 and selector_sum6; rewrite the
existing J7 row directly as the addition of supplied G12 and G03.

The existing group_global_slack=g+Shat1 retains its source row. Add

    groups_size_slack=group_global_slack+S0

and use that new result as the P-row slack operand. It equals the old
private global-slack exit under(2). No other consumer requires the old
intermediate value. This is one added addition, two deleted additions
and two edited rows. A topological metadata reorder is permitted.

The complete polynomial identity is

    F244(new)=F245(Shat3=G03-S0+1,g_old=g+S0,others).           (3)

It holds over every commutative ring. To see that it is a whole-output
identity, the changed selector cone preserves J, the changed size cone
preserves P, and every other retained row and numeral is unchanged.
The upper transport already uses J in245. Thus there is no new fixed
constant compensation or uncharged arithmetic in(3).

## 2. Raw positive bounds before any selector typing

The source still uses

    Ctree=G12+P*S0+P^2*S1,
    Zb=ZU+P*ZV0+P^2*(ZVhat1-1),
    Mtree=J+P*(J+(b-1)J*G12),
    Hb=HU+P*HV+P^2*HV, Mb=(b-1)Ctree,
    Hr=HU+P*HV, Mr=(1+P)(D-1)J.                   (4)

These raw words are nonnegative. In particular both selector digits
S0,S1 are belowP by the paid sum(1). The low recoder and raw positive
native decompositions from245 are unchanged; the geometry discriminant
is positive on every positive child tuple. At a child zero, cancel that
multiplier to obtain the sixteen unscaled unit factors.

The signed global relation and the positive sum give

    P=(b-1)J+epsilon, epsilon in {-1,1},
    b=c_h D, c_h>=32, D>=1,
    J>=2, J<=P/6, b<=P+2, 0<=(D-1)J<P.           (5)

The lower bound J>=2 follows directly from the two positive groups.
Both G12,G03 are at mostJ. Thus the actual mask expansion is

    Mtree=J+P*(G03+(1-epsilon)G12)+P^2*G12,

with coefficients at most3J<=P/2<=P-2. As in245,

    Ctree<P^3, Mtree<=P^3-P^2-P-2,
    Mb<(P+1)P^3, Mb+P^3*Mtree<P^6.                (6)

The new S0 bound by P suffices for these estimates; a nonexistent raw
bound S0<=J is not used. Histories and selected words are belowP, so
Hb,Zb<P^3 and Hr,Mr<P^2. With T=P^8 the unchanged words

    H0=Hb+P^3*Ctree+P^6*Hr,
    M0=Mb+P^3*Mtree+P^6*Mr,
    Z=Zb+P^3*Ctree+P^6*Hr,
    H=H0+2T, M=M0+T

obey 0<=H0,M0,Z<T and

    H-Z>=T+1, M-Z>=1, bT-H-M+Z>=(b-5)T+2.

These are exactly the scalar bounds needed for positive joint truth
fields before any AND typing. The signed native recovery from245
therefore applies: first recover the joint dyadic scale and its positive
factors b,P, then the geometry/low-mask signs. The independent signed
Mersenne argument gives

    P=b^t, t>=1, J=(P-1)/(b-1), epsilon=1.         (7)

The argument uses no selector-bit conditions. Writing b=2^d with d>=5,
2^k modulo2^d-1 cannot equal -1, and equality to1 forces d|k.
The native AND and low-block separation consequently give H AND M=Z.
The physical mask has not yet been assumed to fit its old region.

## 3. Nested carry and two exact controller lanes

Put m=b-1. The low physical coefficient mG12 is at mostP-1, but mS0
and mS1 need not be. Define their exact successive carries

    c1=floor(m*S0/P),
    c2=floor((m*S1+c1)/P).                        (8)

Since 0<=S0,S1<=P-1, one has 0<=c1<=m-1=b-2. Also

    m*S1+c1 <= m(P-1)+(m-1)=mP-1,

so 0<=c2<=b-2. Writing mS0=r1+Pc1 and mS1+c1=r2+Pc2 gives

    Mb=mG12+P*r1+P^2*r2+P^3*c2,
    0<=mG12,r1,r2<P.                              (9)

Thus the effective controller mask is Mtree+c2. By(7) it equals

    (J+c2)+P*G03+P^2*G12.

Its lowest digit is still belowP:

    J+c2<=J+b-2<P,
    P-(J+b-2)=(b-2)(J-1)+1>0.                    (10)

There is no controller carry into its middle or top digits. Equation(6)
also excluded any carry out of the whole controller region into the
range region atP^6. No cancellation or informal carry suppression is
being used.

P is a power of two, so extraction of its digit blocks commutes with
bitwise AND. In H AND M=Z, the middle controller coefficients at offset
P^4 and the top coefficients at offsetP^5 give, respectively,

    S0 AND G03=S0,
    S1 AND G12=S1.                               (11)

Both are obtained before assuming either selector bound. Hence
S0<=G03<=J and S1<=G12<=J. Now mS0,mS1<=P-1, so c1=c2=0. The physical
and controller regions have their exact old meanings, including the
lowest controller lane. In particular

    Shat3_old=G03-S0+1>=1.

All old245 supplied coordinates in(2) are positive, and(3) is a genuine
positive parent zero. Only now invoke the complete245 theorem to recover
the genuine loaded U9 word and halting. This proves soundness without
using an old selector that might initially be negative.

## 4. Positive converse, exact count and degree

Conversely take a positive245 zero on a valid program slice. Its typed
S0 is positive, so

    G03_new=S0+Shat3_old-1>0.

Set g_new=g_old-S0 and leave every other supplied coordinate fixed. The
245 proof provides the quantitative bound g_old>=30J-1, not merely a
constant positive lower bound. Its typed S0 is at mostJ. Therefore

    g_new>=29J-1>=28>0.                           (12)

Equation(3) supplies a positive244 zero, and these maps invert(2).
Thus the change is a bijection of complete positive zero tuples on valid
U9 program slices. Malformed arbitrary positive parameter values are
not asserted to describe those word languages. No accepting history is
claimed to exist for a rejecting input.

Every recursively enumerable set of positive integers therefore retains
the same four effective fixed program parameters and ordinary-input
zero criterion, with43 positive existential witnesses. The optional
fifth duration parameter remains separate with the same count. All
variable-length controller, range, endpoint and native obligations are
still present and charged.

Each full source has244=129M+115A operations. Before its last subtraction,
its certificate costs243=129M+114A with one comparison to the already
paid geometry discriminant. The graph retains241 literal row records,
edits two rows, deletes two and adds one; all supplied ports, rows and
ten fixed numeral roles remain live. The degree bound936 follows by the
affine identity(3) from245. It is not an exact degree calculation or a
source-array degree propagation.

**Remark 1 (no unpaid bound on the second selector).** Supplying G03
alone does not imply S0<=J: at G12=G03=1 and S0=100, J=2. The extra
paid S0 contribution to P is therefore an actual proof obligation,
not a redundant positivity convention. This is a raw selector-cut
counterexample, not a zero of the complete source.

**Remark 2 (the new carry is genuinely nested).** The formula
`c2=floor(mS1/P)` would omit the carry from the middle physical digit.
For positive dyadic-prefix data b=32,P=1024,J=33,G12=1,G03=32,
S0=34,Shat1=34 (so S1=33), HU=HV=2,ZU=ZV0=ZVhat1=1,g=949,
the paid sum(1) and P=(b-1)J+1 both hold. But c1=1 and c2=1,
whereas floor(mS1/P)=0. The middle/top controller tests reject this
assignment; it is not claimed to be a compiler zero. Formula(8) and
ordered recovery(11) are necessary for the stated proof.

## 5. Scope, authentication and fresh checks

The frozen245 proof and both source arrays are read inertly, and the
first-two-tile premise is inherited with its exact actual-U9 scope from
247. The accepted native scalar and signed Mersenne interfaces remain
those explicitly isolated in245 and250. This packet rechecks their new
scalar inputs and does not re-audit old machine or Pell implementations.

Only fresh static graph edits, independent handwritten polynomial cuts
and scalar/bit diagnostics are run before freezing. No archived,
supplied, predecessor or frozen program is executed or imported; no
saved array is evaluated or used to propagate arithmetic or degrees.
Author files are in /tmp, and root alone handles repository mutations.

The fresh writer and exact saved-receipt comparisons in normal and
optimized Python modes from `/` passed before freezing. The receipt
contains both complete244 sources (488 rows), six independently
handwritten polynomial-cut identities,880 signed prefix contexts
(440 negative-sign and440 height-one), and408 dyadic two-lane contexts.
Twenty-four of the latter have a genuinely nested carry. Remark2's
specific omitted-carry counterexample is also retained. These checks
support the all-size argument; no full compiler or native Pell zero is
materialized or inferred from sampling.

Evidence SHA256:

- Helper: `21bfe676106749fefe71bd0f5b32e3cd8689f3e68c24f4798782fb717750d203`.
- Receipt: `59fb18b0cda52249afab70bf7e2952e80378ab41961e299d809dfa20e322003b`.

The following dependency bytes are authenticated under
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue`,
with the identical same-name frozen author /tmp file allowed before its
repository installation. A byte pin does not broaden proof-read scope.

| Dependency | SHA256 |
| --- | --- |
| `neary_woods_positive_group245_tesla.md` | `fad086d06813e2dc97eb0b18b68d064fdbc67d35f6352efbdee27c43a32d851c` |
| `neary_woods_positive_group245_tesla.json` | `d9ddce2c7581243ff18a2e36c694bb5dd321e12286388c995ee4bc6ddadf4d38` |
| `neary_woods_positive_first_production247_tesla.md` | `9cb9da3c211fecbe3129421b23a16c747d8d1bf7b6365cf6320c426733ffd56a` |
| `neary_woods_hierarchical_history250_tesla.md` | `1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330` |
