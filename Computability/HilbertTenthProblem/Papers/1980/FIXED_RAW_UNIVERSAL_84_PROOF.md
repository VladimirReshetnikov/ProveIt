# An 84-operation fixed-index certificate for positive raw inputs

For every recursively enumerable set S of positive integers, one can
effectively choose fixed positive numerals, independent of raw input x,
such that the system below has strictly positive integer witnesses if
and only if x belongs to S. Its complete straight-line certificate is
**84=44M+40A**, with **33 positive existential unknowns and21 equations**.
Numerals and equality comparisons are free; multiplication by a numeral
is counted. This improves the complete
[88-operation theorem](FIXED_RAW_UNIVERSAL_88_PROOF.md) by four operations.

The input remains a raw positive coordinate. It is not compiled into
the fixed numerals. The construction directly inserts both fixed marker
bits into an otherwise masked word. Encoding End with scalar1 removes
the multiplication formerly needed to insert it. The word left after
removing both markers is a supplied positive coordinate, so it requires
no separate multiplication by the cell radix.

The [executable source](../verification/explore_fixed_raw_universal_84.py)
and [receipt](../verification/explore_fixed_raw_universal_84.json) state
all84 primitive operations and all21 source residuals. The proof below
supplies the universal soundness and positive completeness arguments;
the bounded checks do not materialize enormous full Pell witnesses.

## 1. Fixed machine, fixed markers, and fixed coefficients

Use the [fixed unary tableau theorem](EXPLORATION_FIXED_UNARY_TABLEAU.md)
for the chosen set S. Its normalized machine starts on t+1 ones, where
`t=x+2`, writes a right-endpoint flag, moves left in its first step, and
never visits a positive tape coordinate. Its fixed phase graph gives
first rows `L^a I^t Q R^b`. The local alphabet and transition relation
depend only on the chosen semidecision machine, not on x.

Apply the [exact-period three-cell lift](EXPLORATION_THREE_CELL_PERIOD_LIFT.md).
The fixed alphabet consists of allowed3-by-3 windows; the rule on center,
right, and next enforces the two overlaps. Let End=E3 have alphabet
index0, and Start=S3 have index1. Other states have indices2 through
`k-1`, where `k>=2`. These are fixed distinct states. A canonical
single-rectangle completeness torus has exactly one of each: every
Start is an initialized Q, and every End is the first I of that row.

Compile the ternary relation homogeneously as before. Choose a power
of two `A>max(2k,4)`. Three occupancy clauses use mask `A-2`; two
center/right and center/next occupancy-equality clauses use mask1.
Each forbidden state triple contributes its selected indicator sum
with weights `(1,1,2)` and mask4. All raw clause values are below A,
so their radix-A concatenation is a linear form

    phi=sum_(s,i)c_si*z_si, mu=sum_j A^j*mu_j,
    s in {C,R,Y}, i=0,...,k-1.                        (1)

Every coefficient is positive. Put `m=popcount(mu)` and, if necessary,
append zero-expression mask1 clauses until `m>=k`. Thus the local test
has exactly m tested binary positions. This compiler depends only on
the fixed finite relation.

## 2. Unshifted state bits and two forbidden positions

Use m+2 Boolean positions per cell, numbered `0,...,m+1`. The first k
are genuine state indicators; the rest are ignored dummies. Define the
following fixed numerals:

    R>=max((m+2)sum c_si,mu)+2, R a power of two,
    p=k-1, H=k+m, B=R^(H+1)=R^(k+m+1)=2^d,
    CS=R,
    Ds=sum_(i<k)c_si*R^(p-i), s in {C,R,Y},
    MC=B-1-sum_(j=2)^(m+1) R^j,
    MF=mu*R^p.                                       (2)

The native scalar cell is now

    Ccell=sum_(j=0)^(m+1) z_j*R^j.                    (3)

There is no leading factor2. End has scalar1 with dummy0, and Start
has scalar CS. The mask MC forbids positions0 and1 and permits exactly
the m positions2 through m+1. It will type the remainder word Z, not
the full word C.

For any typed bits, including zero or multiple genuine indicators,

    Fcell=DC*Ccell+DR*Rcell+DY*Ycell.                  (4)

Each product coefficient is nonnegative; their total sum is at most
`(m+2)sum c_si<=R-2`. The highest degree is H. Therefore there are no
inner-radix carries, including from off-diagonal products, and

    0<=Fcell<=B-2.

The coefficient at degree p is exactly phi. Dummy terms lie above it.
Consequently `Fcell AND MF=0` is exactly the homogeneous clause test.
Every native cell is also at most B-2: its coefficient sum is at most
m+2<=R-2 and its degree is at most H. The fixed constants satisfy

    0<DC,DR,DY<B, 0<MC,MF<=B-2,
    MC odd, MF even,
    popcount(MC)=d-m, popcount(MF)=m.                  (5)

MF is even because `p>=1`. The low mask forbids the unit binary bit,
so any word typed by MC is even. The two extra dummy positions keep
the population balance unchanged while forbidding both markers.

## 3. All coordinates and all21 equations

The raw parameter is x>0. The33 positive existential coordinates are

    q,P,C,v,J,align,F,alpha,z,Z,
    a,c,dmain,f,h0,i,j,k0,o,r,s,w,tau,eta,zeta,gamma,yaux,
    W,kappa,muP,delta,phiP,rho.

The source names are `Jrep,zquot,d,h,k,ga,y_aux,mu,phi` for
`J,z,dmain,h0,k0,gamma,yaux,muP,phiP`, respectively. The compiler mask
mu in (1) is a fixed numeral; the positive Pell coordinate muP is
different. Neither k0 nor the existential discriminant notation below
is the fixed alphabet size or the inner radix.

Construct the expressions

    t=x+2, Lambda=q^2, D0=q^3,
    Scode=Z+qF, Mcode=(MC+q*MF)J,
    X=wD0, Yp=sD0, Delta=a^2+4a+3,
    A0=a+2, u=j*c-(2r+1), E=DR+B*DY.                 (6)

Here E and B-1 are fixed numeral aliases; the other expressions use
the counted schedule. A0 is mathematical shorthand and need not be
constructed as a separate register.

The seven outer equations are

    (B-1)J=q-1,                     P*v=q,
    (B-1)align=P-1,                 C+alpha+t=q,
    (DC+E*P)C=F+z*(q-1),
    r=(Lambda-Scode)*(Lambda-1)+Mcode,
    C=CS+Z+W.                                         (7)

The ten retained positive Pell equations are

    X*Yp^2*(X*Yp^2+1)*k0^2=tau*(tau+1),
    c=Yp*k0+eta,                    k0=eta+zeta,
    k0=r+1+h0*X*Yp,
    a=Yp*(X+1),
    dmain=X+a*c+gamma*(4a+3),
    dmain^2=Delta*c^2+1,
    (i*c^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)*(u^2-yaux^2)=1-yaux^2,
    u=o*f-c.                                          (8)

The four raw-exponent equations are

    kappa=t+delta*(a+1),              c=kappa+phiP,
    muP^2=1+Delta*kappa^2,
    muP=W+kappa*(A0-P)+rho*(Delta-(A0-P)^2).           (9)

No endpoint remainder, hidden inequality, digit condition, or additional
power equation is imposed. In particular Z is not required to be
divisible by B. Start and End cells may have ignored dummy bits.

## 4. Bounds and kernel decoding before any state interpretation

Take any positive solution. The geometry gives `q>=P>=B>=16`.
The strengthened bound and marker decomposition give

    0<t<q, 0<Z<C<q, 0<W<C<q.                         (10)

This is the strict endpoint bound required by the exponent bridge,
obtained before interpreting W as a power. By (5) and the repunit
equation,

    0<Mcode<q^2-1.

Positivity of r forces `Z+qF<=q^2`. Since Z is positive, `F<q`.
Now both fields are strictly below q, so `0<Scode<q^2` and

    q^2<=r<q^4, D0=q^3<r^2.                           (11)

These are exactly the pre-power hypotheses of the retained43-operation
kernel. Its direct nonsquare-scale proof gives

    X=2^(2r+1), c=psi_(a+2)(2r+1),
    q^3 divides binom(2r,r), a>2r+1.                 (12)

Specifically `X,Yp>=q^3`, `a>q^6>2r+1`, `XYp>=q^6>r+1`, and
`4r/a<4/q^2<=1/64` give the retained growth and ratio estimates.
Since q^3 divides X, q is a power of two. The repunit equation forces
`q=B^N`; divisibility P|q and its alignment force `P=B^h`, with
`1<=h<=N`. None of these steps assumes that C is typed or that F is
the actual field of a configuration. They use the bounds, masks, and
kernel equations only.

## 5. Decode the raw exponent before inserting the markers

Apply the [positive exponent bridge](EXPLORATION_RAW_INPUT_EXPONENT_BRIDGE.md)
to (9), using (10)--(12). The norm gives
`kappa=psi_A0(u0), muP=chi_A0(u0)`, and the positive gap gives
`0<u0<J0=2r+1`. The first congruence gives `u0=t mod(a+1)`.
Both indices are strictly below a+1, because `t<q<J0<a+1`.
Thus u0=t.

Put `Hexp=Delta-(A0-P)^2`. The last equation gives
`W=P^t mod Hexp`. The retained bounds imply

    P^t<q^q<=2^(q^2)<=2^r<X<A0<Hexp.

Since `0<W<q<Hexp`, this is exact:

    W=P^(x+2)=B^(h*t), h*t<N.                         (13)

In particular `h*t>=3` and `N>=4`. This stage deliberately precedes
typing the full C word. It has not used the conclusion that either
marker is a genuine state.

## 6. Mask recovery and the two disjoint bit insertions

The two fields of Mcode are disjoint and have population dN. The
inverse-packing identity, including its strict overflow case, bounds
the population of r by3dN, with equality exactly when
`Scode AND Mcode=0`. The central-binomial divisibility in (12) forces
that equality. Strict field bounds in (10)--(11) separate it into

    Z AND (MC*J)=0, F AND (MF*J)=0.                   (14)

Thus every radix-B digit of Z has Boolean positions2 through m+1,
and has positions0 and1 absent. Equation (13) places W at the unit
bit of cell ht; CS is the position1 bit of cell0. They are different
cells, and both bits were absent from Z. Therefore

    C=CS+Z+W

inserts exactly those two bits, with no binary or cell carry. Every C
cell is typed into positions0 through m+1. Position1 occurs only at
cell0, and position0 only at cell ht. At this stage either marked cell
may still have other genuine bits; those are excluded next, rather
than assumed absent.

Form C's actual right and next words and the field in (4). Its bounds
give `Factual<q-1`, and `DC*C>0` gives its strict positivity even before
genuine occupancy has been established. The local equation in (7)
gives `F=Factual mod(q-1)`. As `0<F<q`, it forces exact equality.
The second mask in (14) now gives the homogeneous clauses everywhere.

The occupancies are at most1 and invariant under h and h+1, hence
under1. The inserted Start bit makes their common value1. This
excludes all additional genuine bits at both marked cells, and every
cell becomes a genuine state. The fixed ternary relation holds, Start
occurs exactly once at0, and End exactly once at ht. Dummy bits may
remain at either marked cell and do not change its genuine state.

The fixed unary theorem therefore applies. Pulling back any cyclic
word gives a periodic plane tableau. The unique Start prevents the
End at left distance t from belonging to another rectangle, since
reaching such an endpoint would cross that rectangle's initialized
head and hence another Start. The initialized I-run has exactly t
cells. Exact transitions, no escape, and acceptance at the last row
prove halting on raw input `x=t-2`. This proves soundness without
assuming `N=h(h+1)`.

## 7. Completeness with every witness strictly positive

Suppose x belongs to S. The fixed unary theorem gives sufficiently
large `(h+1)`-by-h single-rectangle tori, with one Start and one End.
Their cyclic presentation has `N=h(h+1)`, Start at0, End at ht, and
`ht<N`, where `t=x+2>=3`. Encode genuine state bits with dummy0 and set

    q=B^N, P=B^h, W=P^t, Z=C-CS-W.

Removing the two marked bits leaves all other genuine cells intact.
Since `N>=4`, Z is positive. Its mask in (14) vanishes, and every Z
cell uses positions2 and above. Hence Z is even. It need not be a
multiple of B for the soundness theorem; this canonical dummy0 choice
may have that additional property without requiring it.

Set `J=(q-1)/(B-1), v=q/P, align=(P-1)/(B-1)` and let F be the actual
field. Every genuine scalar cell is at least1, so `C>=J`. For the wrap
quotients

    Rword=PC-kR(q-1), Yword=BPC-kY(q-1),

one has `kR>=0` and

    kY=floor(BPC/(q-1))>=P.

Consequently `z=DR*kR+DY*kY>=DY*P>0`. This is the positive transport
proof appropriate to the unshifted coding; no lower bound2 on every
cell is assumed.

The strengthened slack is positive. Native cells satisfy
`C<=(B-2)J`, so `q-C>=J+1`; and (13) gives
`N-1>=ht>=t`, hence `J>=B^(N-1)>=B^t>t`. Take
`alpha=q-C-t>0`.

Form the actual new packed index from (6)--(7). Its masks vanish, so
its population is3dN, giving the required central-binomial divisibility.
It obeys (11) and is odd: Z and qF are even, whereas MC and J are odd.
The full retained fresh positive fixed-minus Pell construction applies
at this actual r,D0 and supplies all seventeen kernel witnesses in (8).
No numerical witness from an earlier packing is reused by identification.

Finally choose

    kappa=psi_A0(t), muP=chi_A0(t),
    delta=(kappa-t)/(a+1), phiP=c-kappa,
    rho=(muP-(A0-P)*kappa-W)/(Delta-(A0-P)^2).

The exponent bridge proves integrality and strict positivity of all
five coordinates, including x=1. These choices satisfy (9). All33
existential coordinates are positive and all21 equations hold.

## 8. Exact84-operation ledger and evidence boundary

| Part | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Geometry |3|2|5|
| Existing C+alpha register |0|1|1|
| Three-cell transport |3|2|5|
| Powers and inverse packing |6|5|11|
| Two direct marker additions |0|2|2|
| Full retained Pell kernel |25|18|43|
| Raw exponent, x+2, strengthened bound |7|10|17|
| **Complete source** |**44**|**40**|**84**|

The five-part outer subtotal before the kernel and exponent is24.
It constructs C's marker right side by `CS+Z`, followed by `+W`.
Z is supplied, so no radix multiplication constructs it. End has code1,
so there is no numeral multiplication of W. Neither saving introduces
an unpriced inequality or an input-dependent numeral.

The checker verifies all21 expanded source residuals and the same
acyclic preceding-norm correction as the retained43-operation kernel.
It separately checks the native scalar compiler and the two insertions,
including nonzero dummy bits at the marked cells and Z not divisible
by B. Composed examples share the actual q,P,C,Z,W and demonstrate
positive outer and exponent-adapter coordinates. Their moderate Pell
parameters are deliberately separate from the astronomical packed
kernel indices; the general converse above supplies those full
witnesses. No Lean formalization, numeral-size bound, or global
optimality of84 is claimed.
