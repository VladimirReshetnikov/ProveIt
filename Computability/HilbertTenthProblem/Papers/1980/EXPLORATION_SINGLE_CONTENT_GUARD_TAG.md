# A single guarded content word gives a complete104 tag certificate

This is a complete positive encoded-input certificate with **104 operations =
53 multiplications + 51 additions/subtractions**, 33 positive unknowns and
20 equality comparisons, for every fixed binary appendant of length at least
two. Both fixed leading-symbol schedules have this count. Author and two
independent complete proof/source reviews and fresh verification runs passed
without findings. The proof and arithmetic are frozen in the companion files.

The input is the original specified binary word, with its ordinary ternary
value and power-of-three length marker. No input conversion is hidden. This
is not a universal raw-input bound. Unlike the separate weakened104 source,
this certificate retains the paid equation q=Rv and recovers genuine radix
geometry. The published generic105 and all weakened-source results are unchanged.

The main change is to mask only GN=N+Jg, where Jg fills the top beta trits
of every row. There is no Boolean mask on N, no Nbar or Nsum coordinate, and
no numerical containment equation relating content to its length marker.
The proof explicitly permits signed content rows. A first discrepancy either
forces a forbidden digit in the following guard or occurs at a step whose
actual successor is already short.

## 1. Exact positive source and operation count

Fix beta>=1 and a binary word u of length a>=2, with the tag productions
0->0 and 1->u. First symbols occupy least significant ternary positions.
Compile the fixed integer numerals

    K=3^beta, k=K/3, B=3^(a-1), U=value(u), cc=(k-1)/2,
    epsilon=U mod3 in {0,1}, Ut=(U-epsilon)/3.

Choose a fixed power of three

    C>max(K^3, K*3^a, 2KU+3),
    j=(C-C/K)/2.

These numerals and quotients are fixed at compilation and cost no variable
division. In particular j is a positive integer. Retain the original input
parameters Li=3^ell and Ni=value(input), where ell>=beta.

The supplied positive coordinates are those listed in the checker. In
particular F_Q,F_S1,F_T,F_E,F_Nfinal are positive and define the possibly-zero
values

    Q=F_Q-1, S1=F_S1-1, T=F_T-1, E=F_E-1, Nf=F_Nfinal-1.

The supplied A,H,R,L,q,Lf,alphaI,alphaH,v,r,betaP and the seventeen kernel
auxiliaries are positive. Compute

    2Q=twice_Q, M1=2Q+S1,
    N=3T+S1              if epsilon=0,
    N=3T-2Q              if epsilon=1,
    D=(C/k)A.

Only the fixed appendant determines the branch. N may initially be negative
in the second branch. The nine outer comparisons are

    kD=R,
    D(T-E+Ut*M1)=N-Ni+qNf,
    D[L+(B-1)M1]=L-Li+qLf,
    Li+alphaI=A, Lf+alphaH=K,
    H(R-1)=q-1, Rv=q,
    2r+1=q^9+2P, r+betaP=q^9.                         (1)

The first two computations give the exact polynomial identity

    N-3E-S1+UM1=3(T-E+Ut*M1).

Thus (1) includes the usual content transport

    R(N-3E-S1+UM1)=K(N-Ni+qNf).                       (2)

The nine conceptual fields, in increasing q-block order, are

    Gstar=Q+AH+H-S1, Q, S0=H-S1, S1,
    M0=L-M1, M1, Ebar=ccH-E, E,
    GN=N+Jg, Jg=jAH.                                  (3)

They are expressions, not additional supplied positive coordinates. Their
Booleanity is proved from the kernel and index comparison. Let

    Lo6=H(A+q^2+1)+(q+1)Q+(q^3-q^2-1)S1
         +q^4[L+(q-1)M1],
    TE=ccH+(q-1)E,
    P=Lo6+q^6 TE+q^8 GN.                              (4)

Expanding (4) gives exactly the q-Horner packing of (3), including when a
conceptual field is negative. The complete DAG retains the low packing from
generic105. It removes the two containment operations and Nsum, replaces
the old two-operation top pair Nsum+(q-1)N by the three operations
j*A, (j*A)*H, N+(j*A)*H, and changes q^10 to q^9. The power chain
q^2,q^4,q^8,q^9 still costs four multiplications. Hence the total is104,
with one fewer positive coordinate and one fewer comparison than105.

The eleven remaining comparisons and44 operations are exactly the established
parity-free Pell kernel, supplied with D0=q^9. The checker expands every one
of the20 source polynomials in both branches; the known norm-source correction
now occurs at comparison17. It does not infer source equality from a numerical
sample or treat internal signed registers as positive unknowns.

## 2. Bounds before any power or mask conclusion

All bounds in this section use only the positive source domains and (1).
Geometry gives q>=R and H=(q-1)/(R-1). Since A>Li>=K and C>K^3,
R>K^4; the weaker R>K^2 suffices for the estimates below.

The length equation gives

    (R-k)L+R(B-1)M1=k(qLf-Li)<kKq.

Since L>0, M1>=0 and B>=3,

    0<L<q/2, 0<=M1<q/6,
    0<=Q<q/12, 0<=S1<q/6, N>-q/6.                   (5)

For the first estimate use R-k>2kK; for the second use
kK/R<1/3 and B-1>=2. The N estimate follows in either fixed branch
from T>=0 and 2Q<=M1. Also

    Jg=(R-R/K)H/2 >= (q-1)/3,
    GN>q/6-1/3>0.                                    (6)

Here q is already larger than108, so the final positivity is strict.
Every coefficient in the displayed factored Lo6 is positive or nonnegative
when q>=2; H,L>0 make Lo6>0. TE>=0 because cc,E>=0. Thus P>0 before
any field is known Boolean. The index and positive packed slack imply

    (D0-1)/2<r<D0, D0=q^9>=81,
    r>=27, r<2D0, D0<r^2.                            (7)

These are all the scale hypotheses of the established44 kernel. In
particular no content bound, N positivity, field mask, or power-of-three
property has been used to justify its invocation.

## 3. Kernel bootstrap and recovery of all nine fields

The parity-free kernel soundness theorem gives D0 a power of three and
the required central-binomial valuation. Since D0=q^9, q is a power of
three. With 0<r<D0, the unit-two mask theorem makes every trit of r
native1/2 with unit2. Subtracting (D0-1)/2 digitwise shows that P is Boolean,
has unit1 and satisfies P< D0/2.

From (4), Lo6>0 and TE>=0,

    q^8 GN<P<D0/2,
    0<GN<q/2, GN<=J=(q-1)/2, N=GN-Jg<=J.             (8)

This deduction is about the scalar GN; its individual block typing will
follow below. It does not assert that N is nonnegative or Boolean.

The content identity (2) gives

    3E=(1-K/R)N-S1+UM1+K Ni/R-KqNf/R.

As U<(3B)/2 and the pre-mask length bound gives
M1<q/[3(B-1)], we have UM1<3q/4. The input contract gives
Ni<Li/2<A/2, so K Ni/R<1/2. Using N<=J and 0<1-K/R<1
is legitimate even when N<0: that term is then negative. Consequently

    E<5q/12+1/6<q/2.                                 (9)

The following bounds now hold for the first eight conceptual fields:

    -q/2<Gstar<q, 0<=Q<q,
    -q/2<S0<q, 0<=S1<q,
    -q/2<M0<q, 0<=M1<q,
    -q/2<Ebar<q, 0<=E<q.                             (10)

For Gstar use its lower bound -S1 and
Gstar<=Q+(A+1)H<q/12+q/3<q; the last inequality follows from
(A+1)/(R-1)<1/3. S0<=H<q, M0<L<q/2, and their negative bounds
follow from (5). Finally Ebar=ccH-E, where 0<=ccH<q/2, gives its
two bounds by (9). These are scalar inequalities, independent of digits.

Recover the q-blocks of P successively. With zero incoming carry, a field
w in (-q/2,0) has remainder q+w>J; that remainder cannot be Boolean.
It is therefore nonnegative, and its upper bound <q means there is no
outgoing carry. Induct over the first eight fields using (10). The last
block is then exactly GN, which is already between0 andq by (8).
Thus all nine fields in (3) are individually nonnegative and Boolean.

Since q=Rv and R=CA, R is now a power of three as well. The divisibility
R-1 | q-1 implies q=R^t with integer t>=1. A=R/C is a power of three.
This establishes all row geometry from paid source equations.

## 4. Projector, deleted prefix and the length path

The recovered S0+S1=H is carry-free, so S0,S1 partition the row heads.
The equation 2Q+S1=M1, together with the Boolean Gstar=Q+AH+S0,
gives the usual single projector in every row. If its head selector s_i
is zero, Q_i=M1_i=0. If it is one, Q_i is a run of ones ending before
the A-position, and M1_i is a single marker at most A.

For clarity, this also holds with the extra S0 in Gstar: at an inactive
head the equation for M1 starts with no incoming carry and forces Q to
remain zero. At an active head S0 is zero and the A-digit in Gstar
forces the projector's carry to terminate there or earlier. Induction
therefore gives zero outgoing carry at every row boundary.

Similarly E+Ebar=ccH implies carry-free support in the lowest beta-1
positions of each row. Hence d_i=3E_i+s_i is Boolean and

    0<=d_i<=(K-1)/2, d_i mod3=s_i.                    (11)

This includes beta=1, when E=Ebar=0.

The length equation becomes

    M0+M1+qLf=Li+(R/k)M0+B(R/k)M1.                   (12)

Both shifts on the right are powers of three larger than Li, and every
literal ternary coefficient on each side is at most2. Thus (12) is a
carry-free equality of coefficients. Viewing each M0/M1 bit as an edge
to its shifted exponent gives one increasing unit path from Li to a
single marker qLf. In particular Lf is a power of three; no terminal
digit promise was supplied.

Before this path first reaches a marker less thanK, it has exactly one
marker L_i in each successive row. It obeys the stronger invariant

    K^2 L_i<R.                                       (13)

Initially Li<A and C>K^3>K^2. A zero edge multiplies the marker by
3/K<=1. A one edge starts at L_i<=A and gives
K^2 L_(i+1)=K*3^a L_i<=K*3^a A<R by the choice ofC.
The new exponents are nonnegative while L_i>=K, so each such edge
advances exactly one row. Let j>=1 be the first short-marker index;
it exists at latest at the terminal marker. For i<j,

    M1_i=s_i L_i, M0_i=(1-s_i)L_i.                    (14)

No claim is made about a legal row structure after that first short marker.

## 5. Signed content rows and their first discrepancy

Write

    b=R/K, z=R/K^2, hK=(K-1)/2.

These are powers of three where appropriate, and b=Kz. The row value
of Jg is hK*b. Let g_i be the ordinary Boolean row of GN and define
the signed integer

    n_i=g_i-hK*b.

This is an exact expansion N=sum(n_i R^i), even when some n_i are
negative. No normalization or Booleanity of N is assumed. Each row satisfies

    -hK*b<=n_i< b/2.                                 (15)

We identify the actual computation inductively through its causal prefix.
Suppose all earlier rows have been identified exactly, and let v_i be
the actual content at the current marker. Then (13) gives

    0<=v_i<(L_i)/2<z/2.

Removing the previous exact scalar transitions from (2) gives its same
form with initial value v_i. Reduction moduloR implies
n_i=v_i-s*b for an integer s. Bounds (15) force

    0<=s<=hK.                                        (16)

The current guard is

    g_i=(hK-s)b+v_i.

Since 0<=v_i<z<b, the high beta-trit block hK-s is Boolean. Subtracting
it from the all-one beta-trit word hK shows that s is Boolean as well.

Let p_i=v_i modK, the actual Boolean deleted prefix. The constant
coefficient n_i-v_i=-sb supplies a residual carry -s. The next coefficient
of (2) therefore gives

    n_i-d_i+UM1_i+s-K n_(i+1)=0 modR.                 (17)

If the following position is the endpoint, n_(i+1) can be replaced by Nf;
only the reduction moduloK is needed in that case. Since b is divisible
byK and M1_i is either zero or a marker divisible byK, (17) yields

    d_i=p_i+s modK.

Both p_i and s lie between0 andhK, so their sum is belowK. Thus

    d_i=p_i+s                                        (18)

without modular wrap. Booleanity of d_i and s implies that the encoded
selector cannot change an actual first symbol1 into0: if both unit
digits were1, the unit digit of d_i would be2. An actual0 can remain0
or become encoded1. As a>=2, the encoded successor length is therefore
at least the actual successor length.

If i=j-1, the encoded successor is short. The actual successor is then
short too, and this actual step halts. Its numerical value need not be
identified with the supplied endpoint or any later encoded row.

It remains to handle i<j-1, when the next guard row exists. Define the
nonnegative integer

    vstar=(v_i-p_i+UM1_i)/K.

The choice C>2KU+3 and (13) imply

    0<=vstar<=v_i/K+UA/K<z/(2K)+z/2<z.                (19)

Equations(17)--(18) imply

    n_(i+1)=vstar-s*z-c_next*b

for some integer c_next, with no sign restriction. The next guard modulo b
therefore equals vstar-s*z modulo b. If s>0, its unique residue is

    (K-s)z+vstar.

The beta-trit block starting at the z-position is K-s>hK, which cannot
be Boolean. This contradicts the next GN mask regardless of c_next.
Hence s=0. Equation(18) then recovers the actual prefix and selector.
The same argument applied to the next row continues the induction.

To be explicit about the transition in the s=0 case, (17) says
n_(i+1)=vstar-c_next*b. It supplies precisely the next inductive initial
value vstar; after removing the exact current transition, the remaining
transport has initial value vstar. Thus the induction does not assume
that a residue class alone identifies the next signed row.

All rows before the final genuine source are identified this way; at that
last source, the length monotonicity argument already proves actual halting.
No upper bound or Boolean promise on Nf is needed for this soundness proof.

## 6. Complete positive converse

Suppose the specified input halts. Use its genuine source words through
the first halt. Choose a power of three A strictly larger than every source
length marker; put R=CA,q=R^t and the usual row-head H. Construct Q,S0,S1,
M0,M1,E,Ebar and the actual content N by their ordinary row formulas.
All eight noncontent fields are Boolean. Each content row has support
below its length marker, hence below A<R/K. Its sum with the top-beta
guard hK*(R/K) is consequently Boolean. This gives GN with exactly the
required value N+jAH.

Take the actual final content and length for Nf,Lf. Their adapters and
the boundary slacks are positive. Choose

    T=(N-S1)/3  if epsilon=0,
    T=(N+2Q)/3  if epsilon=1.

Each row has a nonempty genuine source word, so these are nonnegative
integers; the fixed-branch reconstruction gives exactly N. Both transports
and all paid geometry are satisfied. The first trit of Gstar is1: at an
active first head it comes from Q, and at an inactive first head from S0.

Pack the nine actual Boolean fields, set D0=q^9,
r=P+(D0-1)/2 and betaP=D0-r. Then betaP>0, the unit-two mask valuation
is exact, and every scale bound of the generic44 kernel holds. Its positive
converse supplies all seventeen strictly positive auxiliaries, for either
parity of r. These are fresh witnesses at the new nine-field index; an
old ten-field auxiliary tuple is not transported unchanged.

This proves complete positive encoded-input equivalence. The Boolean N
used in the converse is a chosen genuine witness, not a premise imposed on
arbitrary solutions in Sections2--5.

## 7. Verification boundary

The companion checker expands all20 source comparisons in both fixed
branches, verifies the exact104 count and full positive-coordinate list,
and checks the changed q^9 kernel source and norm correction. Its rational
pre-power tests do not filter for a power radix or typed fields. Separate
signed-chunk and local-borrow tests include altered deleted prefixes and
arbitrary signed next carries. These local tests are evidence for proved
implications, not claimed complete false tuples.

The canonical regression constructs the whole positive outer tuple for
actual halting computations in the same bounded family as generic105,
checks every one of the nine outer equalities and nine masks, and evaluates
the exact new central-binomial valuation. It includes both fixed branches,
both index parities, and zero source/terminal values behind positive adapters.
Huge Pell auxiliaries are supplied by the proved generic converse and are
not materialized. Inputs reaching the simulation cutoff are unclassified.

Neither the fixed compilation padding nor the stronger causal marker bound
is a new charged runtime comparison. They follow from the freely chosen
fixed C and the retained paid source. There is no claim of raw-input
universality or soundness after dropping q=Rv.
