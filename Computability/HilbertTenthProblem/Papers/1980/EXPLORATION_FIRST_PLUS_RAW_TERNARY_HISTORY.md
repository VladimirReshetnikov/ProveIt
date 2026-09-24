# A 79-operation raw counter history with an initial increment

Reordering the six fields of the raw mixed-counter history exposes a
control bit to the direct unit-two mask. This removes three operations
while requiring the first transition to be +1. The complete system has
**79 operations: 40 multiplications and 39 additions/subtractions**,
32 positive unknowns and 22 equations. The raw input I may be any
nonnegative integer, including the literal zero; the positive output
parameter Fplus represents F=Fplus-1.

The exact schedule, fresh source comparisons and finite receipt are
`../verification/explore_first_plus_raw_ternary_history.py/.json`.
The 82-operation predecessor remains unchanged in
`EXPLORATION_RAW_TERNARY_MIXED_HISTORY.md` and its companion checker.
This is a counter-history component, not a universal program verifier.
Its first-increment condition is part of the proved relation, not an
uncharged assumption or a silent choice of kernel parity.

## 1. Full source and new packing

The fourteen outer positive unknowns are

    q,F0,F1,T0,T1,FKp,FKm,J,alpha,W,H,T,v,alphaI.

The checker calls J `Jrep`. The eighteen retained positive unknowns are
a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux,u. Mathematical
abbreviations S=F0+F1, A=S-2J and delta=FKp-FKm can be signed before
decoding; they are charged arithmetic registers, not extra positive
unknowns. The ten non-kernel outer equations are

    q=2J+1,                                      (1)
    F0+F1+alpha=q+J,                             (2)
    T0=F0+T, T1=F1+T,                           (3)
    q=Wv, H(W-1)=q-1,                           (4)
    FKp+FKm=2J+H,                               (5)
    3T=2J+H,                                    (6)
    I+(W-1)(S-2J)+W(FKp-FKm)+q=qFplus,           (7)
    I+alphaI=W.                                  (8)

The two double displays (3),(4) each comprise two equations. The eleventh
outer equation uses the new order

    P=FKp+qT0+q^2F0+q^3T1+q^4F1+q^5FKm,
    r=P, D0=q^6.                                (9)

Append the eleven-equation parity-free kernel of
`EXPLORATION_PARITY_FREE_PELL_KERNEL.md`, with inputs D0,r. Explicitly,
put U=wD0, Y=sD0, Q_pell=UY^2, Delta=(a+3)^2-1, J_pell=2r+1. Its
equations are

    Q_pell(Q_pell+1)k^2=tau(tau+1),
    c=Yk+eta, k=eta+zeta, k=r+1+hUY,
    a=Y(U+1), d=U+ac+gamma(6a+8),
    d^2=1+Delta*c^2, (ic^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)(u^2-y_aux^2)=1-y_aux^2,
    u^2=J_pell^2+jc, u^2=c^2+of.                (10)

There are thus twenty-two source equations. The schedule shares 2J
with the row geometry; its actual geometry residual is the displayed
one plus q-2J-1. The other acyclic source adjustment is the relaxed
norm residual times u^2-y_aux^2. All source comparisons, including the
changed scale and packed word, are checked symbolically.

## 2. New pre-mask range, with no digit assumptions

Positivity gives q>=3, S<=3J and each F_i<3J. The positive row relation
H(W-1)=2J excludes W=1, including when I=0. Since q is odd and W
divides q, W>=3, and hence 0<H<=J. Thus

    FKp+FKm=2J+H<=3J,
    0<FKp,FKm<3J,
    0<T<=J, 0<T0,T1<4J<2q.                     (11)

Group the new word using T_i=F_i+T:

    P=FKp+q^5FKm+(q+q^2)F0+(q^3+q^4)F1
         +T(q+q^3).

The two positive pair bounds give

    q^5<P
       <=1+(3J-1)q^5+q+q^2+(3J-1)(q^3+q^4)
            +J(q+q^3)
       <3(q^6-1)/2.                             (12)

After J=(q-1)/2, the gap between the final bound and the middle
upper expression is exactly

    (q-1)(2q^4+3q^3+9q^2+6q+5)/2>0.

For r=P and D0=q^6, these are stronger than all hypotheses of the
general-scale parity-free kernel:

    D0>=729>=81, r>q^5>=243>27,
    r<3D0/2<2D0, D0<r^2.

The kernel first recovers U=3^(2r+1) and D0 dividing binomial(2r,r).
Consequently q is a power of three. There was no prior field typing,
power-of-three assumption or parity promise in this argument.

Write q=3^ell. The existing geometry proves W=3^m and ell=mt for
m,t>=1. Then q=W^t, H=1+W+...+W^(t-1), J=((W-1)/2)H and
T=(W/3)H. These facts are available before the native field argument.

## 3. Decode the new lowest flag before the guard pairs

The direct unit-two theorem in `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`
applies to (12): with L=q^6=3^(6ell), divisibility by L forces

    P<L, P mod3=2, every ternary digit of P is one or two. (13)

The overflow window is important here. If L<=P<L+(L-1)/2, the highest
zero below the extra leading one stops the doubling carry and at least
two positions fail to carry, giving valuation below 6ell. Thus (12)
justifies (13) without first assuming P<L.

Each native q-chunk is between J and q-1. Since FKp<3J, a lowest
field FKp>=q would have remainder at most J-2, impossible. Hence FKp
is below q and native, with no carry entering T0.

Now T0<4J<2q. If it were at least q, its native remainder would require
T0>=q+J, and a carry one would enter F0. Native decoding of that next
chunk, with F0<3J, forces F0<=q-2: F0>=q would leave a remainder at
most J-1, and F0=q-1 would leave zero. But T<=J then gives
T0=F0+T<=q+J-2, contradiction. Thus T0<q, and the elementary no-carry
chunk argument also gives F0<q. The identical reasoning handles T1,F1.
The final FKm<3J is native and below q as well.

All six supplied fields therefore equal their native q-chunks. In
particular FKp has unit digit two by (13). Since J has unit digit one,
the raw plus-control word Kp=FKp-J has unit digit one. Thus the first
row is forced to choose +1 by the mask itself.

## 4. Ordinary numerical values and exact mixed time semantics

Define the raw Boolean words A0=F0-J, A1=F1-J, Kp=FKp-J and
Km=FKm-J. Equation (5) gives Kp+Km=H digitwise, so exactly one sign
appears at each row head and nowhere else. Write

    delta=Kp-Km=sum epsilon_j W^j,
    epsilon_j in {-1,+1}, epsilon_0=+1.

The native guards T_i=F_i+T imply that A_i has zero at every highest
row digit. At the first overlap, adding the one from T to a native two
would create digit zero, contradicting the native guard. With no overlap
all additions are carry-free. Thus each row a_j of A=A0+A1 is an ordinary
ternary integer in [0,W/3-1]. Digits two arise as 1+1 across the tracks.
This is the number a_j itself, not a binary value encoded by ternary bits.

Put F=Fplus-1>=0. Expanding (7) gives

    (I-a_0)
      +sum_(j=1)^(t-1)(a_(j-1)+epsilon_(j-1)-a_j)W^j
      +(a_(t-1)+epsilon_(t-1)-F)W^t=0.

By the paid input bound, 0<=I<W. The unit coefficient has absolute value
less than W, so it is zero. Every interior coefficient has absolute value
at most W/3<W, so successive division and reduction modulo W prove

    a_0=I, a_j=a_(j-1)+epsilon_(j-1),
    F=a_(t-1)+epsilon_(t-1).

All a_j and F are nonnegative. There is no decrement of zero, modular
wraparound or cross-row borrow. The final F may equal W/3 after a final
increment, although all stored source rows are smaller; this endpoint
is deliberately included.

The exact relation is a finite nonnegative +/-1 walk from raw I to
Fplus-1, with positive length and first sign +1, recorded by the typed
control fields. The existential finite width can be chosen large enough
for any such walk. Without a separate program relation choosing the
signs, the endpoint predicate is decidable and carries no universality
claim. An existing walk whose first sign is minus is not accepted as
that same trace; prepending an increment/decrement pair gives another
walk with the same endpoints, but such preprocessing is a separate
control convention in any program composition.

## 5. Full positive converse and exact cost

Given such a walk, choose W=3^m with all its values below W/3, set
q=W^t, and form H,J,T,v. Split the ternary digits of every source row
into two Boolean tracks with a zero highest digit. Construct the two
head-control words and add J to every masked field. All six native
fields are positive, even when a raw track or control is zero.

Since A<= (W/3-1)H<=J, choose alpha=q+J-(F0+F1)>=1 and
alphaI=W-I>=1. Every outer equality holds. The first sign plus makes
FKp's unit digit two, so the new packed word has unit two and otherwise
native digits. Its direct mask gives D0-divisibility. Bounds (12) give
all kernel hypotheses. The parity-free positive converse constructs all
remaining Pell auxiliaries for the new r=P,D0=q^6, regardless of r's
parity. They cannot simply be reused from the older scale/index.

The ten outer equations take 22 operations and the Horner word takes
ten. Three products compute q^2,q^4,q^6. The kernel takes 44 operations.
Thus the total is 22+10+3+44=79=40M+39A. Relative to 82, scale3L,
index3P and its final addition of two have disappeared; field typing
has instead imposed the explicit first-plus condition. Fixed numerals
and equality comparisons have the existing free convention.

The finite receipt covers 8,315 positive pre-power tuples, 48,684 complete
scalar candidates with 21 accepted traces, and 1,697 canonical first-plus
histories. Those include 47 zero-input, 19 zero-output and 20 final-at-guard
cases, with 573 odd and 1,124 even indices. It also checks rejection of
1,685 valid predecessor traces beginning with minus. These tests support
the general proof; no enormous full Pell tuple is numerically instantiated.
