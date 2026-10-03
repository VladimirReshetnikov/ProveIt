# Raw Boolean ternary fields and smaller finite NAND relations

The changed kernel in [Boolean FIFO60](input_bridge_boolean_ternary60.md)
also gives **55=28M+27A** for four independent positive Boolean ternary
fields. Replacing its joint bound by four individual bounds keeps the
cost and removes the restriction on their sum. A separate three-field
checksum gives **53=27M+26A** for three nonempty one-hot streams at an
even number of positions, with no prescribed first label.

The latter interface gives an exact **64=33M+31A** cyclic NAND relation
and an exact **71=35M+36A** relation with paid noncommuting routing.
These improve the earlier finite66/73 components by two operations.
They retain significant restrictions: every selector occurs, the length
is even, and supplied routing quotients are positive. They do not provide
ordinary-input loading, arbitrary circuit wiring, or universal acceptance.
The complete universal bound remains76.

## 1. Four independent Boolean fields in55 operations

Use the changed44-operation kernel from Boolean60, with X=wq, Y=3s+1
and exactly its ten equations. Supply four positive fields Fi and add

    r=F0+qF1+q^2F2+q^3F3,
    r+bound_beta=X,
    Fi+alpha_i=q  for i=0,1,2,3.                       (1)

Horner packing costs6, the bound on X costs1, and the four individual
bounds cost4. The full source costs55, with16 equations and22 auxiliary
positive coordinates besides q and the four fields.

Its exact projection is q=3^t with t>=1, four positive length-t ternary
words whose digits are0/1, and even sum F0+F1+F2+F3. There is no joint
sum bound. For example q=9 and all Fi=3 satisfy this predicate although
their sum12 exceeds q.

The changed lower endpoint needs a fresh bootstrap. Before power recovery,
(1) gives q>=2, Fi<q, and

    q^3+q^2+q+1 <= r < q^4, r>=15, X>r, Y>=4.

Thus E=XY>r+1, a=Y(X+1)>2r+1, and P=2XY^2+1>A=a+3.
The first index n is r+1 modulo E and is at least r+1. The main
index satisfies p>=n+1>=r+2>=17. In particular

    c>(2A-1)^(p-1)>A(A^2-1)^2,
    c>Y(r+1)>2r+1, c>2p.

These are the relaxed-rank and half-parameter thresholds. An even q is
impossible already at the main norm: X even and d=X+ac+ga(6a+8) give
d=ac modulo2, while Delta=a^2+6a+8=a^2 modulo2. Then
d^2-Delta*c^2=0 modulo2 contradicts its value1. Consequently q>=3
and r>=40, strengthening the thresholds; this argument does not assume
Y even or q divides Y.

Apply the reviewed rank recovery to obtain p=2r+1 and n=r+1. The
signed positive-branch theorem also gives even r. As in Boolean60, use
the lower ratio first: 6XY^2>a yields

    c/k > ((X+1)^(2r)/X^r), Y>=X^r, a>X^(r+1).

The direct exponent recurrence gives X=3^(2r+1) modulo6a+8. Since
X>r>=40 and 3*9^r<X^(r+1)<a, both representatives are smaller than
the modulus, so equality holds. Thus q=3^t. The reviewed upper ratio
and fractional-tail bounds then give

    Y=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j.

Y=1 modulo3 forces zero ternary doubling carries in r. Because Fi<q,
the base-q packing has no field carries, and all Fi are Boolean ternary
words. Odd q gives r=sum Fi modulo2. This proves necessity.

Conversely, a tuple in the stated predicate has a Boolean ternary packed
word r with an even number of ones. Lucas's coefficient calculation gives
binom(2r,r)=1 modulo3. Take X=3^(2r+1), Y equal to the displayed floor,
w=X/q, s=(Y-1)/3, bound_beta=X-r and alpha_i=q-Fi. All are positive
integers. The exact positive map of Boolean60 Section3 supplies all
remaining coordinates. Its ratio and congruence arguments only concern
X,Y,r, and the lower thresholds above suffice. This proves the complete
positive converse, including the endpoint q=3, Fi=1, r=40.

## 2. Three nonempty raw selectors in53 operations

Supply q,F0,F1,F2,Hrep and the same changed kernel, with

    r=F0+qF1+q^2F2,
    r+bound_beta=X,
    F0+F1+F2=Hrep, q=2Hrep+1.                         (2)

Packing costs4 and the X bound1. Compute

    Dword=F0+F1, total=Dword+F2,
    twice_H=Hrep+Hrep, q_calc=twice_H+1,

then compare total=Hrep and q_calc=q. These4 additions give total53,
with14 equations and19 positive auxiliaries besides q,F0,F1,F2.

Here Hrep>=3, q>=7, Fi<q and r>=q^2+q+1>=57, so every bootstrap
bound in Section1 holds. The changed kernel proves that Fi are Boolean
ternary words and r is even. Power recovery makes Hrep=(3^t-1)/2.
At a first possible nonzero residual in sum Fi-Hrep, the digit belongs
to[-1,2], which contains no nonzero multiple of3. Induction excludes
every carry, and exactly one selector is1 at every position. Further,
r=sum Fi=Hrep modulo2, so Hrep even and hence t even. Positivity of
all three selectors forces t>=3, therefore **t is even and t>=4**.

Conversely any partition of an even positive length into three nonempty
labels gives (2). Its packed r is even, so the positive kernel map above
applies. This proves the exact selector projection. There is no first-bit
condition on any Fi. Empty selector classes are excluded, not silently
represented by zero supplied coordinates.

## 3. Exact cyclic NAND in64 operations

Retain (2), so D=F0+F1 is already computed and is Boolean. Compute

    twice_F2=F2+F2, S=F1+twice_F2, ports=A+B.

At a position with label0,1,2, respectively, D is1,1,0 and S is0,1,2.
Thus for Boolean A,B, equality A+B=S is precisely the NAND relation
D=NAND(A,B), retaining the selectors as its exact input-count labels.

Supply positive R0,R1,A,B,K0,K1,Z0,Z1 and impose

    A+B=S,
    R0*A=D+(q-1)K0, q=R0*Z0,
    R1*B=D+(q-1)K1, q=R1*Z1.                          (3)

Use twice_H for q-1. Each rotation needs two products and one sum for
transport and one factorization product:4 operations. The three gate
additions and two rotations add11 to53, giving64, with19 equations and
25 positive auxiliaries besides q,F0,F1,F2,R0,R1.

The bounds used for routing precede port typing. Since A,B>0 and
A+B=S<=q-1, each port lies strictly between0 and q-1. The factorization
forces Ri=3^ai, 0<=ai<=t. Modulo q-1, Ri is invertible. The unique
representative in that interval is the genuine cyclic right rotation

    rot_ai(D)=floor(D/Ri)+(q/Ri)*(D mod Ri).

It is Boolean because D is Boolean and 0<D<Hrep. Thus the NAND
interpretation is sound. Its positive quotient is exactly Ki=D mod Ri;
in particular ai=0 is excluded, and other rotations with zero low
prefix are excluded too. The identity rotation ai=t has Ki=D>0.

These conditions also give all positive converse coordinates: take each
port to be the stated rotation, Ki=D mod Ri, Zi=q/Ri, and extend the
selector tuple with its positive kernel map. The exact projection is the
finite NAND fixed-point relation with these prefix and selector conditions.
The earlier commuting-permutation collapse still applies. This source
does not circumvent that mathematical limitation by saving operations.

## 4. Paid noncommuting routing in71 operations

Keep (2), the two instructions forming S, and replace (3) by

    D=3E+1, q=3Q,
    Q=R0*Z0, C+Jbound=Q,
    R0*C+(Q-1)=E+(Q-1)K0,
    A=C+Q, A+B=S,
    R1*B=D+(q-1)K1, q=R1*Z1.                         (4)

A is derived. The supplied additional coordinates are positive
E,Q,C,Jbound,B,K0,K1,Z0,Z1, with R0,R1 as parameters. The complete
literal suffix has18 operations:8 multiplications and10 additions or
subtractions. Total71 has22 equations and28 positive auxiliaries.

This is the exact routing proof from
[the previous73 component](native_controller_noncommuting73.md), with
the selector interface replaced. For clarity, D=3E+1 and nonempty F0,F1
give E>0 and E<=(Q-1)/2. The explicit bound0<C<Q, the factorization
R0=3^a, and the transport modulo Q-1 force

    C=rot_a(E), K0=1+(E mod R0)>0, 0<=a<=t-1.

Consequently A is Boolean: its lower t-1 digits are the rotation of D's
tail and its top digit is D's known units1. The gate sum bounds B before
the second residue argument, which gives B=rot_b(D), 1<=b<=t and
K1=D mod R1>0. The latter positivity is automatic because D has units1.
All converse coordinates are the same explicit positive quotients and
slacks. The condition C+Jbound=Q is retained; it is not a free bound.

The precise permutation on digits d=(1,d1,...,d_(t-1)) is

    P_a(d)=rot_a(d1,...,d_(t-1)) followed by1.

Thus (4) is exactly d=NAND(P_a(d),rot_b(d)), with the three nonempty
input-count classes, even t, and all positive-domain conditions above.
Unlike the older selector, this source does not require both input
units digits to be0: label1 at the origin is also permitted.

A concrete admitted instance has

    t=8, a=b=3,
    d=(1,0,0,0,1,1,1,1),
    A=(1,1,1,1,0,0,0,1), B=(0,1,1,1,1,1,0,0),
    labels=(1,2,2,2,1,1,0,1).

The checker gives every positive outer coordinate, checks (4), and checks
P_a rot_b(d) differs from rot_b P_a(d). This is an admitted noncommuting
relation, not a universal routing compiler. The finite-defect bound in
the previous73 note applies unchanged and makes no uniform universality
claim for variable offsets.

## 5. Evidence and scope

The [source checker](native_controller_raw_boolean_gates.py) expands every
comparison against independent polynomials, including the inherited
auxiliary-norm correction, for all four literal schedules. It exhausts
arbitrary individually bounded fields, checksum triples including
non-Boolean ones, and positive untyped routing ports before comparing
with the semantic permutations. The saved
[receipt](native_controller_raw_boolean_gates.json) records these counts.
There are327,369 pre-power tuples, 9,640,080 positive cyclic-port tuples,
and1,945,770 positive tail-routing tuples. The port sweeps use lengths4
and6 and find no admitted tuple with all three labels nonempty; the
separate length-eight examples prove both finite relations nonempty.
The displayed positive maps use the proved changed-kernel converse;
astronomically large Pell coordinates are not materialized.

Independent full proof, source, and default-replay review passed. The changes concern native typing and
finite cyclic constraints only. No source here supplies a complete
universal certificate below76.
