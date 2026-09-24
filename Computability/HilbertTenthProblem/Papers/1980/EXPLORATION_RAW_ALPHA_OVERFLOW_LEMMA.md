# Overflow exclusion without the raw-track aggregate bound

This note proves the preliminary ranges and the packed-word overflow
exclusion needed when deleting the aggregate alpha bound from
`EXPLORATION_PARITY_ALIGNED_RAW_COUNTERS.md`. It does not alone prove that
the six supplied fields recover their native chunks or that the deleted
bound is redundant. Those remaining implications require a separate
field-carry argument. No smaller complete component count is asserted here.

The symbolic inequalities and finite carry checks are reproducible in
`../verification/explore_raw_alpha_overflow.py/.json`. The earlier bounded
search in `explore_raw_counter_alpha_bound.py/.json` is preserved unchanged.

## 1. Hypotheses, with no aggregate bound

Retain the positive raw-counter variables and equations, except for alpha
and F0+F1+alpha=q+J. For a fixed number k>=1 of registers write R=W when
k=1; for k>=2 retain the charged equality W=R^k. Put

    I=2x, S=F0+F1, A=S-2J, delta=Kplus-Kminus,
    P=Kplus+qG0+q^2F0+q^3G1+q^4F1+q^5Kminus,
    L=q^6.

Here Kplus and Kminus denote the supplied native-offset flag coordinates
(called FKplus and FKminus in the source), not already decoded raw flags.
The retained equations used in this note are

    q=2J+1, q=Wv, W=R^k,
    H(R-1)=2J, I+alphaI=R,
    Kplus+Kminus=2J+H=3T,
    G0=F0+T, G1=F1+T,
    W(A+delta)=A-I.                              (1)

All supplied coordinates, x and the input slack alphaI are positive.
The expressions A and delta may be signed. The fixed plus-sign
general-scale Pell kernel is retained with index r=P and scale D0=L.
Its use is justified below before any ternary digits are assumed.

## 2. Pre-power bounds, including q>=9

The input equation gives R>=3. Since q is odd and W divides q, W is odd.
Reducing the last equation in (1) modulo two gives delta even. Because
delta and Kplus+Kminus have the same parity, H is even. Thus H>=2.

Also R divides q and is odd, and

    q=H(R-1)+1>R.

The positive odd integer q/R is therefore at least three. Consequently

    q>=3R>=9, J=(q-1)/2>=4, W>=3,
    0<H<=J, 0<T<=J, 0<Kplus,Kminus<3J.            (2)

These are integer-equation consequences; q has not yet been proved a
power of three. Rearranging time gives

    (W-1)A=-W delta-I.

The positive complementary flags and I>=2 imply

    -delta<=3J-2,
    A <= [W(3J-2)-2]/(W-1)
       =3J-2+(3J-4)/(W-1)
       <=9J/2-4.

Hence, without the removed bound,

    S<=13J/2-4,
    F0,F1<=13J/2-5,
    G0,G1<=15J/2-5.                              (3)

In particular every field below the last q-block is less than 4q, and
Kminus<3q/2. Therefore

    q^5<P
       <(3/2)q^6+4q(1+q+q^2+q^3+q^4)
       <2q^6.                                   (4)

For the last strict inequality, the difference between 2q^6 and the
middle expression is

    [q^6(q-9)+8q]/[2(q-1)]>0                     (5)

for q>=9. Positivity makes the first inequality in (4) strict. Thus
D0=q^6 and r=P satisfy all general-scale kernel conditions:

    D0>=81, r>=27, r<2D0, D0<r^2.

The kernel's parity-independent soundness now proves q is a power of
three and D0 divides binomial(2P,P). This deduction neither assumes
native supplied fields nor assumes P<L.

## 3. The highest-chunk carry lemma

Let q=3^ell with ell>=2, L=q^6=3^N and N=6ell. Suppose

    L<=P<2L, v_3(binomial(2P,P))>=N.             (6)

The ternary expansion of P has leading digit one at position N. By
Kummer's carry formula, doubling P has at least N carries among its
N+1 possible positions 0,...,N. Thus at most one position has no carry.
The carry from position N-1 must be one: otherwise both position N-1
and the leading digit one at position N would have no carry.

Consider the ell digits at positions N-ell,...,N-1, which form the
highest q-chunk below L. If every position carries, each of these digits
is at least one, so the chunk is at least J=(q-1)/2. If the single absent
carry occurs in this chunk, it cannot occur at its last position. Its
digit is zero, and the immediately following digit must be two to restart
the carries. Relative to an all-ones chunk, those two digits change the
value by -3^j+3^(j+1)>0. Every other digit in the chunk is at least one.
The same lower bound follows. Thus (6) always implies

    floor(P/q^5) mod q >= J.                     (7)

The lemma is about normalized digits of the entire packed integer. It
does not identify those digits with any supplied field.

## 4. The final packing carry forces Kplus<=2

Normalize the six supplied fields in base q, starting at the bottom.
Since Kplus<3J<2q, its outgoing carry is at most one. The bounds (3)
then show successively that every carry through either guard or either
base field is at most three. Indeed

    (15J/2-5)+3<4q,
    (13J/2-5)+3<4q.                              (8)

Let c be the carry entering the final supplied Kminus field. Then c<=3
and the mathematical top coefficient is

    floor(P/q^5)=Kminus+c.

If overflow (6) occurred, (7) would give Kminus+c>=q+J. Combining this
with Kplus+Kminus=2J+H<=3J yields

    0<Kplus<=c-1<=2.                             (9)

If Kplus=1, the first two ternary digits of P are 1,0, since q>=9 and
all other packed fields begin at position ell. Doubling already has two
absent carries, contradicting (6).

If Kplus=2 and q>=27, the first three digits are 2,0,0. Their carries
are 1,0,0, again giving two absent carries. It remains only to handle
q=9 and Kplus=2.

## 5. The q=9 boundary also excludes overflow

Now J=4, H<=4, T<=4. The flag sum gives

    -delta=2J+H-4=4+H<=8.

Using I>=2 and W>=3 in the time equation sharpens the bounds to

    A<=[8W-2]/(W-1)=8+6/(W-1)<=11,
    S<=19, F0,F1<=18, G0,G1<=22.                 (10)

There is no carry from the initial Kplus=2 into G0. A guard at most 22
has carry at most two in base nine; a base field plus that carry is at
most 20; the next guard plus carry is at most 24; the next base field
plus carry is again at most 20. Hence the final carry c is at most two.
Equation (9) would now force Kplus<=1, contradicting Kplus=2.

All possibilities in (6) have been excluded. Therefore every accepting
positive solution of the equations in Section 1 and the retained kernel
satisfies

    P<q^6.                                      (11)

The ordinary direct unit-two mask can now be applied in its original
nonoverflow domain: the normalized packed word has only ternary digits
one and two, with unit digit two. Identifying its chunks with all six
supplied coordinates, and recovering S<=3J, remain the explicitly
separate final steps needed for an alpha-deletion theorem.

## 6. Evidence boundary

The checker verifies the rational identities and positive margins in
Sections 2 and 4 symbolically. It exhaustively checks the highest-chunk
lemma for every L<=P<2L with L=3^N and 2<=N<=9, and every chunk length
1<=ell<=N. It also checks every positive split F0+F1<=19 with T=1,...,4
for the q=9 final-carry bound. These tests corroborate the general proof;
their finite range is not substituted for any step of the argument.
