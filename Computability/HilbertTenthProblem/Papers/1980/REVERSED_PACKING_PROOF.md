# Reversed packing and a self-checking quotient

This construction is derived from the frozen 112-operation direct quadratic
certificate. The proof below establishes its mathematical equivalence;
`../verification/round7_1980_certificate.py` supplies its exact 111-operation
primitive and polynomial-residual check.

## Fixed index and equations

Keep the quadratic rows, Sidon variable weights, target positions, and polynomial
`D(B)` of `QUADRATIC_MASK_PROOF.md`. Write `t_*` for the largest target position,
`L=5^16`, and `K=t_*+1`. The fixed values satisfy the stronger support margin
`L>3K+2`. Every coefficient of `D`
lies strictly between `-z` and `z`, where `Z=2z` is a power of two and `z>=2`.
Replace the dense coefficient code by

    e_0(B) = z sum_{j=0}^{K-1} B^j + D(B).

Its digits are in `[1,Z-1]` and its degree is at most `t_*`. The support/target
code `ell_0(B)` is unchanged and also has degree `t_*`. The new packed index is

    V = ell_0(Z) + e_0(Z) Z^L.

Choose the fixed power of two `H` greater than all the previous bounds and also

    4 Z 1890^2,   2^(t_*+4) Z 1890^2.

These choices depend only on the represented set, not on the queried positive
integer `x`. All earlier support inequalities remain unchanged.

Retain `B=H b^2`, `C=1+xB+g`, `theta=B-Z`, and

    lambda(B-1)=q^2-1,       n=q^8.

The two changed packing equations use

    Y = ell + e q,
    Y + C^2 + alpha = q^2,
    Y = V + t theta.

Define the already computed third-block expression by

    S_3 = (2e-Z lambda) C^2 + B lambda(1+q).

Introduce one positive unknown `sigma` and the free equality `sigma=S_3`.
Finally replace the packing expression for `r` by

    S = g + q^2(Y+q^2 S_3),
    T+1 = q^2(1+theta lambda) - (b-1)ell + (B-2)ell q^4,
    r = S(n^2-n)+(T+1)(n^2-1).

Every other equation of the frozen 112-operation system is retained. In
particular the Pell equations still have their proved positive-domain meaning.

## Noncircular bounds before the Pell implications

All variables declared positive remain positive. The new inequality implies

    ell < Y < q^2,   e < q,   C < q,   g < q.

Since `C>B`, this gives `q>B`. We have `b>=2`, `B=Hb^2`, and `B>2Z`. Consequently

    q < lambda < 2q^2/B,
    b < N := theta lambda < q^2-1.

The imposed positive unknown gives `S_3>0`. Its upper bound follows without
decoding: since `e<q` and `C^2<q^2`,

    S_3 < 2q^3 + B lambda(1+q) < 5q^3 < q^4.

Here `q>5` follows from the fixed lower bound on `H`. Thus `S` occupies blocks
of widths `q^2,q^2,q^4`, and `0<S<q^8=n`.

The first raw mask `q^2-1-(b-1)ell` is not assumed nonnegative. The complete
quantity `T+1` is nevertheless positive: `N>b` and `ell<q^2` imply

    q^2(1+N)-(b-1)ell > q^2.

Also `(B-2)ell<q^3`, so

    0 < T+1 < q^7+q^4+q^2 < q^8.

It follows that `0<=T<n` and `r>=n^2-1>=n`. The usual hypotheses for the
existing Pell implications are now available. Those implications therefore
give `q=B^L`, the required powers of two, and the binomial no-carry condition
`tau_2(S,T)=0`. This stage used neither decoding nor positivity of the first
raw mask.

## Removing the possible first-block borrow

Put

    d = floor((b-1)ell/q^2),
    u = (b-1)ell-dq^2.

Then `0<=d<b`, `0<=u<q^2`, and the actual base-`q` block decomposition is

    T = (q^2-1-u) + q^2(N-d) + q^4(B-2)ell.

The middle block remains in `[0,q^2)` because `N>b`. Since `q=B^L`, the
base-`B` digits of `N=(B-Z)lambda` are all `B-Z` in positions `0,...,2L-1`.
As `d<b<B-Z`, subtracting `d` changes only its unit digit. Therefore the
middle no-carry condition implies that all nonunit base-`B` digits of `Y`
are less than `Z`, while its unit digit is at most `Z+d-1`. In particular

    Y < Z q^2/(B-1) + b.

Since `ell<Y`, we obtain

    (b-1)ell < (b-1)Z q^2/(B-1) + b(b-1) < q^2.

For the last inequality one may use `B-1>4(b-1)Z` and `q>4b`, both immediate
from the stated lower bounds on `H`. Thus `d=0`. All digits of `Y` are now
less than `Z`, and the ordinary digit-evaluation lemma applies to the packed
congruence. It gives

    Y = ell_0(B) + e_0(B) q.

Since `0<ell_0(B)<q` and `e>0`, there is an integer `m` satisfying

    ell = ell_0(B)+m q,    e = e_0(B)-m,    0<=m<e_0(B).

The rest of the proof shows that the third mask forces this apparent quotient
ambiguity to vanish.

## Decoding the low coordinate positions

The fixed support bound gives `(b-1)ell_0(B)<q`. The low `q` block of the first
mask is consequently `q-1-(b-1)ell_0(B)`. Since `g<q`, the first no-carry
condition forces the base-`B` digits of `g` to occur only at the unchanged
support positions, with every digit less than `b`. In particular the extra
positions of `m q` cannot acquire coordinates: they are all at or above `L`.

Hence `C` has degree at most `t_*`, its constant digit is `1`, and its input
digit is exactly `x`. If `A` is the sum of the coefficients of `C^2`, then

    A = C(1)^2 < 1890^2 b^2,     ZA < B/4.

Both `e` and `m` have at most `K=t_*+1` base-`B` digits, since they are smaller
than `e_0(B)`. The decoded `C` also has at most `K` digits, each less than
`B`. Hence `e,C<B^K` and

    2eC^2 < 2B^(3K) < B^L=q.

This uses the explicitly checked margin `L>3K+2` and bounds the actual integer,
so carries in multiplying `e` and `C^2` do not require a separate degree
assumption. Its entire contribution lies below the high mask positions.

## The high mask forces the quotient ambiguity to be zero

Let

    X=(B-2)m = sum_{j=0}^{t_*+1} X_j B^j,   0<=X_j<B.

Since `(B-2)ell_0(B)<q`, the digits of the third mask at positions
`L,...,L+t_*+1` are exactly the digits `X_j`.

At all these positions the coefficient of `lambda C^2` is the constant `A`:
the window is above `2t_*` and below `2L`. The positive term `2eC^2` has ended
strictly below this window. The offset `B lambda(1+q)` has coefficient `1`
at position `L` and coefficient `2` at positions `L+1,...,L+t_*+1`.
Normalize the nonnegative integer `2eC^2` first; it has no digit at or above
`L`. The remaining raw coefficients below `L` are bounded below by `-ZA`,
so the incoming carry at `L` is at least `-1`. The positive part below `L`
is less than `q+q/(B-1)<2q`, so that incoming carry is at most `1`.
As `ZA>=4`, the raw coefficient `1-ZA` plus any of these possible incoming
carries is negative, and its normalized digit is between `B-ZA` and
`B-ZA+2`. Its outgoing carry is exactly `-1`. Thus the actual digits are

    in [B-ZA,B-ZA+2]     at position L,
    B-ZA+1               at positions L+1,...,L+t_*+1.

The outgoing carry remains `-1` throughout this window because
`4<=ZA<B/4`. No carry enters from a higher position. The lower bound
`B-ZA` is all that is needed.

The third no-carry condition therefore implies

    0<=X_j<=ZA-1  for every j.

Apply the elementary digit polynomial `F(T)=sum X_j T^j`. Since
`F(B)=X=(B-2)m`, the integer `F(2)` is divisible by `B-2`. But

    0 <= F(2) < ZA 2^(t_*+2)
                 < Z 1890^2 b^2 2^(t_*+2)
                 < B/4 < B-2.

Thus `F(2)=0`. Its coefficients are nonnegative, so every `X_j` is zero;
hence `m=0`. We have recovered both canonical codes

    e=e_0(B),    ell=ell_0(B).

All third-mask positions are now below `K`. In this range
`e_0-z lambda=D`, and the offset gives the same zero-coefficient tests as in
the direct quadratic proof. Its support-separation argument therefore forces
every original quadratic residual to vanish.

## Necessity and arithmetic cost

Given genuine witnesses, use the unchanged coordinate encoding, choose one
unused dummy coordinate to be `1`, and take a sufficiently large power of two
`b`. Set `e=e_0(B)` and `ell=ell_0(B)`. Their degrees are at most `t_*`, so

    Y=ell+eq < q^2,       Y+C^2<q^2,

with a strictly positive slack; the large gap `L>3t_*+1` makes the latter
inequality immediate from the fixed coefficient bounds. Also `ZC^2<q`, so

    S_3 >= lambda(B(1+q)-ZC^2) >0.

The digit-evaluation congruence has a positive quotient because `B>Z` and
the packed polynomial has positive nonconstant coefficients. All three masks
then have their intended no-carry values. The preceding Pell necessity
constructions supply the remaining positive unknowns, and one sets
`sigma=S_3`.

Relative to 112 operations, replace the product `ell*C^2`, the addition of
`e`, and the addition of the positive slack (three operations) by `Y+C^2`
and the addition of the slack (two). Computing `Y=ell+e*q` has the same cost
as the old order. The two packing shifts use `q^2` and the third mask uses
`ell*q^4`, so both retain their previous costs. Replacing `1+q^2` by `1+q`
has equal cost. The new positive unknown is connected to the existing `S_3`
register by a free equality test. The exact checker gives 111 arithmetic
operations (61 multiplications and 50
additions), 33 positive unknowns, and 21 equations. Generating the fixed
numerals from `1` adds the same seven instructions as before, for 118 operations.
