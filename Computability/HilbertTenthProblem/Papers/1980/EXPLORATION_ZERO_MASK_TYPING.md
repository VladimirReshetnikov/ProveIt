# What the zero-mask convolution does and does not type

The serial counter zero mask is

    R=3^m, q=R^u, H=(q-1)/(R-1),
    top=(R/3)H, rep=(R-3)/6,
    T=top+rep*Z.                                  (1)

Here m>=2. The existing complete component types the raw zero-event
word Z as a Boolean subset of H using two native flag fields. This note
examines whether typing T instead could remove those fields. It records
exact counterexamples both with Boolean Z and with only nonnegative Z.
These invalidate the proposed support-typing implications. No smaller
complete certificate is claimed.

The independent finite checks are
`../verification/explore_zero_mask_typing.py/.json`.

## 1. Boolean Z is insufficient once the block has three digits

Call an integer Boolean when every ternary digit is zero or one. Take
m=3, R=27 and any u>=3. Set

    Z=120=3+9+27+81.

This Z is Boolean but has off-head bits at positions one, two and four.
Nevertheless (1), with rep=4, gives the exact identity

    T=3+27^2+9*sum_(j=2)^(u-1)27^j.               (2)

Thus T is Boolean and 0<T<=J=(q-1)/2. Also Z<=H. In the smallest case
u=3, q=19683, H=757, J=9841 and

    top=6813, T=7293=3+729+6561.

Both native adapters J+Z and J+T are valid. Therefore even retaining a
native FZ while replacing its complementary field by a native FT does
not establish head support.

The first invalid interval begins at position one. Its next start is
exactly at position two, coinciding with the fixed top bit. Three ones
there normalize to zero and a carry. The successive coefficients at
positions three, four and five are each two plus that incoming carry;
they also normalize to zero. The carry ends as a one at position six.
No coefficient two survives to reveal the malformed support. A proposed
first-overlap proof failed by overlooking the simultaneous third term
at the top position.

This family also meets the later parity conveniences. At u=6 it has
q=387420489, H=14900788, J=193710244 and T=134107572. Here H,J,Z,T are
all even, u is a multiple of three with even quotient, and m is odd.
These facts do not turn it into a complete controller counterexample,
but rule out repairing the standalone typing lemma just by imposing
those parity or complete-bank conditions.

The forward construction remains valid: any Boolean head subset Z
does produce Boolean T<=J, by disjoint block intervals. For the special
case m=2 the reverse also holds when Z is Boolean, because rep=1 and
adding the two Boolean words top and Z cannot carry: their overlap
would have digit two. In two-digit blocks the only forbidden positions
are precisely the fixed top positions. This restricted fact does not
support an unbounded counter-width construction.

## 2. A closed counterfamily for every block width m>=3

The failure is not confined to small widths. For any m>=3 and u>=m put

    Z=4*3^(m-2)*sum_(n=0)^(m-2)3^(n(m-1)),
    D=m(m-1)-1.

The two one digits of 4=1+3 make Z Boolean: its support consists of
the disjoint pairs

    m-2+n(m-1), m-1+n(m-1),       0<=n<=m-2.

In particular it has an off-head bit at m-2. Its highest position is
(m-1)^2, strictly below the highest head position m(u-1), and Z<H.

The convolution has a simple telescoping evaluation:

    rep*Z
      =[(3^(m-1)-1)/2]*4*3^(m-2)
         *[(3^((m-1)^2)-1)/(3^(m-1)-1)]
      =2*3^D-2*3^(m-2).

Subtracting 2*3^(m-2) from top borrows from its first bit at m-1,
leaving a single bit at m-2. The top mask also has a bit at D: adding
2*3^D removes that bit and inserts a bit at D+1=m(m-1). Therefore the
normalized value is exactly

    T=3^(m-2)+3^(m(m-1))
        +sum_(j=1)^(u-1), j!=m-2 3^(mj+m-1).      (3)

Every displayed position is distinct and below mu, so T is Boolean
and T<=J. Formula (3) has u one digits; Z has 2(m-1) one digits. Taking
u to be any multiple of six at least m makes H,J,Z,T all even, gives
whole three-register banks with even bank duration, and keeps both
J+Z and J+T native. The exponent m can exceed any fixed program-width
threshold, while R remains divisible by its fixed power-of-three
minimum. Thus width enlargement and these parity conditions cannot
repair the support-typing implication.

## 3. The stronger nonnegative-Z statement is false

Take

    m=3, R=27, u=2, q=729, H=28, J=364,
    top=252, rep=4, Z=18, T=324.

Then

    T=252+4*18=324=3^5+3^4

is Boolean, positive and at most J. However Z=18 has ternary digit two
at position two and is not one of the head subsets {0,1,27,28}.
The counterexample even satisfies the scalar bound 0<=Z<=H.

Its carry mechanism is explicit. The term 4Z has coefficient two at
positions two and three. At position two it adds to the top bit, making
three, which normalizes to zero and a carry. At position three the two
plus that carry again make three. The carry terminates at position four
as a one; the original top bit at position five remains one. Thus the
normalized T is Boolean despite the malformed zero-event digit.

The native adapter FT=J+T=688 is also valid. Replacing a raw event by
the positive adapter Zplus=Z+1=19 therefore does not repair the lemma.
Both Z and T happen to be even, so a parity restriction does not repair
this example either.

## 4. Scope of the rejected shortcut

One proposed replacement removed both native zero flags, supplied
Zplus=Z+1, and masked only FT=J+T. The same subtraction would compute
Z=Zplus-1, while one adapter addition replaced the old complementary-flag
addition. One fewer Horner field would save a product and an addition;
changing the scale chain from q^12 to q^11 would cost one extra product.
This suggested a net one-operation saving, conditional on the false
nonnegative-Z typing lemma.

Sections 1--3 invalidate that proof route. They are counterexamples to the
standalone typing implication, not a claimed full positive solution of
the modified controller/Pell system. Whether other equations could
exclude every malformed event is a separate unresolved question.

Keeping the old native FZ field while replacing its native complement
by FT has the same arithmetic and field count, and Section 1 defeats
its proposed support proof as well. No frozen source or article was
modified for either proposed substitution.
