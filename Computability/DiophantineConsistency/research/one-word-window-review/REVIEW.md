# Independent ordinary review of the one-word window proposal

The alpha=1 proposal cannot work with the retained mask/population interface.
There is a short universal obstruction, before the transport congruence is
used. This is stronger and more precisely scoped than the brief's group-based
heuristic. It does not rule out every one-word compiler, a different rank or
population calibration, or a different deterministic expression for alpha.
No nine-positive compiler, equation, operation count or degree is established
by this review. No incoming program, compiler, checker or Lean command was
executed. Only ordinary proofs, literal recipes and fixed file bytes were read.
The frozen source packets and the brief itself are unchanged by this review.

The reviewed brief is the version at commit
76f2647cdf1c91b38e4c30d75fb791f0ff918b5e, SHA256
3275ac4570aac12d2fb2a26c8fa7d5543424dfc37e984bbbfa8cf10754dd81c4.
SOURCE_PINS.json records the precise supporting proof/recipe bytes.

## 1. A finite-word obstruction that is decisive for alpha=1

Let u>=1, Q=2^u and M=Q-1. All bitwise complements in this section are
restricted to the u positions0,...,u-1. Suppose

    1<=C<Q, 0<=F<Q, C+F=M,
    0<=a,b<Q, (C-1) AND a=0, F AND b=0.

Then

    popcount(a)+popcount(b) <= u+1.                 (1)

Proof. Since F=M-C, it is the exact u-bit complement of C. A bit set in
both a and b must therefore be a1-bit of C, because F AND b=0, and a0-bit
of C-1, because (C-1) AND a=0. Hence

    a AND b is supported inside C AND NOT(C-1).

For C>=1 the latter set has exactly one bit: the least significant set
bit of C. Subtracting1 clears that bit, sets the lower zero bits and leaves
higher bits unchanged. Thus popcount(a AND b)<=1. The union a OR b is a
u-bit word, so the ordinary union/intersection population identity proves
(1). No parity assumption and no carry-free assumption is needed.
The bound is sharp, for example C=1,F=Q-2,a=M,b=1.

Now use the retained native window. Write MF0 for the NATIVE high mask,
so the actual fourth source port is MF_source=MF0+beta. The proved native
interface gives B=2^d,d>=4,q=B^N=2^u,u=dN,N>=1,
J=1+B+...+B^(N-1), and

    0<MC,MF0<B-1, MC=2 mod4, MF0=4 mod8,
    popcount(MC)+popcount(MF0)=d.

The two actual window masks are

    a=MC*J+1, b=MF0*J-1.

Both lie below q. Repetition has no overlap between radix cells. MC*J is
even, so incrementing it adds one1-bit. MF0*J has precisely two trailing
zero bits, so decrementing it replaces its lowest1-bit by two1-bits and
also increases population by1. Therefore the proved repeated-mask identity is

    popcount(a)+popcount(b)=dN+2=u+2.              (2)

The half-binomial rank lower bound and the retained four-block population
upper bound force the two mask equations used in (1). Fixing alpha=1 in
C+F+alpha=q gives C+F=M. Equations(1) and(2) contradict each other.

Thus NO positive zero with alpha=1 exists under this native interface,
whatever K0 or tile encoding is chosen. The contradiction survives changing
MC and MF0 if the same population budget, masks and kernel conclusions are
retained. In particular the brief's suggestion that only the tile encoding
needs replacement, with this kernel otherwise unchanged, is excluded.
This is a conditional ordinary nonexistence theorem for that lane, not a
proof that the underlying refutation problem has no solutions.

The low-bit interface supplies an additional immediate check. Since J=1
mod4, a=3 mod4 and b=3 mod4. The masks force C=1 mod4 and F=0 mod4,
whence alpha=q-C-F=3 mod4. This separately excludes alpha=1 and also
alpha=J in the UNCHANGED window. It is not a statement about windows whose
low-bit normalization has been redesigned.

## 2. A useful extension: every power-of-two slack fails

Keep the two mask conditions, but now C+F+alpha=Q with alpha>=1. Put
A=C-1. Then A+alpha=M-F is a u-bit word and

    a AND b is supported inside NOT A AND (A+alpha).

Adding a single power of2 to a nonnegative integer creates at most one
new1-bit: it either sets its position or clears a run of1-bits and sets
the first zero above it. Add the distinct powers in alpha successively.
Every final1-bit absent from the original A must have been created at
one of these additions. Consequently

    popcount(NOT A AND (A+alpha)) <= popcount(alpha).

The same union/intersection argument now gives

    popcount(a)+popcount(b) <= u+popcount(alpha).

Under (2), popcount(alpha)>=2 is necessary. In particular EVERY
power-of-two choice of alpha is impossible in this retained interface.
This bound does not prove sufficiency for any other alpha.

## 3. What the cyclic-group calculation proves, and what it does not

At a fixed N and whole-cell stride h, put P=K0+B^h and M=B^N-1.
For alpha=1, the transport is exactly

    (P+1)C=0 modM, equivalently (P+1)F=0 modM.

If g=gcd(P+1,M), its full residue solution set is the subgroup consisting
of multiples of M/g. This algebra is correct. Positive field bounds and
masks then select a subset. For a fixed expression alpha=A(J) independent
of F,C, the correct inhomogeneous equations are

    (P+1)C=1-A(J) modM,
    (P+1)F=P*(1-A(J)) modM.                     (3)

If consistent, each is a coset of the same subgroup. In particular
alpha=J has right sides1-J and P(1-J); it is not the homogeneous alpha=1
case. Its low-bit exclusion above is a separate retained-interface fact.

The brief's extension to EVERY fixed digit-wise tie is too broad.
Even a polynomial choice alpha=F² gives instead

    P*F²+(P+1)F=P modM,

which is generally quadratic, not a coset equation with a fixed right side.
This observation does not establish any completeness for alpha=F².

A literal digit-wise example makes the logical issue explicit. Let q=32,
M=31,P=5, and set C=F AND3, retaining only the low two bits. For residue
representatives0<=F<31 the transport5C=F mod31 holds exactly at

    F in{0,5,10,15}, C in{0,1,2,3} respectively.

Indeed F=5C lies in0..15 and (5C) mod4=C for C=0,1,2,3.
Set alpha=32-F-C; its corresponding values are32,26,20,14. The three
positive C,F examples have positive alpha. Neither the four-element set
nor its three-positive-element subset is a coset in the prime-order group
Z/31. Thus a fixed digit-wise relation need not linearize as claimed.
This example supplies neither the native mask budget nor a polynomially
free digit extraction in the kernel, and is NOT a compiler or equation.

The repetend calculation is also correct: gcd(B,g)=1, and the digits of
k*M/g are the base-B repetend of k/g. Remainders evolve by multiplication
by B modulo g. Across h digits, the full remainder state evolves by
B^h=-(K0+1) modulo g. This is a substantive algebraic restriction on this
family; it should not be dismissed.

It does not by itself prove impossibility of encoding nonlinear tile
rules. A block of observed digits is floor(B^h*r/g), rather than the full
residue r with its additive coordinates. This decoding can involve floors,
carries and masks. Even an injective encoding need not conjugate linear
residue arithmetic to linear evolution of the actual Boolean tile fields.

One must also avoid overstating the hidden-state size. The current recipe
has K0=DC+B*DR<B². For h>=3,

    g <= B^h+K0+1 < 2*B^h.

Thus it has at most h+1 radix digits, rather than necessarily N digits.
If it is a proper divisor of B^h+K0+1 and B^h>K0+1, then g<B^h and
an h-digit observation can even be injective. None of these corrections
turns the digit decoding into a linear Boolean map. The nonlinearity of
K215 alone is therefore not a proof against the group/coset family.

As a simple illustration of expressiveness, Boolean clauses can be enforced
by integer linear equations with Boolean slack bits: a three-literal clause
l1 OR l2 OR l3 is equivalent to l1+l2+l3+s1+s2=3 for some Boolean s1,s2.
Pack finitely many such equations into distinct digits of a base at least6;
all digit sums are at most5, so one integer linear equality enforces every
clause without carries. This does not construct the highly constrained
translation-invariant convolution here. It only shows why 'linear integer
relation plus fixed bits' is not itself a nonuniversality argument.

## 4. A selective gap that clears the local budget obstruction

There is a concrete algebraic replacement target more flexible than
alpha=1. For fixed u-bit masks a,b, set

    alpha=a AND b,
    A=(b AND NOT a) OR Z,

where Z is any word supported outside a OR b. The two parts of A have
disjoint supports and A AND a=0. Also A AND alpha=0, so A+alpha=A OR alpha
without carries. Put C=A+1 and F=M-(A+alpha). Then

    C+F+alpha=q, (C-1) AND a=0, F AND b=0.

Here alpha>=1 follows from the native mask budget, which requires at least
two intersecting bits. In the actual tuple a has bits outside b, so F>0;
C>=1. These are only the local field/mask facts, without transport.

This target has a polynomial expression in J using fixed coefficients.
Let D=MC AND MF0 and epsilon be bit2 of MC. Since the increment/decrement
only affect the lowest radix digit,

    (MC*J+1) AND (MF0*J-1)=D*J+3-4*epsilon.

The actual compact44 recipe has epsilon=1, so this is D*J-1. Its indexed
BFS descendant retains EXACTLY the same MC,MF0,B, hence the same formula.
The constant D is derived from a whole calibrated tuple; MF0, not the
shifted fourth port, is used. No tuple ports may be spliced.

This exhibits a positive polynomial candidate expression for the eliminated
slack, compatible with the two masks. It gives a concrete selective-gap
research target. It does not prove that ANY genuine computation, or the
current literal compiler, has transport-compatible canonical words with
that gap. The transport still imposes the inhomogeneous coset relation(3).
Untested convolution output bands would have to be encoded, filled or
absorbed consistently, and the full cell carry/anchor/alignment proof must
be rebuilt. No variable saving is accepted without that completeness proof.

## 5. A genuine inherited-completeness obstruction: the dummy controller

The current compact44/indexed completeness construction uses independent
safe low dummy bits to correct the ACTUAL packed rank modulo dN. At fixed
N,h a single toggle changes C by a power of2, up to sign. Its transport
residue changes by P times that amount. If a new gap alpha=A(J) is fixed
at that N, then C+F=q-A(J) requires the opposite change in F. Thus two
accepted words related by this toggle would require

    (P+1)*deltaC=0 modM.

A power of2 is a unit modulo odd M. Therefore P+1=0 modM would be
necessary. For canonical padded dimensions with h>=3 and N>=h+2,
0<P+1=B^h+K0+1<M. So this toggle cannot remain independently valid.
The original freely chosen safe-dummy subset controller cannot simply be
reused after ANY fixed-J gap tie, even if its mask constraints are locally
consistent. Coordinated word changes, another controller or another
rank/exponent interface would need a new unbounded completeness argument.
This is a precise obstruction to an inherited proof step, not to every
possible replacement controller.

The current86 normalization does not supply an extra source register. Its
Y=q³*s substitution and n_new=n_old+s positive converse remove a common
carrier factor, while the source still has independent J,F,alpha and
C=q-F-alpha. The seven other positive inputs retain kernel meanings.
Fixing a positive polynomial alpha(J,F) restricts that accepted source and
therefore preserves soundness; preserving positive completeness is exactly
the missing task. Re-labeling another unbounded input does not establish it.
The q-cube normalization's larger syntactic degree is no source compiler
freedom, and this review performs no circuit census.

The near-term conclusion is narrow. Stop alpha=1 work that retains the
current mask budget: section1 decides it. The group's existence does not
settle other one-word encodings. The selective gap above is a definite local
lemma worth retaining, but the required transport encoding AND rank-controller
replacement mean there is no demonstrated short route to a calibrated
nine-positive equation. Alternative packed S=qF+C or changed exponent-mask
interfaces remain separate source/kernel redesigns, with no result here.
