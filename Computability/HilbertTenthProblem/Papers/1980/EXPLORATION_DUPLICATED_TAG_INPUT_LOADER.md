# A fixed tag startup from repeated ordinary ternary input

This is a constructive input-loader component. It preserves all digits of
an ordinary numerical query through the first pass of a fixed deletion-tag
system, with an explicit fixed header and trailer. For deletion two, the
raw duplication costs two arithmetic operations. The complete initial-word
interface below costs eight, or ten when the odd-length condition is also
paid. It does **not** yet establish that a fixed universal target tag system
accepts the resulting startup format, nor a universal operation bound.

The extra symbols are represented honestly: they require additional aligned
ternary tracks. The initial numerical query keeps its original radix-three
significance. No scalar digit dilation or change of radix is implicit.

## 1. The fixed combinatorial loader

Fix a deletion number beta>=2. Let the three raw input symbols be
0,1,2, and let sigma and tau be two different fresh symbols. Let Delta
be a finite target alphabet disjoint from these five symbols. Fix target
words P,T in Delta* and a homomorphism h:{0,1,2}* -> Delta*.

Use the fixed rules

    sigma -> P,       d -> h(d) for d=0,1,2,       tau -> T,

together with the target beta-tag rules on Delta. The rule for the first
symbol is applied while beta symbols are deleted, in the usual tag sense.
Zero in the following formula is an ordinary raw zero, used as an ignored
filler. For any word w of length ell with gcd(ell,beta)=1, initialize at

    sigma 0^(beta-1) w^beta tau 0^(beta-1).                 (1)

Exactly ell+2 tag steps transform (1) into

    P h(w_0) h(w_beta mod ell) ...
      h(w_((ell-1)beta mod ell)) T.                       (2)

Proof: the first step deletes the initial beta-symbol block and appends P.
The next ell steps delete the beta copies of w, beta symbols at a time.
Their read positions, measured from the start of the copies, are
0,beta,...,(ell-1)beta. Taking these positions modulo ell gives the
displayed permutation. Coprimality makes it a permutation of all ell
positions. The last step reads tau, deletes the final filler block and
appends T. Before that last step, enough original symbols remain to take
the required step, regardless of the lengths of the appended words. None
of the target rules has been used yet. The produced words occur in exactly
their append order, proving (2).

Consequently the initial word halts under any fixed target rule table if
and only if (2) does. This statement uses the same tag halting convention
on both sides, such as reaching a word shorter than beta. There is no
premature halt or accidental target transition in the loading phase.

For beta=2, choose ell odd. The read sequence is

    w_0,w_2,...,w_(ell-1),w_1,w_3,...,w_(ell-2).

Its inverse is computable from its length: if ell=2s+1, take alternating
symbols from the first s+1 and final s symbols. More generally, the inverse
uses the inverse of beta modulo ell. This is a reversible permutation of
the input digits. Actually executing its inverse inside a target simulator
remains part of that simulator's startup obligation.

Coprimality matters. For beta=2 and ell=2, the words 00 and 01 have the
same read sequence 00 in their respective doubled words. No appended
encoding can recover the discarded second symbol in that example.

## 2. Ordinary numerical input and honest symbol coordinates

Let x>=0 and choose ell>=1 with x<L=3^ell. Interpret x as the little-endian
ternary word w of exactly ell digits, padding with high zeros. All numerical
inputs have such a padding with ell=1 mod beta. Padding does not change x.

Choose a fixed number k of ternary coordinates large enough to encode the
finite alphabet injectively. Assign

    d     -> (d,0,...,0), d=0,1,2,
    sigma -> (0,1,0,...,0),
    tau   -> (0,2,0,...,0),

and assign distinct remaining tuples to Delta. Thus k can be chosen with
3^k >= |Delta|+5. The work alphabet may need k>2. Only the first two
coordinates of the initial word can be nonzero; the others start at zero.
For example, the initial symbol sigma is not an out-of-range scalar trit.
It is a pair of ordinary trits at one aligned queue position.

Put K=3^beta, a fixed numeral, and let Winit be the initial length marker.
The coordinate values of (1) are exactly

    N0 = K*x*(1+L+...+L^(beta-1)),
    N1 = 1+2*K*L^beta,
    Ni = 0 for i>=2,
    Winit = K^2*L^beta.                                  (3)

The nonzero metadata trits are sigma at position zero and tau at position
beta*(ell+1). Both fit below Winit. The first coordinate consists of the
beta disjoint copies of x after beta low zero trits, so (3) has no carries
between copies and exactly encodes (1).

For deletion two this specializes to

    N0=9*x*(L+1),       N1=1+18*L^2,
    Winit=81*L^2.                                       (4)

The scalar value of the middle word ww alone is x*(L+1), using one
addition and one multiplication. Formula (4) also supplies the startup,
endpoint and length; its additional costs are not hidden in that two-op
duplication claim.

With L supplied, an explicit schedule for (4) and x+alpha=L is

    L2=L*L; copy_factor=L+1; copies=x*copy_factor;
    N0=9*copies; marker_scale=18*L2; N1=marker_scale+1;
    Winit=81*L2; input_bound=x+alpha.

It costs exactly eight operations, 5M+3A, with the free comparison
input_bound=L. The positive slack alpha proves x<L. The realization of L
as a power of three is external. If its odd exponent is not already part
of that geometry, add positive Y and the paid equality L=3Y^2, costing
two multiplications. Together with L=3^ell this forces ell odd. The full
stated interface is then ten operations, 7M+3A.

For general fixed beta, computing L^2,...,L^beta once, summing the powers
for the geometric factor and forming (3) gives 2beta+4 operations:
(beta+3)M+(beta+1)A, including x+alpha=L. A straightforward paid condition
L=3Y^beta adds beta multiplications and forces ell=1 mod beta once L is
known to be a power of three. These are explicit schedules, not claims
that the addition chains are minimal. No operation on a witness is made
free merely because beta is fixed.

Zero-valued coordinate words are allowed in this component. In particular
x=0 gives N0=0 and every unused work coordinate is initially zero.
Strictly positive adapters and the mask realization of all aligned tracks
must be paid by a complete arithmetic verifier.

## 3. Compatibility with a queue history, and the remaining boundary

Encoding symbols by k ternary coordinates does not change the deletion
number. If a rule appends a fixed word v of a symbols, let Ui be its value
on coordinate i, and let di be the coordinate value of the deleted beta
symbols. For a nonhalting source with length marker W, every coordinate
obeys exactly

    K*Ni_next=Ni-di+Ui*W,
    K*W_next=3^a*W.                                     (5)

These are the same queue-content and length recurrences as in the current
tag-history interface. However, there are now k content coordinates and
many possible fixed productions. Their alignment, rule selection,
coefficient bounds and zero coordinates are additional obligations. The
eleven-mask binary 0->0,1->u verifier is not already a verifier for this
larger alphabet.

The source contract still matters. Woods and Neary's fixed-alphabet
2-tag simulation uses decorated symbol pairs and a unary counter whose
length is a power of two determined by the input length. Definition 4 is
not merely a fixed header, a letterwise homomorphism and a fixed trailer.
Their definition of the running representation also allows a larger
power-of-two counter, but that counter must still be initialized and
maintained. See [Woods and Neary, On the time complexity of 2-tag systems
and small universal Turing machines, Section 4.1](https://tilde.ini.uzh.ch/users/tneary/public_html/WoodsNeary-FOCS06.pdf).

Thus the present result closes an exact finite loading phase, including
its lost-digit, header, endpoint and numerical-radix issues. It does not
assert a fixed universal target with startup (2). A constructive target
that first undoes the read permutation and builds its work representation,
or a different proven target input format, is still needed. The query is
not smuggled into h, P, T or the production table: all of them are fixed.

## 4. Evidence

`../verification/explore_duplicated_tag_input_loader.py` checks the source
DAG and counts, the initial track formula, every loading transition and
the inverse permutation. It exercises all ternary words in its listed
small coprime dimensions, three distinct fixed header/homomorphism/trailer
choices, high-zero padding and the noncoprime loss example. It also tests
the general fixed-beta schedules and the two paid exponent conditions.
The unbounded loader and input formulas are proved above; no finite test
is used as evidence of universality.
