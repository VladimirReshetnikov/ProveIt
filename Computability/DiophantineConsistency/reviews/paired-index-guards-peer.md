# Independent ordinary review: paired index guards

**PASS for the stated ordinary source-level existence equivalence.** I
independently read the complete argument and its exact row certificate:

| Reviewed file | SHA256 |
|---|---|
| `research/paired-index-guards/README.md` | `7307c64d16a085fff48680ec7a4941b92237c0adc64408f70b7039bc7eb4303e` |
| `LOCAL_FACTORIAL.md` | `1fbb094d09d8d10e03c745a32f7863ca4a5d4a57765408549d47130a4623580d` |
| `local_factorial_audit.py` | `1932e42bfed4eef58110226dc45274836166b43270e6e835c2961df5f2077a0e` |
| `LOCAL_FACTORIAL_CERTIFICATE.json` | `2be4f7d49a5c473f71dae8227a791e415ee085d90d6db6f7b3bd31982d4de34a` |

The three removed old scalar predicates are exactly raw674>=0,
raw861>=0 and raw1214>=0. The replacements are V/raw656>=1 and
raw674*raw861>=0. The remaining75 scalar predicates retain all61
semantic-prefix guards, base0.T/raw694, and the local seed bounds
raw711 and raw779. This review accepts those particular replacements;
it does not accept deleting the predicates without their replacements,
weakening V>=1 to V>=0, or any projected variable/term/height claim.

## The local proof does not borrow the full power bridge

The retained prefix premises give all643 prefix coordinates nonnegative,
t>=1 and n0=t+1>=2. The existing guarded-T0/bootstrap argument supplies
A>=2 and A>W^W without using either missing index slack or the old product
factor's sign. W is2 plus the actual nonnegative frame arguments, so each
actual n,k,m is below W before a power interpretation is applied.

The new strict V predicate and the exact product identity force every
seed ordinate nonzero. Thus the squared product is a positive integer,
and its remaining factor raw1214+1 is positive: raw1214>=0 is recovered
pointwise. The unchanged common norm then excludes the B=1 comparison
exception through0<A−1<|U|. The signed-B criterion is applicable with
absolute main ordinates, and no original q4 positivity is asserted.

The exact source constructors give K=raw86>=3 and Nshift=K+fK²>=K,
using only f>=0 at this stage. The retained local slack predicates yield
positive ordinates at those two indices, licensing their short intervals.
They do not require either of the missing t/k122 predicates. The only
locally interpreted calls, bound to the actual original rows, are:

| Call | Base | Exponent | Output | Main pair |
|---|---:|---:|---:|---|
| 1 | raw92 | raw86 | raw93 | raw707,raw708 |
| 5 | raw531 | raw90 | raw532 | raw775,raw776 |
| 6 | raw530 | raw86 | raw533 | raw707,raw708 |

At either retained pair, its positive ordinate and positive base n>=1
suffice to orient the main abscissa: a negative abscissa would make the
positive integer m*n^k+1<T divisible by T. Then the ordinary residue and
both values' strict bounds below T give the exact intended power. This
argument includes base1 and m=0; it does not require n>=2 prematurely.

Call1 first gives N=(fK²+1)^K>=1. The actual ceiling/remainder cuts give
C=r+s+1>=1 and fC=N+s, hence **only now** f>=1. The literal M constructor
already gives M>=1; the radix is b=M*(1+N+raw113)>N. No intended meaning
of raw113 is used: its retained nonnegative sign is enough. Calls6 and5
then give b^K and (b+1)^(K+d), where d=fK². No t-index call has been
interpreted to reach this point.

## The digit and factorial steps are unbounded

The actual choose0 cuts give

    (b+1)^(K+d)=b^K*(C+b*h)+u,
    b^K=u+v+1,
    b=C+z+1.

The retained prefix signs prove0<=u<b^K and0<=C<b. These are actual
source remainder/digit inequalities, not desired interpretations of
unnamed witnesses. For a_j=binom(K+d,j), d>=K implies the coefficients
through K are nondecreasing, and

    a_j<=a_K<=product_(i=1..K)(d+1)=N<b.

Consequently all coefficients **through K** are valid base-b digits.
Their lower sum is at most b^K−1, so there is no carry into the selected
digit. Higher coefficients need no bound because their whole terms are
multiples of b^(K+1). Two Euclidean remainder comparisons therefore give
C=a_K exactly. The proof does not apply a no-carry assertion to the entire
binomial expansion.

The self-referential factorial step is also sound. With m=K!,

    N/C=m*product_(j=1..K)(1−(j−1)/(d+j)),
    m*(1−1/(2f)) < N/C <= m.

The strict lower bound follows from product(1−a_j)>=1−sum(a_j) and
sum(a_j)<(K−1)/(2fK)<1/(2f). The actual source bounds0<=s<C give
f−1<N/C<=f, hence f=ceil(N/C)<=m. If1<=f<m, then
(f−1)(m−f−1)>=0 gives f(m−f)>=m−1, so
m*(1−1/(2f))>=f for m>=2, contradicting that strict lower bound.
This includes K=2,f=1; no equality loophole is left at the endpoint.
Thus f=K!, and at the actual K>=3, f is even.

## Parity is used before either missing-index power meaning

Even f makes raw103=1+(t+1)f odd. Its actual modulus is even.
Reducing the **norm** and actual call2 residue modulo2 gives raw104 odd,
without knowing the signs or indices of the t pair and without asserting
raw104=raw103^t. The exact source addition k122=t+raw104+2 then gives
opposite parity of t and k122. The corrected K constructor has no assumed
parity: raw86 is `(t+x+y+M0+2)^(2^23)`, and raw36 is y+1.

Whichever missing index is positive and even has a nonzero ordinate by
V>0. If its absolute ordinate were1, the main Pell index would be1.
The abscissa half-period congruence forces the comparison index h odd,
whereas the signed ordinate congruence modulo4 forces h even. This
contradiction does **not** first assume the missing short interval.
It covers negative Y, the common-index endpoint j=1, and h=0 (whose
ordinate is simply0). Otherwise |Y|>=2 gives |Y|>=psi_2(A)=2A>W>k,
so the needed short interval is now established and the signed index
criterion recovers the intended absolute main pair.

The corresponding actual supporting base is at least2: call0 uses t+1,
and call9 uses raw531=b+1. With these bases, the three unwanted X/Y sign
patterns make T divide m*n^k+1, m*n^k−1, or m+n^k. The first and third
are positive below T. The second has absolute value below T, and cannot
be0 because n>=2 and k>=1 exclude m*n^k=1, including m=0. Hence both
main coordinates are positive. Since this index is even, its original
slack is **strictly** positive. Its product with the other actual slack
is nonnegative, forcing that other slack nonnegative as well.

This recovers all three removed old predicates at the **same original
body tuple**. Transfer the75 retained triples and choose fresh triples
for the three recovered nonnegative values. Conversely, at an old zero
all15 indices are positive by the unchanged constructor proof, so the
old slack predicates give all Y>=k>=1 and the old product identity gives
V>=1. The old nonnegative slacks have nonnegative product. Thus choose
fresh triples for V−1 and the product. These are zero-existence maps;
no bijection of private Legendre witnesses is claimed. The inherited
full power/calibration argument is invoked only after the literal old
guarded source has been reconstructed.

## Exact checks and limits

My adjacent script imports only pinned sparse polynomial primitives,
never the author audit module, an optimizer or an emitter. It independently
replays575 prefix sign steps, all431 strict constructor steps (including
the converse's all15 positive-index license),77 complete original-row
identities, the23-square K constructor, the three local call bindings,
the later conditional call0/9 interfaces, and four complete Boolean
parity identities. It authenticates the complete declared author inventory
and every inherited source pin. The normal and optimized author audits
were replayed into scratch, leaving the packet unchanged; both pass and
agree except their mode flag. Their low-digit, factorial and sign controls
and my exact rational-product diagnostics supplement the reviewed
unbounded proof, rather than replacing it. Independent normal/-O peer
receipts also pass.

The accepted conclusion is ordinary integer-zero existence equivalence
for these exact source predicates. No new projected equation, coefficient
census, count improvement, Lean result, internal-ZFC derivation or native
calibration theorem is asserted by this review.
