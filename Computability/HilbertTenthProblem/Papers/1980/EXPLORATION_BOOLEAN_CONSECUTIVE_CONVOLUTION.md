# A ten-operation Boolean convolution on consecutive cyclic shifts

This is a conditional arithmetic component for a binary radius-one cellular
automaton. It gives one **10-operation source equality, 6 multiplications
and 4 additions**, for its local affine field on a cyclic quotient with
spatial and temporal strides `h,h+1`. The quotient in this equality has a
strictly positive coordinate, with no signed-quotient adapter. The Boolean
word domains, power geometry, field bounds, mask predicate, and a universal
input or marker interface remain external. This is not a complete universal
certificate or an improvement to the published universal operation count.

The [standalone checker](../verification/explore_boolean_consecutive_convolution.py)
imports the [generic Boolean affine compiler](../verification/explore_boolean_affine_mask.py).
Its [receipt](../verification/explore_boolean_consecutive_convolution.json)
checks every quiescent binary radius-one rule on all words of lengths one
through six and all strides `1<=h<=N`. The argument below applies to all
positive lengths and strides, independently of that finite check.

## 1. The local affine field and its strict digit bound

Fix a Boolean rule `f(l,c,r)` satisfying `f(0,0,0)=0`. Use the complemented
output as the fourth input to the generic compiler: the allowed tuples are

    (l,c,r,u) with u=1-f(l,c,r).

Exactly eight of the sixteen tuples are forbidden, including the all-zero
tuple. Order the forbidden tuples `p_0,...,p_7` with zero last, and put

    A=8, G=A^8, B=2G=2^25, R=(G-1)/7,
    mu=4 sum_{j=0}^7 A^j.

The compiler supplies fixed numerals `c0,cL,cC,cR,cY` such that

    phi(l,c,r,u)=c0+cL*l+cC*c+cR*r+cY*u
               =G+sum_{j=0}^7 A^j (dist((l,c,r,u),p_j)-1).

For Boolean inputs, the clause digits lie between `-1` and `3`. Hence

    G-R <= phi <= G+3R < B-2.

In particular, the slightly weaker bound `1<=phi<=B-2` holds uniformly.
If every clause is nonnegative, its base-eight digit is at most three, so
the bit selected by `mu` is zero. If a negative clause exists, the first
such clause has value `-1`, and the earlier nonnegative digits produce no
carry into it. Its normalized digit is seven, so its selected bit is one.
The guard `G` keeps the whole number positive. Therefore

    phi & mu = 0  iff  u=1-f(l,c,r).

The all-zero final forbidden tuple also makes every variable coefficient
positive: the final weight exceeds the sum of all earlier weights. More
precisely,

    1 <= cL,cC,cR,cY <= R < B/2,       c0 >= G-R >= 1.

These coefficient inequalities, not just finite testing of the 128 rules,
will give a positive quotient below. Coefficients and `B` are fixed
numerals for the chosen rule and have no construction cost in the present
complexity measure.

## 2. The exact cyclic congruence

Let `N,h>=1`, and suppose the following power geometry and repunit are
already supplied:

    q=B^N, D=q-1, J=D/(B-1), P=B^h, Q=B P.

Let `C=sum_{i=0}^{N-1} z_i B^i` with each `z_i` Boolean. Subscripts in this
section are modulo `N`. Define the actual affine word

    Factual=sum_i phi(z_{i+h},z_i,z_{i-h},1-z_{i-h-1}) B^i.

Multiplication by `P` modulo `D` sends the digit at `i-h` to position `i`.
Thus the words for the left, center, right, and next cells are congruent to

    P^(-1) C, C, P C, Q C  (mod D),

respectively. The inverse exists since `gcd(P,D)=1`. Every cyclic rotation
of `J` equals `J` modulo `D`, so

    P Factual == K(P) C + (c0+cY) J  (mod D),
    K(P)=cL+cC P+(cR-B cY)P^2.

This is a polynomial congruence for every `N,h`; neither `h<=N` nor an
equation `N=h(h+1)` is required. The finite checker uses `h<=N` as a bounded
test domain only.

The ordinary, non-modular digit bound gives

    c0 J <= Factual <= (B-2)J < D.

In particular, `Factual` is nonzero and strictly below the modulus. If a
supplied integer `F` satisfies `0<F<q` and the displayed congruence, then
`F==Factual (mod D)`. Its only possible representative in `1,...,D` is
`Factual`, because `0<Factual<D`. Consequently the congruence, the supplied
field bound, and Boolean typing of `C` recover the exact affine word.
They imply

    F & (mu J)=0
        iff z_{i-h-1}=f(z_{i+h},z_i,z_{i-h}) for every i.

This assertion relies on the already established radix alignment,
Boolean typing, and field bounds. The congruence or the mask alone does
not establish those prerequisites for arbitrary integer words.

One further consequence useful to a future outer construction is
`C+Factual<=q-1`: at every cell its digit is at most `1+(B-2)=B-1`, so no
carry occurs. Thus a positive slack in `C+F+alpha=q` exists for every
genuine word. This observation supplies no unpaid soundness direction.

## 3. A positive quotient at no extra operation

Set the following two fixed positive numerals:

    a=B cY-cR,       cstar=c0+cY.

Let

    H(P)=P(aP-cC)-cL=-K(P).

All parts of this Horner expression are positive. Indeed `a>=B-R`, and
`P>=B`, so `aP-cC>=B-2R>0`; as it is an integer, multiplication by `P`
and subtraction of `cL<=R<B` leave `H>0`. Also

    B c0-cstar=(B-1)c0-cY>0.

It follows, even when `C=0`, that

    P Factual + H C - cstar J
        >= (B c0-cstar)J > 0.

The cyclic congruence says that this positive integer is divisible by
`D`. It therefore defines a strictly positive integer `w`, and the exact
source equality can be written as

    P F + H(P) C = cstar J + w D.                       (1)

Conversely, a positive solution of (1) in the supplied word domain implies
the congruence from Section 2, so it recovers `Factual` and the same local
truth equivalence. There is no lost endpoint case or need to write a
signed quotient as a difference of two positive unknowns. For `C>0` all
arithmetic outputs in the following schedule are strictly positive; for
the allowed constant-zero word, only `HC` becomes zero.

## 4. The ten-operation source

With `a,cstar,cL,cC` fixed numerals and `P,C,F,J,w,D` supplied inputs, use

| Row | Instruction | Kind |
|---:|---|:---:|
| 1 | `aP=a*P` | M |
| 2 | `inner=aP-cC` | A |
| 3 | `Pinner=P*inner` | M |
| 4 | `H=Pinner-cL` | A |
| 5 | `HC=H*C` | M |
| 6 | `PF=P*F` | M |
| 7 | `left=PF+HC` | A |
| 8 | `cJ=cstar*J` | M |
| 9 | `wD=w*D` | M |
| 10 | `right=cJ+wD` | A |

The final comparison `left=right` is free. Subtractions cost one addition,
and can be written as `inner+cC=aP` and `H+cL=Pinner`. The checker expands
every instruction, verifies its primitive equation, and checks that the
source residual is exactly

    PF - [cL+cC P+(cR-B cY)P^2]C - (c0+cY)J - wD.

No product hidden in the two fixed numerals is an input-dependent
operation. The mask `mu J` requires a further multiplication if it is not
already available. Its enforcement, formation of `D,J`, all power and
alignment equations, Boolean and size constraints, and a computational
acceptance interface are outside this ten-operation ledger.

For comparison, if spatial and temporal powers `P,Q` are independent,
the coefficient is `cL+P(cC+cR P-cY Q)`. Its direct Horner construction
uses `3M+3A`, before the remaining equality arithmetic. Substitution of
`Q=B P` combines two terms into a fixed coefficient and yields the
`2M+2A` Horner construction above. This is an exhibited saving in these
particular schedules, not an optimality theorem about arithmetic circuits.

## 5. What the consecutive quotient represents

For a cyclic word satisfying the local relation, define a configuration
on the entire integer space-time lattice by

    c(x,t)=z_{-hx-(h+1)t mod N}.

Its left, center, right, and next values are exactly the four cells tested
in Section 2. Thus it is a valid CA space-time configuration, periodic
under both `(N,0)` and `(0,N)`. The map from `(x,t)` to the cyclic index is
surjective: `(x,t)=(i,-i)` has index `i`. Therefore the cyclic local
relation is equivalent to validity of this pullback, rather than merely
testing a subset of its cells.

This soundness statement holds for arbitrary positive `N,h`. Completeness
for a specified family of periodic computations is a separate issue. A
particular sufficient hypothesis is that the actual local relation has
a torus presentation of width `h+1` and height `h`, including matching
opposite edges. The map

    (x mod (h+1),t mod h) -> -hx-(h+1)t mod h(h+1)

is a bijection, by reduction modulo the two coprime periods. It converts
that presentation to the cyclic word with `N=h(h+1)` and the required
strides. This proves a conditional transfer, not the existence of such
tori for any chosen CA.

The [marked periodic tableau padding theorem](EXPLORATION_MARKED_PERIODIC_TM_PADDING.md)
establishes independent large width and height padding for its own
effectively generated finite-alphabet local relation. It would provide
consecutive torus dimensions for that relation. It does not establish
such padding for Rule 110, for an arbitrary binary CA, or for a fixed
raw-input arithmetic encoding. An alphabet/rule conversion must preserve
the required periods and acceptance interface before this conditional
transfer can be used. No such conversion is included here.

## 6. Bounded independent evidence

The checker exhausts all 128 quiescent binary radius-one rules. For each
rule it checks all sixteen scalar inputs, then every cyclic Boolean word
of length `1<=N<=6` at every stride `1<=h<=N`. There are **2,048 scalar
cases and 82,176 cyclic cases**. Each cyclic case checks the exact quotient,
its strict positivity, the full ten-instruction source, all intermediate
signs, the field bounds, the mask/local-truth equivalence, and selected
pullback coordinates. The ten instructions also have a symbolic residual
check independent of those finite words. Running without `--write`
recomputes the receipt and requires exact JSON equality.

The infinite-length claims follow from Sections 1--5. Finite enumeration
is regression evidence for the compiler, conventions, schedule, and
receipt, not a substitute for those proofs.

Review status: author and independent complete scoped proof/source reviews
pass. The independent review checks the coefficient bounds, positive
quotient, exact field recovery and surjective lattice pullback as separate
claims. A fresh default checker run reproduces the saved JSON exactly.
