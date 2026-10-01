# Faithful free-group matrix embeddings with five-operation ordinary-input loading

A finite-rank free group admits an explicit faithful representation in
SL2(Z) with a designated generator b mapped to a unipotent matrix B.
For rank N>=2, an appropriate choice of the named generator a gives the
ordinary-input conjugate

    L(x)=B^-x A B^x

with **five scalar operations:2 multiplications and3 additions/subtractions**.
Its entries have degrees1,0,2,1 in x. There are **no supplied witnesses**.
The fixed coefficient depends only on N. A second construction gives the
same input conjugate with **six operations:3M+3A**, using A and B independent
of N. Both take the ordinary integer x directly; the intended group-language
domain is x>0. Swapping the named free-basis images also gives a
**six-operation2M+4A** program-composed loader for one fixed universal
subgroup from the companion theorem.

These are input components, not complete Diophantine certificates. A fixed
conjugation of a fibre-product subgroup makes the repeated pair `(L(x),L(x))`
a suitable target for testing a commutator relation, but this note does not
supply a subgroup-membership encoding or claim universal membership. Those
are separate requirements in the [group substrate argument](group_commutator_universal_substrate.md).

## 1. An elementary free pair in SL2(Z)

Fix

    U=[[1,4],[0,1]], B=[[1,0],[1,1]].                  (1)

Both have determinant1. We prove directly that they freely generate a
rank-two free group, without relying on a matrix-freeness citation.
Act on the real projective line by fractional linear transformations and
use disjoint sets

    X={z: |z|>2} union {infinity}, Y={z: |z|<2}.

For every nonzero integer n,

    U^n(z)=z+4n, B^n(z)=z/(nz+1).

If z is in Y, then |z+4n|>=4-|z|>2, so U^n(Y) is contained in X.
For finite z in X,

    |n+1/z|>=1-|1/z|>1/2,

so B^n(z)=1/(n+1/z) is finite with absolute value less than2.
Also B^n(infinity)=1/n belongs to Y. Thus B^n(X) is contained in Y.

A nonempty reduced word in nonzero powers of U and B can be cyclically
reduced by conjugation. If it has one block, it is a nonzero power of
U or B and is not the identity. Otherwise, after cyclic rotation it has
alternating blocks beginning with a power of U and ending with a power
of B. Applying this word to infinity sends the rightmost B block into
Y and then alternates between Y and X. Every intermediate point is
finite: a B block cannot have a pole on X, and a U block preserves
finiteness. The final point is finite, so it differs from infinity.
The cyclically reduced word is not the identity, nor is its conjugate.
This also excludes a nontrivial word representing -I, whose projective
action would be the identity. Therefore the homomorphism from the
abstract free group on U,B into SL2(Z) is injective.

## 2. A free family whose named matrices are independent of rank

For each integer i define

    g_i=U^i B U^-i=[[1+4i,-16i^2],[1,1-4i]].           (2)

Any finite set of distinct g_i is a free basis for the subgroup it
generates. To see this, consolidate any nonempty reduced word into blocks

    g_(i1)^e1 ... g_(is)^es,

where each exponent is nonzero and adjacent indices differ. Expanding gives

    U^i1 B^e1 U^(i2-i1) B^e2 ...
        U^(is-i_(s-1)) B^es U^-is.

Every interior U exponent is nonzero. The two endpoint U powers may be
absent, but at least one B block remains. This is a nonempty reduced word
in the free pair(1), so it is not the identity.

For any rank N>=2 choose b=g_0 and a=g_1, and assign every remaining
basis generator a distinct index in2,...,N-1. Then

    B=[[1,0],[1,1]], A=[[5,-16],[1,-3]]                 (3)

are independent of N. U itself is not one of these named basis generators;
adding U as another basis image would destroy this particular free-family
argument.

Since B^x=[[1,0],[x,1]] for every integer x, direct multiplication gives

    L6(x)=B^-x A B^x
         =[[5-16x,-16],[(4x-1)^2,16x-3]].             (4)

Set t=4x-1. A literal six-gate schedule is

    four_x=4*x, t=four_x-1, square=t*t,
    four_t=4*t, upper_left=1-four_t, lower_right=1+four_t.

The output is `(upper_left,-16,square,lower_right)` in row-major order.
This costs3M+3A. The fixed entry-16 and repeated uses of registers require
no arithmetic gates. The determinant is identically1 and the trace is2.

## 3. A fixed-rank free basis and a five-operation curve

For a fixed integer k>=1, consider the k+1 elements

    a=U^k, b=B,
    g_i=U^i B U^-i for1<=i<k.                         (5)

They are freely independent. Here is an explicit covering-graph proof.
Use vertices0,...,k-1. At each vertex put a B loop, and put an oriented
U edge from vertex i to i+1 modulo k. Retain as a spanning tree the
U edges from0 to1 through k-2 to k-1. The remaining U edge, from k-1
to0, represents a; the B loop at vertex i represents g_i, with g_0=b.

Each word in(5), expanded in U,B and followed from vertex0, is a closed
path. The path for a traverses the entire U cycle and exactly one edge
outside the tree. The path for g_i follows the tree to i, traverses its
B loop, and returns through the tree. Its only edge outside the tree
is that B loop. Assign those edges the distinct labels a,g_0,...,g_(k-1),
assign inverse labels to the reverse edges, and erase tree edges.
The path of a reduced word in the proposed basis therefore projects
to precisely that same reduced word.

If its expanded word in U,B were the identity, freeness of(1) would allow
it to reduce to the empty word by adjacent inverse-letter cancellations.
Such a cancellation removes an edge immediately followed by its inverse.
On the projected path it either removes no letters or an adjacent inverse
pair. The projected reduced basis word would then reduce to empty, a
contradiction. This proves freeness for every k, including k=1, where the
tree is empty and the two edges are U and B.

For a presentation with N>=2 named free generators, choose k=N-1,
map a to U^k, b to B, and map the others to g_1,...,g_(k-1). Put

    c=4k, A=[[1,c],[0,1]], B=[[1,0],[1,1]].            (6)

Here k and c are fixed numerals determined by the presentation, not
additional inputs or witnesses. The conjugate is

    L5(x)=B^-x A B^x=[[1+cx,c],[-cx^2,1-cx]].          (7)

The signs in(7) correspond to B^-x on the left. Reversing that conjugation
would reverse the two diagonal signs.

The exact five-gate schedule is

    q=c*x, product=q*x, lower=0-product,
    upper_left=1+q, lower_right=1-q.                   (8)

The output is `(upper_left,c,lower,lower_right)`. Both products, including
the multiplication by the fixed coefficient c, are charged. There are
2M+3A operations, no powers or divisions as primitives, and no existential
coordinates. The circuit uses only the nonnegative literals0,1,c, and
computes the negative entry by its paid subtraction.

An alternative five-operation circuit computes q=c*x, square=x*x and
lower=(-c)*square, followed by the same two diagonal operations. That
version has3M+2A and permits a signed fixed numeral. The main source
uses(8), which keeps the total cost and saves one multiplication.

For every fixed k>=1 the determinant of(7) is identically1, its trace
is2, and its coordinate degrees are exactly1,0,2,1. In particular rank4
allows k=3,c=12 and the fixed curve

    [[1+12x,12],[-12x^2,1-12x]].                      (9)

No theorem bounding the number of generators of an external presentation
is proved here. Formula(9) applies whenever a suitable presentation has
four named generators; the separate group argument is responsible for
obtaining that presentation. Without such a bound, the five-operation
family has a fixed coefficient depending on N, whereas(4) is independent
of N.

## 4. Why the same matrix can appear in both target blocks

Let F be a free group with named generators a,b, let pi:F->H be any
quotient map, and define its fibre-product subgroup

    M(H)={(u,v) in F x F: pi(u)=pi(v)}.

Conjugate the subgroup once by a fixed element:

    M_A=(a,1) M(H) (a^-1,1).

For the word a_x=b^-x a b^x, one has

    (a_x,a_x) in M_A
      iff (a^-1 a_x a,a_x) in M(H)
      iff pi(a)^-1 pi(a_x) pi(a)=pi(a_x)
      iff [pi(a_x),pi(a)]=1,                         (10)

using the explicit convention `[g,h]=g h g^-1 h^-1`.
This is an elementary conditional identity for any quotient H.

Apply either faithful representation above in each factor. The pair
`(L(x),L(x))` or the block diagonal4-by-4 matrix `diag(L(x),L(x))` is then
the exact target in the corresponding conjugated matrix subgroup. Copying
the four entries into two blocks introduces no scalar arithmetic; zero
entries are fixed numerals. The subgroup conjugation changes fixed program
matrices and is independent of x. This accounting does not treat the
subgroup-membership verifier, its generators, a finite presentation, or
any Diophantine witness construction as already paid.

## 5. A reference affine prefix for a fixed universal subgroup

The group companion can apply its theorem once to the c.e. positive set

    T_univ={2^p*(2x+1): x in S_p},

where S_p ranges over an effective enumeration of all c.e. positive sets.
For fixed program p, put kappa_p=2^(p+1) and lambda_p=2^p. These are
positive fixed numerals compiled from the program, not varying inputs.
The affine value

    y=kappa_p*x+lambda_p=2^p*(2x+1)

has2-adic valuation exactly p, so its odd part uniquely recovers x.
Thus y belongs to T_univ exactly when x belongs to S_p. The companion's
subgroup for T_univ is fixed across programs; only these two loader
numerals change. This invokes that companion theorem, not an additional
membership certificate from this packet.

Compose the rank-four curve(9) with this affine input. The explicit DAG is

    program_product=kappa_p*x,
    y=program_product+lambda_p,
    q=12*y, product=q*y, lower=0-product,
    upper_left=1+q, lower_right=1-q.                   (11)

It outputs L5(y), with k=3, and its repeated diagonal pair. This costs
**7=3M+4A**, uses only nonnegative fixed literals, and introduces no
witness. All four matrix coefficients retain degrees1,0,2,1 in the
ordinary input x. The powers defining the two fixed program numerals
are computed when the program is compiled; no input-dependent
exponentiation occurs in(11). The group-membership history still has
no paid Diophantine certificate here.

## 6. A swapped basis saves one operation in program composition

The preceding affine prefix is correct but can be improved by changing the
fixed embedding. Put S=[[0,1],[1,0]]. Conjugation by S preserves SL2(Z),
even though det(S)=-1. It sends the old B to Ustar=[[1,1],[0,1]] and
the old U to Vstar=[[1,0],[4,1]]. Thus Ustar,Vstar are free by Section1.
Conjugate the entire free basis(5) by S and swap its first two names:

    a=Ustar, b=Vstar^k,
    remaining basis images=Vstar^i Ustar Vstar^-i, 1<=i<k,
    Vstar^i Ustar Vstar^-i=[[1-4i,1],[-16i^2,1+4i]].

Conjugation and permutation preserve the already proved free independence.
There are again exactly N=k+1 basis images. With c=4k, now

    Astar=[[1,1],[0,1]], Bstar=[[1,0],[c,1]],
    Lstar(x)=Bstar^-x Astar Bstar^x
            =[[1+cx,1],[-(cx)^2,1-cx]].               (12)

Compute q=c*x, square=q*q, lower=0-square,1+q,1-q. The base curve still
costs5=2M+3A and uses only nonnegative fixed literals.

For the fixed rank-four case c=12 and the program encoding of Section5,
set alpha_p=12*kappa_p and beta_p=12*lambda_p. These are two fixed program
numerals. Instead of evaluating the intermediate encoded input y, compute

    program_product=alpha_p*x,
    q=program_product+beta_p,
    square=q*q, lower=0-square,
    upper_left=1+q, lower_right=1-q.                   (13)

This directly outputs Lstar(y) and its repeated pair. It costs
**6=2M+4A**, has no supplied witnesses, and uses only nonnegative literal
numerals. All coordinate degrees are again1,0,2,1. The matrix alphabet is
the fixed one supplied by the companion's group theorem for the single
coded c.e. set T_univ; the two scalar program numerals change the target
curve, while the numerical input x remains ordinary and unencoded.
The fixed products defining alpha_p,beta_p are compiled once and are
not varying-input gates. No subgroup-membership history is paid by this
six-operation loader.

## 7. Optional direct commutator coefficients

For comparison, with the rank-independent matrices(3), the literal
commutator

    W(x)=[B^-x A B^x,A]

has a19-operation integer circuit. Put

    t=8x, q=t^2, v=q^2, h=q-t,
    p=t*(2q-1), ell=p+h, r=4*(2p+ell).

Then

    W=[[1+r,-64p],[2ell-3v,1+16v-r]].                  (14)

The adjacent source lists all19 binary gates:8M+11A, including the products
by8,4,-64,3,16. Its entries are exactly

    W11=12288*x^3+256*x^2-128*x+1,
    W12=-65536*x^3+512*x,
    W21=-12288*x^4+2048*x^3+128*x^2-32*x,
    W22=65536*x^4-12288*x^3-256*x^2+128*x+1.

Their degrees are3,3,4,4. The determinant is1 and

    trace(W)=2+65536*x^4.

Thus W(x) is not the identity for any nonzero integer x, while W(0)=I.
This is a fact in the free matrix group, not a statement about its image
in a quotient H. The repeated quadratic target of Section4 avoids paying
for these quartic coefficients when that subgroup-conjugation interface
is available. No minimum-circuit claim is made for either construction.

## 8. Source, verification, and scope

The [source](group_unipotent_input_loaders.py) and
[receipt](group_unipotent_input_loaders.json) contain the six full schedules,
all fixed matrices, and exact symbolic identities. Matrices use flat
row-major four-tuples. The primary APIs are `loader5(x,k)`, `loader6(x)`,
and `paired_diagonal_target(x,k=None)`; the last uses the six-operation
curve when k is omitted and otherwise the five-operation curve. The
reference program-composed API is `loader7(x,kappa,offset)`. The preferred
APIs are `loader5_swapped(x,k)` and
`loader6_program(x,scaled_kappa,scaled_offset)`; the last two arguments of
the latter are the fixed positive program numerals alpha_p,beta_p.

Default execution regenerates and compares the receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/group_unipotent_input_loaders.py

The checker verifies the two quadratic conjugation identities, determinants,
traces, coordinate degrees, and exact literal counts symbolically. Direct
matrix powers independently check1,285 instances of the five-operation
family and257 of the six-operation curve, including negative and zero
integers. The optional quartic circuit has385 direct matrix checks and a
symbolic commutator identity. These extended-domain checks support the
polynomial identities; the intended group-language query remains ordinary
positive x. The seven-operation composition has a symbolic identity and
832 direct matrix/unique-valuation checks for p=0,...,12 and x=1,...,64.
The preferred swapped six-operation curve has576 independent matrix-power
comparisons across k=1,...,8, p=0,...,11 and six signed/zero/positive
inputs; its five-operation base has48 such comparisons. Conjugating and
permuting the prior Schreier basis is checked explicitly for each k.

For each of the two embedding families, all reduced words through lengths8,
6,5 at ranks2,3,4 are tested for distinct matrix images, respectively.
The elementary proofs in Sections1–3 establish freeness for arbitrary word
length and finite rank; these bounded checks are only implementation audits.
Additional exact rational samples check the two strict ping-pong inclusions.

The result proves faithful embeddings and explicit input loading. It
provides no universal Diophantine polynomial, no arithmetic cost for subgroup
membership, no positive-witness membership construction, and no replacement
for the separate group-theoretic universality proof.

An independent proof/source/default review passed without findings. It checked
the projective ping-pong proof, exclusion of-I, both free families including
the k=1 cover, fixed-numeral charging, and exact five/six-operation ledgers.
A separately written free-word matrix evaluator matched the five-operation
loader for k=1,...,7 and x=-40,...,40, and the six-operation and optional
quartic curves for x=-64,...,64:696 independent input cases in total.
