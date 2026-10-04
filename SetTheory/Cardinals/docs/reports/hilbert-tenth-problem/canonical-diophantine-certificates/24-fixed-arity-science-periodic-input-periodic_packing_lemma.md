# Periodic input, padding, and exact six-neighbor stream packing

## Scope and result

This note gives a fixed-count arithmetic interface for a fixed periodic three-dimensional background, an unknown containing cuboid, its zero odometer shell, and the six lattice neighbors. It does **not** silently convert an ordinary input integer into its spatial addition stream. That conversion must be supplied and paid separately.

The preferred construction uses radix 32 and a paid binary-subset predicate to impose an interior mask. After that one mask, all six neighbors are plain multiplication or exact division: there are no direction-specific wrap masks, truncation operations, or halo variables. Only three variable-exponent POWER relations are needed for the geometry. A second lemma shows how a growing radix removes even the interior mask by carry-free folding.

All arithmetic relations below are over natural numbers. A POWER relation must be replaced by an explicit fixed-arity integer gadget before calling the result an ordinary polynomial certificate. No generic MRDP theorem is used in this note.

## 1. Fixed periodic background and variable cuboid

Fix periods p,q,r >= 1 and a literal table

    h(i,j,k) in {0,1,2,3,4,5},  0 <= i < p, 0 <= j < q, 0 <= k < r.

Extend h periodically to Z^3. Choose natural t_x,t_y,t_z >= 1 and let

    A = 2 p t_x,  B = 2 q t_y,  C = 2 r t_z,
    lower corner = (-p t_x, -q t_y, -r t_z),
    N = ABC.

The cuboid contains exactly the integer points with local coordinates
0 <= x < A, 0 <= y < B, 0 <= z < C. Its lower corner is a multiple of every respective period, so local and global periodic phases coincide. The nested cuboids cover every finite subset of Z^3, and their interiors cover every finite subset after increasing the t parameters. Thus restricting to this family loses no finite-support odometer or finite input.

Use lexicographic index

    i(x,y,z) = x + A y + AB z.

For radix b=32 define

    X = b^A,  Y = X^B = b^(AB),  Z = Y^C = b^N.

These use exactly three variable-exponent POWER calls. All appearances of powers with fixed literal exponents below are ordinary fixed polynomials or fixed multiplication circuits.

For an array a, write

    Pack(a) = sum a(x,y,z) b^(x+Ay+ABz).

All digitwise interpretations require explicit coefficient bounds below b.

## 2. Exact geometric-series formula for the periodic background

Define the fixed literal integers and fixed polynomial

    c_jk = sum_{0 <= i < p} h(i,j,k) b^i,
    P(X,Y) = sum_{0 <= j < q, 0 <= k < r} c_jk X^j Y^k.

Introduce G_x,G_y,G_z by

    (b^p - 1) G_x = X - 1,
    (X^q - 1) G_y = Y - 1,
    (Y^r - 1) G_z = Z - 1.

The factors are positive; dimensions are multiples of their periods, so each quotient exists and is unique. Explicitly,

    G_x = sum_{a=0}^{A/p-1} b^(pa),
    G_y = sum_{a=0}^{B/q-1} X^(qa),
    G_z = sum_{a=0}^{C/r-1} Y^(ra).

Then the exact background stream is

    H = P(X,Y) G_x G_y G_z.

Proof: expanding the product gives, exactly once for each local site, the term
h(i,j,k) b^(i+pa) X^(j+qb) Y^(k+rc). Uniqueness of the coordinate remainders modulo p,q,r makes these exponents distinct. Thus there are no multiplication collisions or carries; the resulting digits are precisely the prescribed h values.

For the reviewed source's periods,

    p = 1303671936,
    q = 744955392,
    r = 1955501604.

The fundamental cell contains 1899139038016727160551374848 sites, while P has at most q*r = 1456761463964448768 literal coefficients c_jk. This is a finite fixed polynomial, but it is not a small-operation claim. A dense nested-Horner evaluation needs at most qr-1 nonconstant multiplications and qr-1 additions after omitting an optional initial zero. The report's particular literal table remains an inherited source dependency, exactly as stated in the intake review; this note does not reconstruct or authenticate that enormous table.

In particular, a notation such as h(i,j,k) cannot remain an unpaid oracle in the final certificate. Either instantiate these fixed coefficients, or give a fully paid fixed circuit for them. Their being fixed proves finite arity, not competitiveness with an 84-operation construction.

## 3. Whole-box and interior masks without extra POWER calls

Let G(t,m)=1+t+...+t^(m-1), with G(t,0)=0. The whole-box mask is

    J = G(b,N),       31 J = Z - 1.

The interior mask is

    I = b X Y J_x J_y J_z,
    J_x = G(b,A-2), J_y = G(X,B-2), J_z = G(Y,C-2).

It has radix-b digit 1 exactly where 1 <= x <= A-2, 1 <= y <= B-2, 1 <= z <= C-2. Define its factors with no new POWER calls:

    1024 (31 J_x + 1) = X,
    X^2 ((X-1) J_y + 1) = Y,
    Y^2 ((Y-1) J_z + 1) = Z.

These equations follow by multiplying the standard geometric-series identities by b^2, X^2, Y^2. They also handle A=2, B=2, or C=2: the corresponding geometric factor is zero and the interior is empty.

When U is a binary bit-subset of I, every radix-b digit of U is 0 or 1 and all six boundary faces vanish. Here binary bit-subset means that each set bit of U is a set bit of I; because I has bits only at positions 5i, this is exactly the desired binary digit restriction. The bit-subset predicate is an external paid interface, not a primitive granted by this note.

## 4. Six exact neighbors with no wrap masks or truncation

Suppose U=Pack(u), all u digits are nonnegative, and u vanishes on every boundary face. Extend u by zero outside the cuboid. Introduce exact quotient streams

    b U_x^- = U,
    X U_y^- = U,
    Y U_z^- = U.

The lower z face is zero, so Y divides U, and consequently b and X divide U. The upper z face is zero, so YU < Z. Therefore all six streams

    bU, U_x^-, XU, U_y^-, YU, U_z^-

are length-N streams with no truncation needed. At a local site v their digits are respectively

    u(v-e_x), u(v+e_x), u(v-e_y), u(v+e_y), u(v-e_z), u(v+e_z).

Proof for x: multiplication by b shifts index by one. The only nongeometric transition would send x=A-1 to x=0 of the next row, but its source digit is zero. Division by b has the symmetric property because x=0 digits are zero. The y proof uses index stride A and zero y faces; the z proof uses stride AB, and the endpoint conditions already rule out overflow or discarded digits. This proves the claim for all sites, including the shell.

Padding is essential: without the x-face zero condition, a nonzero digit at (A-1,y,z) would move under bU to (0,y+1,z), which is not its x-neighbor.

## 5. Stable endpoint equation and exterior closure

Let delta be the complete finite input addition, supported inside this cuboid, and let D=Pack(delta). Correct input decoding and support containment are hypotheses here. Let F=Pack(f), where every f digit is in {0,1,2,3,4,5}. Let U be binary and supported in the interior as above. Impose

    H + D + bU + U_x^- + XU + U_y^- + YU + U_z^-
        = 6U + F.                                      (E)

If delta(v) <= 20 at every site, the left coefficient at each digit is at most 5+20+6=31 and the right coefficient is at most 11. Hence both sides are genuine carry-free radix-32 expansions. Equality (E) is exactly the pointwise equation

    h(v)+delta(v)-6u(v)+sum_{w adjacent to v}u(w)=f(v).

A stronger and often convenient contract is delta(v)<=11. It loses no binary stabilizable input: if u<=1 and the endpoint is stable, its equation gives initial height <=6u+5<=11, so delta<=11 automatically. Either an input decoder must enforce a suitable digit bound, or carry handling must be paid explicitly. An unconstrained addition stream with digits 0..31 is insufficient for the no-carry proof.

For any v outside the cuboid, a neighbor inside lies on the zero odometer shell. Thus no grain is sent outside the cuboid by the candidate odometer. The input is also absent there, so the endpoint equals the stable periodic background outside. No extra halo variables or exterior-face inequalities are necessary. This is precisely what the extra shell buys.

## 6. Rank-free existence certificate by least action

The endpoint certificate already implies finite legal stabilization. It does not need the finite-prism report's canonical burning ranks when the only target is existence.

Suppose a finite nonnegative u satisfies initial+Delta(u)<=5 globally. Consider any legal firing sequence, and assume a vertex v is about to fire for the first time beyond its allowance u(v). Immediately before that firing, v has fired u(v) times and every neighbor w has fired at most u(w) times. Its current height is therefore at most

    initial(v)-6u(v)+sum_{w adjacent to v}u(w) <=5,

contradicting legality. Thus every legal sequence fires at most sum_v u(v) times. Starting from stable background plus finite additions, repeatedly firing an unstable vertex must terminate within that bound at a stable configuration.

Conversely, if the given sandpile has a finite legal stabilization whose actual odometer is binary, choose a sufficiently large centered period-aligned cuboid containing the input and odometer supports in its interior. Its genuine odometer, endpoint, and correct input/background streams satisfy all equations above. The one-shot/binary property is needed only for this completeness implication. It is inherited from the loader under the intake review's stated scope.

Therefore, for a loader whose halting instances have binary odometer, a correctly decoded input plus the packed stable endpoint is a sound and complete finite-toppling existence certificate. It need not preserve the finite-prism certificate's unique witness tuple or real-exactness theorem.

## 7. Optional fully mask-free shell test with a growing radix

This alternative is not compatible with a fixed radix 32 for arbitrarily large prisms without additional bounds. It is recorded because it gives an exact answer to whether padding can eliminate all masks.

Let arbitrary radix b>=2, dimensions A,B,C>=2, N=ABC, and digits 0<=u_i<=K satisfy b-1>NK. Again X=b^A, Y=b^(AB), Z=b^N. Then u is zero on all six boundary faces if and only if there exist eight natural numbers Q_x,a_x,Q_y,a_y,a_z,s_x,s_y,s_z satisfying

    U = Q_x(X-1) + b a_x,
    b^2 a_x + s_x + 1 = X,
    U = Q_y(Y-1) + X a_y,
    X^2 a_y + s_y + 1 = Y,
    U = Y a_z,
    Y U + s_z + 1 = Z.                                (B)

Proof: reducing U modulo X-1 folds all y,z rows into

    R_x = sum_{x=0}^{A-1} (sum_{y,z}u(x,y,z)) b^x.

Every folded coefficient is at most NK<b-1, so no carries occur and 0<=R_x<X-1. The first pair of (B) makes R_x divisible by b and less than b^(A-1), exactly the vanishing of both x-face sums. Nonnegative digits turn vanishing sums into individual vanishing. Similarly, modulo Y-1 folds the z layers; divisibility by X and the bound R_y<b^(A(B-1)) enforce both y faces. The final pair directly removes the lower and upper z layers. Conversely, zero faces produce exactly these quotients, remainders, and strict-inequality slacks.

All equations in (B) are polynomial of degree at most three once X,Y,Z are supplied. Thus three POWER calls plus a digit-bound interface suffice for completely mask-free geometry, using eight fresh witnesses and six equations for the shell.

Why fixed radix invalidates this shortcut: in dimensions A=3,B=10,C=6 at radix 32, put u(0,y,z)=1 for 1<=y<=8,1<=z<=4, and zero elsewhere. This has 32 nonzero digits on the x=0 boundary. Its x-fold is 32, which carries into the interior x=1 digit; all six equations (B) pass even though the x shell is nonzero. The growing-radix condition is substantive, not optional.

## 8. Exact remaining interface for ordinary input

Let n be the ordinary input integer. A complete certificate needs a relation

    Decode(n,t_x,t_y,t_z,D,...)

that proves all of the following, with fixed arity and every operation paid:

1. It applies the specified program/tape-to-sandpile addition map to n.
2. It places every addition at its exact global site, shifted by the chosen lower corner.
3. Every input site is in the containing cuboid; no unrepresented addition remains outside.
4. D has the required bounded digits, and any row/plane base conversion is explicitly enforced.

Merely existentially guessing D, passing D as a second ordinary input, or writing a variable-length sum over input digits is not this interface. Periodicity solves only the background stream, and period-aligned padding solves only geometry and exterior closure.

## 9. A fully uniform raw-instance decoder by two block spreads

The following additional construction, proposed by the parent and checked independently here, removes the need for the enormous literal P when the ordinary input is a raw periodic-plus-finite instance. It does not remove the separate program-to-sandpile encoder dependency.

Take eight natural input descriptors

    p,q,r,Tile,L_x,L_y,L_z,Patch,

with the six dimensions positive. Tile has p*q*r radix-32 digits in {0,...,5}; Patch has L_x*L_y*L_z digits in {0,...,15}. No higher digits may be present. Tile specifies the fundamental periodic cell, and Patch specifies additions at coordinates 0<=i<L_x, 0<=j<L_y, 0<=k<L_z. In particular, imposing the binary subset relation

    Patch subset 15 G(32,L_x L_y L_z)

is exactly the Patch digit contract. A paid three-bitplane construction with the 2-bit and 4-bit planes disjoint can enforce the Tile contract. Subset and disjointness must be implemented rather than treated as unpriced primitives.

### Exact block-spreading lemma

Let beta be a positive power of two, n>=1, s>=n+1, and 0<=T<beta^n. Define

    Spread(T;beta,n,s)
      = [T G(beta^(s-1),n)] AND [(beta-1) G(beta^s,n)].

Here AND is ordinary bitwise conjunction, supplied by a paid arithmetic predicate. If T=sum_{i<n}t_i beta^i with 0<=t_i<beta, then

    Spread(T;beta,n,s)=sum_{i<n}t_i beta^(si).

Proof: before AND, the product has terms t_i beta^(i+(s-1)j), 0<=i,j<n. The exponent intervals [(s-1)j,(s-1)j+n-1] are disjoint because s-1>=n. Thus no coefficients collide or carry. A selected exponent sk equals i+(s-1)j only if i-j=s(k-j); since |i-j|<n<s, this forces i=j=k. Finally beta is a power of two, so beta-1 is a full block of bits and the mask selects complete beta-digits exactly.

Geometric series are enforced by (R-1)G=R^n-1, with a separately paid POWER relation for every variable power. Since s>=n+1>=2 and beta>=2, R=beta^(s-1)>1 and no zero denominator occurs. The number of arithmetic relations and POWER calls per Spread is fixed, independent of n. No loop with n witnesses is used.

### Simultaneous containing dimensions

Choose t_x,t_y,t_z>=2 and put

    a=p L_x t_x, b=q L_y t_y, c=r L_z t_z,
    A=2a, B=2b, C=2c,
    lower corner=(-a,-b,-c).

Choose t_x large enough that

    A/p = 2 L_x t_x >= qr+1,
    A/L_x = 2p t_x >= L_y L_z+1,

and t_y large enough that

    B/q = 2 L_y t_y >= r+1,
    B/L_y = 2q t_y >= L_z+1.

These are fixed polynomial inequalities with natural slacks. Such choices always exist, and can be made arbitrarily large to contain any finite odometer support. The lower corner is period-aligned. For the shifted Patch, a>=2L_x, b>=2L_y, c>=2L_z; hence its entire support is strictly inside the cuboid.

As before set X=32^A, Y=32^(AB), Z=32^(ABC). Apply four spreads:

    T_1 = Spread(Tile; 32^p, qr, A/p),
    T_2 = Spread(T_1; 32^(Aq), r, B/q),
    P_1 = Spread(Patch; 32^L_x, L_y L_z, A/L_x),
    P_2 = Spread(P_1; 32^(A L_y), L_z, B/L_y).

All ratios above are the displayed polynomial expressions, so no variable divisibility is being assumed. Their semantic outputs are exactly

    T_1 = sum h(i,j,k) 32^(i+A j+Aq k),
    T_2 = sum h(i,j,k) 32^(i+A j+AB k),
    P_1 = sum delta(i,j,k) 32^(i+A j+A L_y k),
    P_2 = sum delta(i,j,k) 32^(i+A j+AB k).

The second-stage input length hypotheses hold: T_1<32^(Aqr)=(32^(Aq))^r and P_1<32^(A L_y L_z)=(32^(A L_y))^L_z. In the first case its largest possible exponent is (p-1)+A(qr-1)<Aqr because p<=A; the Patch case is identical.

Now define

    H = T_2 G(32^p,A/p) G(32^(Aq),B/q) G(32^(ABr),C/r),
    D = 32^(a+A b+AB c) P_2.

The background repetition has unique coordinate remainders modulo p,q,r, so every digit appears exactly once and no carries occur. H is exactly the periodic background restricted to the cuboid. The shift exponent is precisely the lex index of global coordinate (0,0,0), so D is the exact complete input addition stream. No additions are outside this cuboid. Background digits are at most 5 and Patch digits at most 15; hence the initial height is at most 20 and the endpoint equation's left coefficients are at most 26<32.

The same interior mask and six neighbor equations from Sections 3-6 apply unchanged. In this uniform variant p,q,r are **input variables**, so expressions such as X^q, Y^r, 32^p and 32^(a+A b+AB c) are variable powers and must all be paid. They cannot be counted as the literal-exponent polynomials of Section 2.

### What the uniform code does and does not establish

This gives a fixed-arity paid decoding architecture for a raw periodic-plus-finite sandpile code once explicit POWER and AND/subset gadgets are substituted. Eight descriptors can be packed into one ordinary natural input by seven fixed Cantor-pairing relations

    2c=(a+b)(a+b+1)+2b,

using a fixed nesting order. Positivity of the six dimension descriptors must be imposed. Injectivity of Cantor pairing prevents the decoded descriptors from being freely guessed. This code represents raw sandpile data; it does not itself implement an arbitrary program's published U15/sandpile loader.

The construction also does not assume the one-shot property for every raw Tile/Patch instance. With binary U it recognizes precisely the raw instances admitting a binary finite stabilizing potential. To identify this with all finitely stabilizing instances of a selected universal loader, one still needs that loader's binary-odometer theorem. Ordinary examples can stabilize with repeated topplings and will not have such a witness.

Anchoring the finite Patch at nonnegative coordinates is explicit input semantics. Any finite signed-coordinate addition can be translated by multiples of the three periods into that form without changing the background, and finite stabilization is translation invariant. Target-site firing is a different question and would require translating or separately encoding the target.

## Provenance and verification

Source inspected as inert data through the read-only GitHub connector:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_sandpile35_36_intake.md

Observed Git blob SHA: 7a0c927b2469acceeedd2f9de1a9654be9af7928.

The source reports stable background values {0,4,5}, the literal periods above, conditional one-shot/binary firing, and halting equivalence to finitely many total topplings. It explicitly does not freshly verify the huge physical graph or program-to-tape encoder. Those limitations remain in force here. No upstream code was executed, and no repository file was written.

The companion locally authored check_periodic_packing.py verifies the geometric identities, interior-mask equations, six shifts, and folding-shell lemma on finite fixtures. Those checks support the algebra above; they do not authenticate the universal loader.
