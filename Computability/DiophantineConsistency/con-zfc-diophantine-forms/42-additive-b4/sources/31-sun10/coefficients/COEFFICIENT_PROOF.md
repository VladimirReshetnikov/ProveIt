# A 121 by 8801 coefficient compiler

## Result and source boundary

This construction combines the mixed-radix clause fields and short spatial
transport of package 25 with the arbitrary-odd-factor rank controller of
package 24. It retains the literal 943-tile language of packages 25 and 27.
The source snapshot is ProveIt commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`.

The resulting complete coefficient tuple has

    rho = 2^121, L = 8801, d = 121*8801 = 1,064,921, B = 2^d.

Its largest port K has 1,070,004 bits, versus 1,958,376 bits in packages 25
and 27. Its four unsigned binary payloads total 533,099 bytes, versus
977,220 bytes. The decrease is 45.36% in maximum port bit length and 45.45%
in total raw payload size. All four new ports are smaller than the
corresponding ports of either previous tuple. Compression is reported
separately and is not the coefficient-height criterion.

The new statement is an ordinary mathematical compiler adapter. It uses
the previously proved marked Wang-language/native-Pell interface and the
K215 endpoint. It is not a new Lean or Rocq certificate. In particular,
the finite program does not establish the inherited semantic endpoint.
Every input table and proof copied into `upstream/` retains its original
role; the builder does not execute those copied proof files.

## 1. Literal recipe

The ordered tiles are exactly `upstream/wang943_tiles.json`. They are
quadruples in west, north, east, south order. The program reconstructs the
entire list from the 430 literal actions in `upstream/k215_transitions.json`.
Start is selector 0; the globally impossible tile is selector 1; the other
941 tiles are lexicographically ordered. No tile is changed or removed.

Let

    E = {0,...,942} union {983,...,992} union {1003,...,1032}
        union {1063,1064,1095,1096,2195,3296}.

Thus |E|=989. The four copy offsets, in slot order, are
1023,1013,1003,983. The four anchors are 1095,1096,2195,3296.
The two dummy positions 1063 and 1064 have clause coefficient zero.

Set W_j=2^(10+2j), for 0<=j<44. If tile i has slot labels x_it, put

    c_i = 1 + sum_(t=0..3,j=0..9) bit_j(x_it+512) W_(10t+j)
              + W_40+W_41+W_42+W_43.

At copy exponent offset_t+j put c_e=W_(10t+j). At the four anchors, in
the listed order, put c_e=W_40,...,W_43. Finally c_1063=c_1064=0.
Set

    mu = 1022 + sum_(j=0..43) W_j,
    Z = (2^119-1) sum_(e=8792..8798) rho^e
        + (2^27-1) rho^8799.

Define the fixed integers

    DC = rho^30+rho^62+rho^1100+rho^2200
         + sum_(e in E) c_e(rho^(4393-e)+rho^(5495-e)),
    DR = rho^42,
    MC = B-1-sum_(e in E,e!=1)rho^e-2rho^1063,
    MF_native = 4+mu(rho^4393+rho^5495)
                +sum_(j=0..9)(rho^(1013+j)+rho^(1065+j))
                +rho^2195+rho^3296+Z.

The actual four ports, always replaced as one tuple, are

    beta = B-1,
    K = DC+B*DR,
    MC,
    MF_source = MF_native+B-1.

These are fixed integers given by bounded finite arithmetic, independently
of whether K215 ever halts. In every downstream circuit, the MF input is
MF_source, not MF_native. A port tuple assembled from different packages
does not instantiate this theorem.

## 2. Clause decoding and finite geometry

The mixed clause proof is inherited without changing a clause coefficient.
For clarity its crucial order of argument is repeated. If n selectors are
active, 0<=n<=943, and the low ten bits of the clause sum equal n exactly:
all other contributions are multiples of 1024. The low mask 1022 forces
n in {0,1}. This does not assume that the upper digits are carry-free.
Once n is 0 or 1, each radix-four field is a selected Boolean tile bit
plus a Boolean copy, or n plus a Boolean anchor. Its value lies in {0,1,2}.
The masked low bit permits precisely 0 and 2. It follows that the copies
are the tile's bits and all anchors equal n, or all are zero when n=0.

The smaller rho still has room for every pre-decoding clause sum: the
global carry estimate is checked independently below. Shortening L does
not change any ordinary coefficient convolution.

For each j from 0 through 9 the exact overlap identities are:

| Target exponent | DC source | DR source | Temporal source |
|---|---|---|---|
| 1013+j | 983+j | absent | 1013+j |
| 1065+j | 1003+j | 1023+j | absent |
| 2195 | 1095 | absent | 2195 |
| 3296 | 1096 | absent | 3296 |

At both clause targets T=4393,5495, the coefficient of rho^(T-e) in DC
equals c_e for every e in E, and DR has no contribution. These statements
give 69,230 exact scalar checks (22*989*3 + 2*989*2). Linearity makes the
checked identities valid for every native assignment, not merely for
one-tile assignments.

The two modular support identities are

    {(4393-e) mod8801:e in E} intersect
    {(5495-e) mod8801:e in E} = empty,

    {(2195-e) mod8801:e in E} intersect
    {(3296-e) mod8801:e in E} = {0}.

They may be checked over the 989-element support, or seen from the
unchanged difference arguments: 1102 is absent from E-E, while 1101
occurs only as 3296-2195. The span 3296 is less than half of 8801,
so reducing modulo 8801 introduces no extra difference in either test.
The source binary-alignment argument applies for b=121 exactly as for
b=125: offsets 1,...,b-2 yield even tested digits, and offset b-1 has
only the single possible upper-dummy odd spill. Two distinct occupied
anchors exclude both alternatives; the displayed intersection then forces
a whole native-cell shift. The clean clause, copy equalities, and anchor
tests therefore recover exactly the same marked periodic Wang language.

## 3. Carries, padding and parity

The conservative pre-decoding bound used by both source adapters is

    mass = (989+2)(2 sum_e c_e+6),
    threshold = max(4mass+8, 2mu+4, 16)
              = 789998487493936316431751375694647416.

It satisfies

    2^119 < threshold < 2^120 < 2^121.

Thus b=121 is sufficient; it is the least odd width for this unchanged
bound. This is a restricted observation, not global optimality.

The largest unshifted exponent in a DC/native product is
5495+3296=8791. The DR/native product and the temporal native term end
earlier. The global bound prevents carries to the next radix position.
Consequently the eight padding cells 8792,...,8799 are identically zero
for every aligned intended assignment, including every permitted dummy
change. Their tests impose no additional completeness restriction.
Soundness simply discards these extra zero tests when decoding a tiling.

The padding contributes 7*119+27=860 bits. Its largest digit also obeys
2(2^119-1)+4<2^121. The core native high mask has 2*53+20+2+1=129 bits.
Thus the materialized masks satisfy

    popcount(MF_native)=989,
    popcount(MC)=d-989,
    0<MC,MF_native<B-1,
    MC=2 mod4, MF_native=4 mod8.

These are the precise population and low-bit hypotheses of the inherited
inverse-population/Pell interface. The masks themselves are not required
to be mutually disjoint; each constrains its own corresponding packed data.

## 4. A short explicit controller for the actual packed rank

The power-of-five controller cannot simply be reused because d is no
longer a power of five. Package 24's arbitrary-odd-factor controller,
with new explicit parameters, resolves this issue.

Factor d=11^2*13*677. Let lambda=2341, a prime, and k=lambda-1=2340.
Exact arithmetic gives

| Modulus | 121 | 13 | 677 | 2341 |
|---|---:|---:|---:|---:|
| Order of B | 10 | 12 | 52 | 60 |

In particular ord_d(B)=780 divides k. Moreover

    B^2340 mod2341^2 = 2556373 = 1+1092*2341,

and 2341 does not divide 1092. Thus v_lambda(B^k-1)=1.
With H0=1+B*DC+B^2(DR+1), the complete unit certificate is:

| Prime p | B mod p | DC mod p | DR mod p | B^2-1 mod p | H0 mod p |
|---|---:|---:|---:|---:|---:|
| 11 | 2 | 5 | 4 | 3 | 9 |
| 13 | 6 | 1 | 12 | 9 | 7 |
| 677 | 611 | 38 | 643 | 293 | 654 |
| 2341 | 2100 | 2051 | 586 | 1896 | 1225 |

The following argument proves unbounded completeness, beyond those finite
certificates. Choose independently sufficiently large powers of lambda
for the spatial width w and temporal height h, and put N=wh=lambda^n,
q=B^N. The unchanged language permits arbitrary sufficiently large
independent rectangular padding, so these dimensions are available for
every finite blank halting run. Require N>d*lambda^2 and h>lambda.

Since the relevant orders divide lambda-1,

    q congruent to B^w congruent to B (modulo d*lambda).

Activating the lower dummy at exponent 1063 in cell j changes the actual
packed Pell index, exactly as in the source compiler, by

    delta R = -Gamma B^j,
    Gamma = rho^1063(q^2-1)[1+q(DC+B*DR+B^w)].

The table shows that Gamma is a unit modulo d*N: every prime factor of
d*N is listed, and both factors in its bracket and q^2-1 are nonzero.

### Boolean coverage lemma

Put T=N/lambda and C0=d*lambda; then d*N=C0*T and T>C0. Every residue
modulo d*N is a Boolean subset sum of

    {B^(2+k*j): 0<=j<T} union {B^3}.

Proof. Since B^k=1 mod d, and v_lambda(B^k-1)=1, binomial lifting gives
ord_(lambda^n)(B^k)=lambda^(n-1)=T. Its first T powers are therefore
exactly the T distinct residues 1+C0*z, z modulo T, in modulus C0*T.

Normalize the target residue by the unit B^2. Choose epsilon in {0,1}
so that the normalized target minus epsilon*B is nonzero modulo lambda.
Let a be its least residue modulo C0. Then 1<=a<C0<T and gcd(a,T)=1.
Write the remaining target as a+C0*u. Solve

    a*z0+a(a-1)/2 = u modulo T.

The a orbit entries with additive coordinates z0,z0+1,...,z0+a-1
modulo T are distinct, and their sum is a+C0*u. Include B^3 if and
only if epsilon=1. After restoring the B^2 factor this gives the target.
No dummy position is selected twice.

The largest available cell index is

    2+(lambda-1)(N/lambda-1)=N-N/lambda-lambda+3.

Since h>lambda, w<N/lambda; every selected index and its translates by
one and w stay below N. The extra index 3 is distinct from 2+k*j
because k>1. Thus the allowed dummy changes are exactly the safe
nonwrapping changes required by the inherited rank formula. This proves
the lemma.

Starting with all control bits zero, let R0 be the actual packed index.
Apply the lemma to (R0-d*w)*Gamma^(-1) modulo d*N. The resulting index
satisfies R=d*w modulo d*N. This is the exact temporal rotation required
when the main Pell witness sets X=2^R. The carry/slack inequalities,
clause fields, and external zero padding remain valid under every selected
dummy change. Hence the native/Pell completeness construction goes through.

## 5. The signed completeness promises also transfer

The dimensions b,L,d,N are all odd. Put t=d*N, so q=2^t. The canonical
single-Start encoding still has C=1 mod4. The source shifted packing
identities give R=3 mod4 and popcount(R)=3t+2 from precisely the mask
population balance established above. Dummy control changes neither fact.
Consequently the canonical scale X/q=2^(R-t) is a positive integer square.

The canonical main Pell parameter is even. Its coordinate c=psi_A(R)
is odd. Taking the strong auxiliary index c*R yields the same odd
positive multiplier promised in the source normalized and ordinary
interfaces. The authentic half-binomial valuation gives v2(Y)=3t,
so the scale s=Y/q^3 is odd as well. These are the additional completeness
requirements used by the existing unrestricted-integer reductions.

Thus the whole tuple may replace the prior Wang943 tuple in every form
whose proof uses this complete native interface, including the compatible
positive and signed arithmetic skeletons. A raw tiling equivalence or a
modular unit check alone would not justify this conclusion; the actual
rank adjustment, positive slack, and parity promises above are required.

Composing with the inherited arithmetic skeleton proof and K215 endpoint
yields, in ordinary mathematics formalizable in ZFC, the same equivalence
between solvability and existence of a finite ZFC refutation. Negating
gives the requested equivalence between absence of solutions and Con(ZFC).
This is not a proof that either side holds.

## 6. Reproduction and attribution

Run `python3 build_coefficients.py`. It reconstructs the literal tile list,
checks the full finite convolution table, decoder fields, support geometry,
carry bounds, modular orders, valuation-one witness, masks, byte round trips
and hashes. It regenerates all four raw and gzip payloads, plus
`COEFFICIENT_BINDING.json`, using the Python standard library only.

The arithmetic operation count and polynomial degree of a downstream
skeleton are unchanged by rebinding fixed ports. No reduction in variables
or gates is claimed for this adapter itself. The raw-data decrease is
achieved by removing two independent power-of-five roundings and choosing
a compatible explicit completeness controller.

The literal language, source compiler, machine data and foundational proof
are credited to the pinned ProveIt developments and their retained notices.
The mixed-radix clause and short-transport geometry are credited to package
25 (also independently present in package 27); the general Boolean orbit
controller is credited to package 24. The present contribution is their
fully checked joint instantiation at b=121,L=8801,lambda=2341.

