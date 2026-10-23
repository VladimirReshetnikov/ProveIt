# Complemented receivers with a shared parity anchor

## Result and status

This is a separate coefficient improvement at ProveIt commit
124c07c0b77a9e20e84676514d8b1ff78536ea3f. It is **not** a rebinding of the
main low-variable equations in this delivery. It supplies a complete new
native coefficient tuple for compatible K215 native/Pell arithmetic
skeletons:

- rho = 2^89, cell length L = 4831;
- B = rho^L = 2^429959;
- 457 unary selector modes, 17 receiver payload bits, 42 copied label bits,
  two standalone anchors, and two dummy positions;
- 520 supported native positions;
- four raw coefficient ports occupy 215492 bytes;
- the largest port has 434054 bits.

The previously complete source44 tuple has B=2^590069 and 295388 raw bytes.
The new raw tuple is 27.0478% smaller. It changes coefficient heights, not
the witness counts or operation counts of a compatible fixed arithmetic
skeleton. No global optimum is asserted.

The proof is ordinary mathematics formalizable in ZFC, composed with the
same inherited native/Pell compiler, marked-Wang-language and K215/refutation
calibration used by sources36,40,44. It is not a new end-to-end Lean/Rocq
certificate. The new local decoder and finite interface are proved below;
the inherited unbounded semantic theorems remain explicit dependencies.

## 1. Inherited factorized tile language

Retain source40's 457 selector modes: the 455 relabelled nonreceiver tiles
from the literal 943-tile K215 Wang language, and two receiver modes

    R = (256,0,0,512),       L = (0,0,512,512).

For Boolean auxiliary bits define QR,QL in {0,...,255}, and u in {0,1}.
An occupied right receiver expands to

    (256+QR, u, 0, 512+2QR+u),

with QL=0; an occupied left receiver expands to

    (0, u, 512+QL, 512+2QL+u),

with QR=0. For any other occupied mode all auxiliary payloads vanish.

This is the same finite receiver factorization as source40, not a newly
discovered smaller Wang language. Its occupied expansion contains 1479
tiles. Exactly 536 expanded receiver tiles have a direction/state label
which occurs on no matching opposite edge; the inherited forbidden tile
also has an unmatched edge. Removing these impossible tiles gives exactly
the relabelled literal 943-tile language minus its forbidden tile. The
independent finite audit reconstructs this fact from the 430 actions of
K215, without running the machine.

The new arithmetic clause changes how these modes are encoded. Its main
ideas are to complement the edge code, double the horizontal labels, and
use a label's parity bit as the current synchronization anchor. Unlike
source40's unfinished original decoder, the resulting decoder permits no
nonzero payload in an empty cell.

## 2. Gates and the new aggregate payload

The low selector field has nine bits. Let n be the selector count, and
alpha,beta the right- and left-receiver selector bits. Use the same three
gate fields as source40:

    GR = 255(n-alpha) + QR,
    GL = 255(n-beta) + QL,
    Gu = n-alpha-beta + u.

Their units are 2^9, 2^18, 2^27. The masked gate bits are 2^17,
2^26,2^28. The selector mask is 510.

Because 0<=n<=457<512, the low selector mask forces n=0 or1 without any
assumption about higher carries. After that, GR,GL lie in [0,510], and Gu
lies in [0,2]. Thus there is no carry between these three fields or from
them into bit29. When n=1 the tested ninth bits of GR and GL force the
inactive direction's payload to zero, and the tested second bit of Gu
forces u=0 on nonreceiver modes. For n=0 these gates alone allow payloads;
the aggregate equation below excludes them.

Put T=2^42, M=4T=2^44 and H=29. For a selector mode
t_i=(w_i,n_i,e_i,s_i), define

    Li = 2w_i + 2^11 n_i + 2^21 (2e_i) + 2^32 s_i.

The four label field widths are 11,10,11,10. The horizontal labels are
doubled. Their matching relation is unchanged. Define the auxiliary
increment

    V = 2QR + 2^11 u + 2^21 (2QL)
        + 2^32 (2QR+2QL+u).

In an occupied valid mode, Li+V is exactly the packed label vector of its
expanded tile and lies in [0,T). In an empty cell, 0<=V<T: the south
field is at most 1021, and all other fields fit their stated widths.

Let Z be the 42-bit vector of copied edge bits, in the above field order.
Let y be its least significant bit, the west copied parity bit. There
are only two additional Boolean anchor bits A1,A2. Define

    W = Z + T(y+A1+A2).

The west bit is deliberately counted twice: once at its actual label
position and once in the field counting the three Boolean values. This is implemented by a
single native coefficient 2^29(1+T) at the west low-bit position. The
top field is a count from0 to3, not three separate binary positions.

The coefficients implement the congruence

    sum_i x_i(1+Li) + V + W = 0 mod M.                  (1)

It is enforced by masking all 44 payload bits beginning at bit29.
All coefficients are nonnegative. In particular, each receiver payload
bit has its small **positive** increment coefficient. This avoids the
large per-bit complement coefficients that arise from directly combining
sources40 and44.

### Local decoder theorem

The complete masked clause accepts exactly:

1. the all-zero selector/copy/anchor/payload assignment (the ignored dummy
   digits remain arbitrary in their permitted ranges); or
2. one selected mode, its correctly gated receiver payload, all copied
   labels complemented within their field widths, and A1=A2=1.

Proof. First extract n=0 or1 and the gate consequences as above. All Li
and V are even. Taking (1) modulo2 therefore gives y=n.

If n=0, then y=0 and W=Z+T(A1+A2)<3T. Since V<T,

    0 <= V+W < 4T=M.

Equation(1) forces V+W=0. Both terms are nonnegative, hence V=W=0.
Every positive-coefficient auxiliary bit is zero; all label copies and
both anchors are zero. This proves the exact empty-cell assertion,
including every formerly problematic receiver payload.

If n=1, the gate conditions give 0<=Li+V<T, and 0<=W<M. Consequently

    0 < 1+Li+V+W < 2M.

Equation(1) forces this sum to equal M, so

    W = M-1-(Li+V)
      = 3T + (T-1-(Li+V)).

Thus y+A1+A2=3, so each is1, and Z=T-1-(Li+V). The latter identity is
precisely bitwise complementation in the four separate fields: all fields
fit, so no field borrows are required. Both horizontal labels before
complementation are even; their complemented low bits are consequently1,
including the west bit y already used in the anchor count.

Conversely every such occupied assignment gives payload sum exactly M
and passes the gates; the zero assignment gives sum0. QED.

This proof is a uniform interval/congruence argument. Exhaustive finite
checks of actual receiver expansions supplement it; they are not its
logical basis.

## 3. Complete fixed coefficient recipe

Use the ordered mode list from Section1. The selector support is0..456.
Copied west bits occupy539..549, north528..537, east517..527 and
south495..504. The auxiliary QR bits occupy567..574, QL575..582, and u583.
Dummies are507,508. The standalone anchors are1203,1807.
There is no native position600 in the new support.

Let E be their union, |E|=520. For mode i put

    ci = 1
         + 255*2^9*[i is not right receiver]
         + 255*2^18*[i is not left receiver]
         + 2^27*[i is not either receiver]
         + 2^29*(1+Li).

Give the copied label bit at payload position j coefficient2^(29+j).
Additionally add2^71 to the coefficient at native position539.
At each standalone anchor put2^71.

For QR bit j put

    c_(567+j) = 2^(9+j) + 2^29*(2^(j+1)+2^(33+j)),

and for QL bit j put

    c_(575+j) = 2^(18+j) + 2^29*(2^(22+j)+2^(33+j)).

Put

    c_583 = 2^27 + 2^29*(2^11+2^32),

and put both dummy coefficients equal to zero. The clause mask is

    mu = 510 + 2^17 + 2^26 + 2^28 + 2^29*(2^44-1).

It has55 set bits.

Now fix rho=2^89,L=4831,B=rho^L and

    DC = rho^33 + rho^68 + rho^664 + rho^1268
         + sum_(e in E) ce*(rho^(2409-e)+rho^(3015-e)),
    DR = rho^46,
    Zpad = (2^87-1)*(rho^4823+rho^4824+rho^4825+rho^4826)
           + (2^38-1)*rho^4827,
    MC = B-1 - sum_(e in E, e!=1) rho^e - 2rho^507,
    MF_native = 4 + mu*(rho^2409+rho^3015)
                + sum_(j=0..9) rho^(528+j)
                + sum_(j=0..10) rho^(585+j)
                + rho^1203 + rho^1807 + Zpad.

The four actual ports are

    beta=B-1, K=DC+B*DR, MC, MF_source=MF_native+B-1.

The fourth port is shifted. No port may be mixed with another tuple.

## 4. Native synchronization and soundness

The complete basis identities are:

| Tested target | Current DC contribution | Spatial DR contribution | Temporal contribution |
|---|---|---|---|
|528+j,0<=j<10|495+j|none|528+j|
|585+j,0<=j<11|517+j|539+j|none|
|1203|539|none|1203|
|1807|539|none|1807|

At each clause target2409,3015, the current coefficient at source e is
exactly ce, and the spatial contribution is zero. The independent audit
checks all37960 scalar identities, so the statements hold by linearity
for every native assignment, including dummy values0..3.

The source-anchor position has changed from600 to539. Its bit is now the
west parity bit y. The two tested temporal anchors remain distinct.
For every native assignment the finite support conditions are

    ((2409-E) mod L) intersect ((3015-E) mod L) = empty,
    ((1203-E) mod L) intersect ((1807-E) mod L) = {0}.

They follow either by finite arithmetic or from the following short
difference argument. The low support is contained in[0,583]; the two
remaining high positions are1203 and1807. The clause gap606 is absent
because1203-606=597 and1807-606=1201 are absent, and606 exceeds the
low span. The anchor gap604 occurs only as1807-1203:
1203-604=599 is absent. Since L>2*1807, no additional circular differences
occur.

Consider an arbitrary arithmetic solution. At Start, the native origin
constraint forces selector0 present. The clean-band property supplies
an uncontaminated clause, so the local decoder gives n=1, y=1 and both
standalone anchors1. Each temporal anchor test therefore requires an odd
rotated digit at its distinct target.

Write the temporal binary rotation as89t+epsilon,0<=epsilon<89.
For1<=epsilon<=87, every rotated native radix digit is even: all
supported digits are Boolean except the designated two-bit dummy.
At epsilon=88 only the single upper-dummy spill in each native cell can
be odd. It cannot meet the two distinct anchor targets. These are the
same source parity estimates, with unchanged dummy geometry and the
verified carry bound below. Therefore epsilon=0. The unique anchor
intersection then forces t=0 modulo4831. Thus the temporal rotation is a
whole number of native cells.

Once aligned, every local clause is accepted and has either an exact
occupied mode or an empty cell with only ignored dummy digits. Spatial parity at the west/east low
copy positions matches an occupied current east bit1 to its neighbor's
west bit. The local decoder says that west bit is n. Starting at Start
and iterating the spatial shift by one native cell visits the whole cyclic
word, so every cell has n=1. All copied complemented label fields match;
complementation and horizontal doubling are injective on the allowed
label sets, so they give exactly the same Wang matching relations.
Removing unmatched expanded receiver tiles recovers the literal marked
K215 Wang tiling. The inherited language theorem then yields a blank
K215 halt, hence a finite ZFC refutation.

This is an explicit synchronization proof. It does not assume that empty
cells carry no payload before proving the local decoder; that property
has already been established uniformly in Section2.

## 5. Carry, population and completeness

All new coefficients are nonnegative. The inherited conservative mass is

    mass=(520+2)*(2*sum(ce)+6)
        =21943453599356796577770480,

where sum(ce)=21018633715859000553417. Direct exact arithmetic verifies

    max(4*mass+8,2*mu+4,16) < 2^89.

Also 2(2^87-1)+4<2^89. Therefore all source no-carry, nonaligned-rotation,
and strict-positive-raw-slack estimates remain valid.

The maximum unshifted product exponent is3015+1807=4822. Every added
padding bit at4823..4827 is therefore zero on a canonical aligned
computation, even after safe dummy changes. The padding population is

    4*87+38=386.

The other high-mask population is2*55+10+11+2+1=134. Consequently

    pop(MF_native)=520, pop(MC)=429959-520,
    MC=2 mod4, MF_native=4 mod8,
    0<MC,MF_native<B-1, 0<DC<B.

These are checked on the actual large integers as well as from their
defining supports.

For completeness fix the prime lambda=106261 and k=lambda-1=106260.
The following exact certificates hold:

    d=429959=89*4831,
    ord_d(B)=26565 divides k,
    B^k mod lambda^2=8376873414 !=1,
    B^k=1 mod lambda.

Thus v_lambda(B^k-1)=1. For H0=1+B*DC+B^2*(DR+1):

|Prime p|B mod p|(B^2-1) mod p|H0 mod p|
|---:|---:|---:|---:|
|89|4|15|44|
|4831|840|273|3664|
|106261|93141|97840|51423|

All controller factors are units. Choose the inherited independently
padded helical width w and height h as sufficiently large powers of
lambda, and put N=wh=lambda^r, q=B^N. Require N>d*lambda^2 and h>lambda.
Then q=B^w=B modulo d*lambda.

Changing a safe low dummy bit in native cell j changes the actual packed
rank by

    delta R = -Gamma*B^j,
    Gamma = rho^507*(q^2-1)*[1+q*(DC+B*DR+B^w)].

The unit table gives gcd(Gamma,dN)=1. The unchanged Boolean prime-padding
lemma applies: with T=N/lambda and C0=d*lambda, the orbit of B^k runs
through exactly the T classes1+C0z modulo C0T=dN. Every desired residue
is a Boolean subset sum of the weights B^(2+kj),0<=j<T, together with
B^3. Indeed normalize by B^-2, subtract epsilon*B for epsilon0 or1 so
the remaining residue is nonzero modulo lambda, choose its least residue
a modulo C0, and solve

    a*z0 + a(a-1)/2 = u mod T.

Since1<=a<C0<T and gcd(a,T)=1, a consecutive cyclic block of a orbit
coordinates gives the required sum. No weight is used twice. The largest
cell index is at most N-T-lambda+3, and w<T, so all required translated
dummy positions remain below N and avoid the origin.

Apply this to (R0-dw)*Gamma^-1 modulo dN. The resulting actual rank
satisfies R=dw mod dN, exactly the required temporal rotation. The
canonical tiling, masks, strict slack and copied labels survive.
The inherited Pell converse supplies all remaining witnesses.

Finally d and N are odd. The unchanged low-origin condition gives C=1
mod4, and the population identities give the same canonical rank
pop(R)=3dN+2 and R=3 mod4. Thus the usual square-scale and odd-multiplier
promises remain available to compatible signed-domain adapters.

## 6. Use, artifacts and attribution

The tuple may replace all four ports of a native arithmetic skeleton
whose correctness theorem uses precisely the imported native interface
proved above. The parameterized correctness proof composes with the
K215/refutation calibration, giving the same ZFC-provable equivalence of
unsolvability and Con(ZFC). This is a coefficient-interface theorem.
The main ten-integer and nine-natural polynomials in the present delivery
retain their previous complete source31 binding.

Reproduce with Python3:

    python3 build_separated.py
    python3 audit_separated.py

The first materializes the fixed coefficient bytes. The second is an
independent reconstruction from the literal K215 actions; it does not
import either builder. Normal and optimized Python executions are both
required. The finite checks establish exactly their stated finite
identities; they do not decide K215 halting or ZFC consistency.

Inherited material is from:
- source36: literal K215 actions and complete original Wang language;
- source40/research_candidate: 457 receiver modes, gate design and the
  starting compact geometry;
- source44/native: aggregate complement principle and prime-padding
  interface proof.

The new contribution is the complemented doubled-label encoding, its
positive auxiliary coefficients, the reuse of one copied parity bit in
the aggregate anchor count and synchronization source, the exact empty
cell theorem, and the new complete tuple. Original source notices and
licenses accompany those source files.
