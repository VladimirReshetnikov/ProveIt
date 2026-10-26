# Factorial-free pooled power certificates for a fixed consistency quartic

Prepared for ProveIt on 25 October 2026, with AI assistance. This document
proves the new composition used in `composed/differences223/equation.json`.
Later exact integer projections are proved separately. The equation has
223 unrestricted integer coordinates, 160 quadratic residuals, total degree
four, 7,801 collected monomials, and coefficient height 128,446.

The comparison snapshot is
`953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`. The exact arithmetic source is
`157-linear-crt/source/equation.json` in
`Computability/DiophantineConsistency/con-zfc-diophantine-forms`, with Git
blob `0de72d57e14aca0c7ed0b97fc05676b6e5a63153` and SHA-256
`50f88c245d3a32b5c041924ea4ac07b9149e5da24c859f3a167ea984d93e18d2`.
It has 242 integer coordinates and 178 quadratic residuals before its
package's optional final affine projections. All fixed coefficients are
literal small integers; there is no uninstantiated universal-polynomial
parameter.

## 1. Inherited logical and arithmetic interface

Source 157's ordinary proof establishes that its arithmetic system has an
integer zero exactly when the calibrated numerical proof calculus C222
has a finite refutation. The identified logical translations are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. They identify this
with a finite syntactic ZFC refutation. These translations, the numerical
syntax construction, the CRT/binomial decoding, and the signed simultaneous
Pell-frame theorem are inherited interfaces, not newly compiled
proof-assistant theorems in the present submission.

We retain the following semantic choices of source 157:

    t = 16 + 4 d^2,        F = t^t,        R = F,
    C = 2 c,              H = 2 + 4(C + A_1 + ... + A_8),
    y = F(2 v + 1).

Here C and the A_i are the actual CRT representatives. Stored coordinates
may include affine shifts, which the exact frame and row checks account
for. In particular the coordinate named `y` is the actual value y+1;
`pow2.output` is q+1, `crt.encoded.a` is a+1, and
`crt.even_index_half` is C/2. The new proof always refers to actual values.

The inherited power graph gives canonical signed Pell pairs at parameter A
before recovering any sign of B, q, y, x, or the CRT representatives. Its
frame is an exact identity

    W = 2 + sum of 36 squares of actual affine atoms.

Consequently W >= 258, and every actual power base n, requested index k,
and proposed output m satisfies n^2, k^2, m^2 < W. The unchanged signed
frame theorem gives |A| > W^W. The independently reconstructed 36 atoms
and all 17 retained power requests are listed in `composed/FRAME_CHECK.json`.
In particular the list contains t, F, F+t, x, y+1, BH, q, q+1, C, the
derived label J, and every power output. A duplicate t square is harmless:
t is both a horizon and the base of the growth request F=t^t.

## 2. Strict cofinal ranges remove one complete power request

Five old binomial range tests used lower index t+1: the four local schema
parameters a,b,c,d and the full local derived-label expression J. Replace
their lower index by t. Their decoded conclusion is now

    0 <= a,b,c,d < t,      0 <= J(a,b,c,d) < t.

These imply the old weak bounds, so every old soundness argument based on
labels at most t continues to apply. This assertion concerns small local
tuples. The polynomial J on the large global CRT representatives remains
the cofinal semantic Pell anchor and is not required to be less than t.

For completeness, start with a finite proof tree. List every local rule
parameter and every full derived-label expression used by the tree and
the fixed truth-padding tuple. Choose t in the cofinal set 16+4d^2
strictly larger than the number of proof-tree expansion steps and all
these finitely many values. This happens before constructing F, the
pending-multiset path, y, x, or the CRT representatives.

The parent CRT construction uses precision 2x. If a local value w lies
in [0,t-1], its global representative a is congruent to w modulo p^(2xm)
for the selected prime-power component p^(xm) of N=B^x. The falling
factorial a(a-1)...(a-t+1) contains a-w. Since

    v_p(t!) <= t-1 < x <= xm,

division by t! leaves at least xm factors of p. Therefore p^(xm) divides
binom(a,t). Polynomial congruence gives the same argument for J. If
a<t, the binomial is simply zero. The parent one-sided prime-power range
lemma supplies the converse, so this stricter test has the needed two
directions at the new cofinal horizon.

All five new tests use the already present ratio M/q^t. Thus the separate
q^(t+1) power output, its congruence quotient, its private one-step Pell
discriminant coordinate, and the ratio M/q^(t+1) can be deleted. Its
square is removed from the frame; the frame still bounds every retained
request. This changes 242 coordinates and 178 rows to 238 coordinates
and 175 rows.

The literal operation is not the assertion that every old zero survives
at its old horizon. Completeness chooses a new sufficiently large horizon
and reconstructs the witnesses. The removed request was a derived
one-step pair, not an independent principal Pell pair.

## 3. A fixed-base pool uses two quadratic rows

This is source 158's proved pooling lemma, now instantiated on the
factorial-free source. Let n be a nonzero integer, let r<=15, and let
(X_i,Y_i) be the canonical signed Pell pair for the requested signed
index k_i, with Z_i=A Y_i. Put

    T = 2 A n - n^2 - 1,
    D_i = m_i - X_i + Z_i,
    H_0 = sum Y_i(m_i-X_i),
    S_0 = sum (D_i^2-Y_i^2).

Introduce two unrestricted integers K,L and impose the quadratic rows

    K - 2 H_0 - (2 A-n)L = 0,
    S_0 - n K + L = 0.

Eliminating K gives S_0-2nH_0=TL. The polynomial identity

    sum (D_i-nY_i)^2
      = S_0 - 2nH_0 - T sum Y_i^2

holds when Z_i=AY_i. Thus T divides the sum of squared power errors.
The canonical Pell group congruence identifies
X_i+(n-A)Y_i with n^(k_i) modulo T. Negative powers make sense modulo T
because T is -1 modulo n and therefore gcd(T,n)=1.

Set b=floor(sqrt(W-1)). The square frame gives
|n|, |m_i|, |k_i| <= b and b>=16. Multiplying by n^b clears every
negative index, so T divides the nonnegative integer

    E = sum [m_i n^b - n^(b+k_i)]^2.

All exponents displayed here are nonnegative. Each summand is at most
4 b^(4b), including n=1 or n=-1. Therefore

    0 <= E <= 4r b^(4b) < W^(2b+1) <= W^W.

The strict comparison uses 4r<=60<W, b^2<W, and
2b+1<=b^2+1<=W. On the other hand,

    |T| >= 2|A||n| - n^2 - 1 >= 2|A|-W > W^W.

It follows that E=0. Every power request is exact. For |n|>=2, a negative
k_i would imply m_i n^(-k_i)=1, impossible in integers, so k_i>=0.
At n=+/-1 the signed-index unit output is recovered, with no nonnegativity
claim for k_i.

Conversely, true integer powers and canonical Pell pairs make each
D_i-nY_i divisible by T. The displayed identity makes
L=(S_0-2nH_0)/T integral, after which
K=2H_0+(2A-n)L supplies both rows. This proves the existential equivalence
under the unchanged frame and canonical-pair hypotheses. It uses no
factorial authentication and does not require the base to be positive.

The new instance pools eleven requests at q+1 and three at q. It retains
the three initial individual requests

    F=t^t,      N=B^x,      q=(BH)^x.

For each pooled block, its old private congruence quotient for every
member and its one shared modulus coordinate disappear. The saving is
11+1-2=10 coordinates for q+1 and 3+1-2=2 for q, with the same savings in
rows. All fourteen principal Pell norm and AY rows remain.

## 4. The sign bootstrap is acyclic in the composed system

The preceding pool lemma requires only a nonzero base. We now show that
the signed-base facts needed at each use have already been established.

1. The retained individual growth request has the positive base and
   index t>=16. It gives F=t^t>=2^64. The horizon is divisible by four,
   so F is even.

2. The unchanged equation B h_B=C+F+1 has an odd right side because
   C=2c. Therefore B is odd and nonzero, without any prior sign premise
   on C. Also H is 2 modulo 4 for every signed tuple, hence |H|>=2 and
   |BH|>=2.

3. The retained individual request at BH gives x>=0 and q=(BH)^x.
   Since y=F(2v+1), y is nonzero and |y|>=F. Put L_0=1+(t+1)y;
   then |L_0|>1. If x=0, the terminal endpoint would give
   L_0 u_t=-1, impossible. Thus x>=1 and |q|>=2.

4. The q pool is now licensed. Its three indices are t, y+1, and x.
   In particular exactness of the request with index y+1 forces
   y+1>=0. But a negative y would satisfy y<=-F<-1. Hence y>=F>0.

5. In the initial endpoint x=F+1+(y+1)u_0, a negative u_0 would force
   x<=F-y<=0. Thus u_0>=0 and x>=F+1. The terminal endpoint then
   forces u_t>=1 and

       x >= 2+(t+1)y >= 2+(t+1)F.

6. Consequently |q|>=2^x and |q+1|>=2. The q+1 pool is now licensed.
   It recovers all actual representative signs and the nonnegative
   derived-label index. In particular H is positive.

The unchanged signed-binomial digit argument from source 157 now gives
B=binom(F+t,t)>0. Briefly, the bound just obtained makes every low
coefficient negligible compared with |q|; the common quadratic remainder
budget gives absolute remainder less than half the relevant denominator;
and the binomial identity holds also for negative q. Centered remainder
uniqueness authenticates the binomial digit. This yields B>=2 and then
q=(BH)^x>0 and N=B^x>0. All remaining ordinary range and CRT arguments
are now available.

No step assumed the sign recovered at that step. In particular the new
proof does not infer B>0 or representative nonnegativity before the
binomial digit is authenticated, and it does not reuse source 158's
factorial-dependent beta choice y=V-1. The affine odd multiplier of
source 157 is retained unchanged.

## 5. Remaining soundness and constructive completeness

With F=t^t, source 157 proves F>=lcm(1,...,t)^2, the binomial prime-power
selector/support theorem for B=binom(F+t,t), and label-multiset separation
for weights 1+jF. The local source ledger is bounded by R_0^E with
R_0=2+t+x+y+F<2x and E=2^23; the endpoint bound gives x>2^32 and
R_0^E<2^x. The common centered-remainder bounds recover all remaining
binomial digits. These arguments are unchanged except that five ranges
now have a smaller lower binomial index. Smaller ranges only improve the
old coefficient bounds.

The arithmetic boundary y=F is still excluded by the inherited local
flow argument: the initial beta accumulator would be zero, every decoded
local update preserves zero, and the final accumulator is one. Thus
y>F. The inherited positive-weight Horn-flow argument then extracts a
finite C222 refutation from any zero of the composed system.

For the reverse direction, choose the cofinal strict horizon described
in Section 2. Set F=t^t. Let O be the odd part of t!, choose a sufficiently
large odd multiple w of O, and put y=Fw. This has the required affine
form y=F(2v+1). Since v_2(F)=t v_2(t)>v_2(t!), it is divisible by t!
and can dominate every pending-multiset accumulator. Thus the beta CRT
construction and arbitrarily large x in its residue class remain
available. The oddness of B permits the representative parity choices
required by C=2c and the even dominant syntax anchor.

Construct all CRT representatives, their exact binomial digits, and q,
then the unchanged simultaneous Pell frame and canonical signed pairs.
Strict range divisibility is supplied by Section 2. The old common
remainder budget still has ample margin, since the canonical normalized
remainders are each smaller than M/32. Section 3 constructs the two
new integers for each pooled block. The private-wire and Pell coordinate
maps used below have integral polynomial inverses on the zero sets.
This constructs an integer zero from every finite calibrated refutation.

## 6. Exact algebra, final theorem, and verification boundary

Between the strict source and the pools, the private Horn-wire change of
source 158 replaces four private coordinates by one shared product F S,
and combines two private square outputs that only occur through their
sum. Its forward and reverse residual ideal identities are explicitly
checked: 172 forward identities and 175 reverse identities. This saves
three coordinates and three rows without changing existential integer
solvability. After pooling, fourteen unimodular affine changes use
U=X-Z, with inverse X=U+Z and the existing gate coordinate Z.
The retained equation Z=AY identifies U with X-AY on the common zero set.
One integer row operation subtracts the retained
norm rows from the orientation pool. These preserve all integer zeros
and keep every residual quadratic.

Thus the exact progression is

    242 coordinates / 178 rows   inherited factorial-free source
    238 coordinates / 175 rows   strict cofinal ranges
    235 coordinates / 172 rows   shared private Horn wires
    223 coordinates / 160 rows   two fixed-base power pools
    223 coordinates / 160 rows   Pell difference coordinates.

Let P223 be the sum of squares of the final 160 literal quadratic
residuals. Over unrestricted integers, P223=0 is equivalent to the
simultaneous vanishing of all those residuals. The preceding two
directions and the inherited syntactic calibration establish, by
ordinary finite arithmetic and syntax arguments formalizable in ZFC,

    exists z in Z^223 with P223(z)=0
        iff there exists a finite syntactic ZFC refutation.

Negation yields the requested internal equivalence with Con(ZFC).
Subsequent exact integral projections and reversible row operations
preserve it. This is neither a proof of consistency nor a claim of
global minimality.

`check_composition.py` imports no source producer or optimizer. It checks
the pinned original bytes, every strict source edit, both directions of
the private-wire identities, the actual Pell offsets, every member of
both pools, both completed-square identities, every final affine map,
the full 36-atom square frame and all 17 request triples, every collected
quartic coefficient, all exact metrics, and variable liveness. Seven
targeted corruptions are rejected, with and without Python assertions.
Those finite audits bind the literal equation to this ordinary proof;
they do not replace its unbounded estimates or recompile the full
transitive Lean/Rocq calibration.

## Source attribution

All source paths in this list are under the pinned collection named above.

- `157-linear-crt/proofs/MAIN_PROOF.md`: factorial-free growth F=t^t,
  linear binomial CRT radius, parity bootstrap, affine beta spacing,
  CRT completeness, and calibrated source equivalence.
- `158-pooled-powers/proofs/POOLED_POWERS.md`: the two-row fixed-base
  pool and the existing square-frame bound.
- `158-pooled-powers/proofs/STRICT_HORIZON_AND_BETA.md`, Sections 1-4:
  strict cofinal range mechanism. Its factorial-dependent linear-beta
  choice is deliberately not part of this composition.
- `158-pooled-powers/code/build_basis.py`: original private-wire
  polynomial identity, transferred here by exact semantic-name matching.
- `158-pooled-powers/code/shear_pell.py`: integral Pell-difference
  coordinates and the exact orientation-row operation.

The contribution is a proved and fully emitted combination of these
previously separate branches, followed by exact projection. It is not a
claim that the individual inherited lemmas are newly discovered, nor a
claim of literature-wide priority for the combination.
