# Paired sign guards and a square-anchored factorial radius

## Results and theorem boundary

The final polynomial is P489=sum(R_j^2), with 489 unrestricted integer
coordinates and the 308 explicitly listed quadratic residuals in
squared_paired/equation.json. Its fully expanded coefficient list has
6905 nonzero monomials, exact degree 4, and coefficient height 11302118.
The simpler P493 sibling has 493 integer coordinates, 310 residuals,
7174 monomials and height 10945213. Neither equation has hidden natural
variables or variable exponents. All abbreviations in this proof refer
to wires of the supplied finite polynomial, not additional unknowns.

Under exactly the inherited ordinary C222/ZFC and signed-Pell calibration
of the frozen direct source, existence of either zero is equivalent to a
finite C222 refutation. Thus its no-zero sentence is equivalent in ZFC
to Con(ZFC), at the same ordinary-proof level as that source. This is not
a new kernel-checked object-language ZFC derivation. No consistency claim,
global minimality, or historical priority claim is made.

The contributions of this packet are (i) twelve post-power paired guards
with measured projected endpoints, and (ii) reuse of an existing square as
a presemantic sign anchor for the factorial radius, endpoint and budget.
All reduction steps are elementary integer arithmetic and finite algebra
formalizable in ZFC.

### Late upstream attribution

The general paired-product principle is already present in the upstream
six-anchored-product-guard construction accepted at commit
59ee8f21244635b42f706a74c4e9631226dd1f7c, dated 24 October 2026, 22:32 UTC.
Its complete review is preserved in inherited_proofs/late, authenticated by
SOURCE.json, and available at
https://github.com/VladimirReshetnikov/ProveIt/blob/59ee8f21244635b42f706a74c4e9631226dd1f7c/Computability/DiophantineConsistency/reviews/shared-remainder-product-guards-root-peer.md

That packet keeps eight direct scalar anchor graphs and restores twelve
removed signs via six product graphs before invoking its parent power
proof. It has 56 predicates, 1436 unrestricted-integer coordinates and
1242 residuals in its full UNPROJECTED system, saving 18 coordinates and
six rows. It explicitly does not report projected quartic counts.

The present application instead uses twelve pairs whose nonnegative sums
are justified after signed-power recovery, on the later factorial-carrier
source. Its actual projections are517->493 and, after the additional F²
radius/endpoint/budget change,489. The upstream result and these endpoints
are not interchangeable measurements. The product-sign lemma and its
three-square implementation are credited as overlapping upstream work;
no novelty or historical-priority claim is made for that principle.

## 1. A paired nonnegativity guard

Let r,s be integers with r+s>=0. Then

    r>=0 and s>=0
        iff there are a,b,c in Z with rs=a^2+b^2+c(c+1).       (1)

The right side gives rs>=0 because c(c+1)>=0 for every integer c.
If one of r,s is negative, nonnegative product makes the other nonpositive,
contradicting their nonnegative sum. Conversely every natural n has the
form a^2+b^2+c(c+1). To see this, Legendre's three-square theorem represents
4n+1 as u^2+v^2+w^2. Exactly one coordinate is odd, after permutation
w=2c+1, u=2a, v=2b. Divide by four.

The sum hypothesis is indispensable: r=s=-1 has product 1 but neither
coordinate is nonnegative. It is established below before using (1).
Equation (1) is quadratic, so squaring it in the final sum preserves degree4.

## 2. The twelve pairs and their noncircular sign recovery

In the frozen mixed source the twelve pairs are:

    choose0.remainder, choose0.rslack;
    choose1.remainder, choose1.rslack;
    rangei.remainder, rangei.slack  (0<=i<=9).

Every pair has an existing row r+s=q^k-1, with k one of the positive
indices t,t+1,y+1,x+1. The exact row and power-output variable for every
pair are listed in pair_certificate.json. Replace the 24 individual
three-witness guards by 12 instances of (1). No factorial ceiling guard,
output-digit slack, encoded representative guard or Pell index guard is
removed in this step.

Here is the soundness order, before any digit is interpreted.
The retained factorial remainder and slack f_r,f_s give

    D=f_r+f_s+1>=1.

The retained choose0 output slack o_0 gives

    q=D+o_0+1>=2.

The retained ordinary sign guards, the square-budget identity, and the
presemantic lower-bound certificate establish positivity of every seed
index, of its Y ordinate, and of the shared auxiliary ordinate. Hence
the auxiliary norm gives |U|>=2. The inherited signed indexed-Pell
criterion is now applicable without using any removed digit sign.

The request q^t, at a base at least2, orients the t-index pair. It also
orients V=(rho+1)^t, whose base is positive, even if initially equal to1.
The factorial ceiling rows give DF=V+f_s, so V>=1 and D>=1 force F>=1.
In particular V>=2. The retained B>=0 guard and

    C+F^2+1=B*i_q,  C>=1,

force B>0. The K-index request B^K either gives its genuine positive N,
or the sole inverse case B=1,N=-1. In either case N+V+1>=2; its second
K-index request orients the pair and excludes the inverse case. Thus
N=B^K>0 and q=N(N+V+1)^K has its intended value. Every other seed has a
request with base q or q+1, both at least2. All nineteen powers are
therefore recovered before the twelve paired signs are used.

Now q^k-1>=0 for all twelve pair rows. Equation(1) gives every original
digit remainder and slack its required nonnegative sign. The original
ordered factorial, carry-free digit, amplified CRT and Horn-flow argument
then applies. Conversely any old semantic certificate has nonnegative
r,s, so it extends with three witnesses for each rs. Thus this step
preserves existence in both directions. It does not assert that the
three new guard coordinates equal any old guard coordinates.

## 3. Reusing an existing square removes the factorial sign guard

The stronger sibling changes exactly three quadratic rows of the original
mixed source, leaving its full fixed formula-constructor circuit unchanged:

    rho=F*t^2       becomes rho=F^2*t^2;
    y=F+r0+1        becomes y=F^2+r0+1;
    R=2+t+x+y+F     becomes R=2+t+x+y+F^2.                    (2)

The wire F^2 already exists for the reciprocal product binomial, so no
new square variable or equation is introduced. In the frozen coordinate
numbering it is variable27, named mul.36. Rows1,8,11 are changed, and
the independent guard on variable3, fact0.output, is removed. Every
other original guard is retained except the twelve paired replacements.
The old presemantic certificate is not silently reused: a fresh ordered
certificate derives the seed lower bounds from the literal modified rows.

Before knowing anything about F's sign, F^2>=0. Since t=t0+16>=16,
x,r0>=0, (2) gives rho>=0, y>=1, R>=19 and K=2R>0.
The indices rho+t,F^2+t,t,t+1,x+1,y+1 are positive. The encoded
representatives and the derived label-sum index are positive from their
retained guards and nonnegative constructor polynomials. This establishes
all seed hypotheses without assuming F>=0. The proof in Section2 now
recovers V and forces F>=1 from the unchanged factorial ceilings.
Only at this stage is F used as a nonnegative local-source parameter.

Once F>=1, the modified radius satisfies rho=F^2*t^2>=F*t^2. The wider
radius factorial lemma in Section4 applies. The local source polynomial
and derived label sum have their original majorant in
R_old=2+t+x+y+F. Since R>=R_old, their same certified exponent E remains
valid using R. When F=t!, the floor t>=16 gives F>=16!>2^44, hence
R>=F and R^E<2^R<2^K as in the inherited proof. Also
3*ell*(t+1)<=2F<=K, so the separate derived-label carry budget remains
valid. Enlarging the radius does not enlarge the number of variables.

## 4. The wider self-bounding factorial lemma

Let t,F,rho be positive integers, rho>=F*t^2, and put

    V=(rho+1)^t,  D=binom(rho+t,t).

Then nonnegative f_r,f_s satisfying

    D=f_r+f_s+1,  DF=V+f_s                                (3)

exist if and only if F=t!. This remains a statement about the interpreted
digit output D; the interpretation bootstrap is given below.

Write L=t!. The exact ratio identity and the elementary product inequality
for numbers in[0,1] give

    V/D = L product_(i=1)^t (1-(i-1)/(rho+i)),
    L(1-1/(2F)) < V/D <= L.                               (4)

Indeed the sum of the subtracted fractions is at most
 t(t-1)/(2rho)<1/(2F). Rows(3) are precisely F-1<V/D<=F.
Since L is an integer and V/D<=L, F<=L. If F<L, then L>=F+1 and
L(2F-1)>=2F^2, so L-L/(2F)>=F. The strict lower bound in(4)
contradicts V/D<=F. Thus F=L.
Conversely, for F=L, (4) gives L-1<V/D<=L. Set
f_s=DL-V and f_r=D-f_s-1; both are natural and satisfy(3).
This proof includes t=1 and does not require equality rho=F*t^2.

In the actual polynomial the powers are recovered first, while D is still
a proposed binomial output. Their common radix satisfies
q=N(N+V+1)^K>V^2, since N>=1 and K>=2. After the raw ceilings establish
F>=1, rho>=t. Thus every digit up to t of (q+1)^(rho+t) has coefficient
at most binom(rho+t,t)<=V<q. The first exact digit is valid, and (3)
forces F=t!. For the second exact binomial, F^2+t<=(rho+1)^2, so every
needed coefficient is at most V^2<q. Only now is B identified with
binom(F^2+t,t), giving B>=2 and N>=2^K. The unchanged range and
separate derived-label bounds then validate every remaining digit.
There is no circular assumption that B is already its intended binomial.

## 5. Constructive completeness of the square-anchored sibling

This is a reconstruction from a finite proof, not same-tuple equivalence
to the older radius. Given a finite C222 refutation, choose t>=16 beyond
the padded proof-tree length, all finitely many local parameters and all
local label sums, before defining F=t!. Form the positive Horn-flow
accumulator states from weights1+jF, exactly as in the inherited proof.
Choose y, a positive multiple of t!, large enough for every state and
for F^2+1. Then r0=y-F^2-1>=0. The beta CRT construction supplies x>=0
and the endpoint quotient witnesses. All local bounds are valid.

Now set rho=F^2*t^2 and R=2+t+x+y+F^2, K=2R. Construct the reciprocal
moduli, B, N=B^K and the nine independently chosen CRT representatives
at precision2K. Their aggregate bound has its usual natural slack. Set
V=(rho+1)^t and q=N(N+V+1)^K. Section4 provides the factorial ceiling
witnesses, and the unchanged digit bounds provide every exact and range
digit witness. The original simultaneous Pell completeness construction
supplies the shared frame and all index witnesses. Add product-guard
witnesses by(1). Every row of the modified mixed source vanishes.

The signed Horn factorization is an exact polynomial identity. Every
subsequent deleted coordinate has an explicit integral monic restoration
in projection_certificate.json; restoring them in reverse order is the
inverse to projection. Therefore existence of a semantic certificate is
equivalent to existence of a zero of the final489-variable polynomial.

## 6. Exact artifacts and reproducibility

source/ contains the frozen mixed polynomial and original domain
certificate. inherited_proofs/ preserves the ordinary source, arithmetic,
Pell, direct encoding and attribution files used above; nothing in the
build reads outside this packet. vendor/ contains the reviewed finite
polynomial utilities, with their original licenses preserved.

From this directory run:

    python build_pairguards.py source paired
    python build_pairguards.py source squared_paired --squared-radius

The same commands under Python -O use no disabled assertions. The emitted
expanded_polynomial.json is the literal coefficient list, not a gate-count
estimate. The exact degree is4 because the full expansion has nonzero
quartic terms. The paired493 and square-anchored489 changes trade some
coefficient height/support against variable count; no global dominance
claim over all prior equations is intended.

Finite small-value checks supplement the universal proofs. They do not
test consistency and are not a proof-assistant certificate. In particular,
no actual zero of a consistency polynomial is fabricated for a regression.
