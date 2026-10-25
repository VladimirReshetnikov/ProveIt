# Recovering two front signs from one product certificate

This is a new ordinary arithmetic reduction on the common-remainder source
at ProveIt commit 3ecd6a6cf53d47519228328567f45fb7ee9781d9. The literal
parent is the `direct/data/source.json` in the incoming archive
`ConZFC_Common_Remainders_Radix47_2026-10-25.zip`. The parent unbounded proof
is `direct/proofs/NORMALIZED_REMAINDERS_PROOF.md`; its complete signed Pell
and factorial/CRT dependencies remain inherited. All coordinates are
unrestricted integers. This proof is formalizable in ZFC and composes with
the same C222/ZF/ZFC-refutation calibration. It is not a consistency proof
or a new end-to-end proof-assistant certificate.

## 1. Literal change

Write r,s for `fact0.remainder`, `fact0.slack`; B=`choose0.output`,
F=`fact0.output`, V=`pow0.output`, q=`pow2.output`. Define

    G(a,b,c) = a²+b²+c(c+1).

This is nonnegative on Z³ and represents every nonnegative integer. The
proof of surjectivity follows by applying the three-square theorem to
4n+1 and putting its unique odd square in the third position.

Delete the two independent initial guards r=G(...), s=G(...). Replace them
by one quadratic row

    (r+1)(s+1) = 1+G(a,b,c),                           (FG)

or, expanded, r*s+r+s-a²-b²-c²-c=0. No product wire is needed.

Also compose the independently supplied odd-square radix construction:
delete q=B+o+1 and o=G(...), and insert

    q=(2z+1)².                                        (OS)

Retain the entire common-remainder construction, all other source rows,
all signed power requests and both other guards (the squared Pell cap
and the common remainder norm). The original front therefore uses three
ternary guard triples; the new front uses one triple and one square-root
coordinate. The final variable saving must be measured after projection.

## 2. Signed-base power lemma

The inherited signed frame and anchor/orientation argument does not use
any of the deleted front signs. It uses squares of all proposed power
atoms and gives an integer W>=258 with

    |A|>W^W,
    |n|, |k|, |m| < W,

for each requested base n, signed index k and output m. The principal
pair is the canonical pair at signed index k:

    X_k(A),Y_k(A),  X_(-k)=X_k, Y_(-k)=-Y_k.

Its power output row says

    m = X_k(A)+(n-A)Y_k(A) modulo T,
    T=2An-n²-1.

**Lemma.** If 2<=|n|<W, that row forces k>=0 and m=n^k. It is valid for
negative as well as positive bases.

Indeed, |T|>=2|A||n|-n²-1>W^W+W, and T=-1 mod n gives gcd(n,T)=1.
Substitution s=n-A in the Pell identity gives s²=A²-1 modulo T. For
k>=0 it follows that m=n^k modulo T. Since

    |m-n^k| <= |m|+|n|^k < W+W^W < |T|,

this congruence is equality. For k=-j<0, the index -j pair is the inverse
Pell unit; multiplying the positive-index expression gives

    m*n^j = 1 modulo T.

Here j>=1, j<=W-1 and |m|<=W-1, so

    |m*n^j-1| <= (W-1)^W+1 < W^W+1 < |T|.

It would follow that m*n^j=1, impossible over Z because |n|^j>=2.
No positivity premise for m or n is present in this argument. For n=1
and a known nonnegative k, the same congruence yields m=1. This is the
base-one case needed for the initially possible F=0.

## 3. The two possible sign branches

The t-index is known positive: t>=16. Its request at n=F²+1>=1 therefore
first gives

    V=(F²+1)^t >=1.

The literal front equalities, untouched by (FG), are

    r+s=B-1,                 BF=V+s.                  (CE)

Because the right side of (FG) is strictly positive, r+1 and s+1 are
nonzero and have the same sign. Thus exactly one of the following holds:

    (I) r,s>=0, or
    (II) r,s<=-2.

In case I, (CE) gives B>=1 and F>=1. Since V>F², one has B>F and hence
B>=2 and V<=BF<B².

In case II put B=-b. Then b>=3, since B=r+s+1<=-3. F=0 is impossible:
BF=V+s and V=1 would give s=-1. If F>=1, the two equations (CE) imply

    r=(1-F)B+V-1>0,

because B<0, V=(F²+1)^t>1 and 1-F<=0. This contradicts r<=-2.
Consequently F=-f for an integer f>=1. The inequalities s<=-2 and r<=-2
are now exactly the useful bounds

    bf+2 <= V <= (f+1)b-1 < (f+1)b.                   (NB)

Since t>=16 and f>=1,

    V=(f²+1)^t>(f+1)².

For example (f²+1)² >= (f+1)² for every f>=1, with equality only at f=1;
the extra positive powers give strictness. Comparing with (NB) yields
b>f+1, and therefore V<b².

Thus in BOTH branches, putting f=|F|, b=|B|, we already know

    f>=1, b>=2, V=(f²+1)^t, V<b².                    (UB)

This deduction uses no factorial, binomial or radix meaning.

## 4. Recovering the radix and the endpoint bound

(OS) gives q>=1 before q's power meaning is used. Hence q+1>=2. Every
actual CRT representative a_i is the exponent of a retained request at
base q+1; the signed-base lemma makes a_i>=0 and authenticates its power.
Therefore the actual sum

    H0=1+sum_(nine representatives) a_i

is >=1. No sign of the stored shifted coordinates is asserted.

Next apply the signed-base lemma to the retained request N=B^x. Its base
has |B|=b>=2 by (UB); it forces x>=0. The cofinal beta value is the
unchanged polynomial

    y=V(V-1)>f+2.

In the semantic coordinates of `STRICT_BUDGET_PROOF.md`, the untouched
endpoints are

    x=F+1+(y+1)u0,
    x=1+[1+(t+1)y]ut.                                (EP)

The second equality excludes x=0, because its positive bracket exceeds
one. If x=1, the first gives F+(y+1)u0=0, impossible since
0<|F|<y+1. Thus x>=2. The second equality then forces ut>=1, giving

    x>=2+(t+1)y>=8.                                  (XB)

Some delivered centered coordinate lists translate y to y-1 and t0 to
t0-16. Statements (EP) use the unshifted semantic y and t throughout.

Apply the signed-base lemma to the retained request q=(B H0)^x. Since
|B H0|>=2, it gives that exact integer power. Its output is positive by
(OS). In case B<0, x must therefore be even. In both branches,

    N=b^x>0,
    q=b^x H0^x >= b^x >=2^8,
    N divides q.                                    (RQ)

All remaining denominator requests are now exact positive q-powers.
In particular M=q^x, D0=q^t, D1=q^(t+1), Dy=q^(y+1) are positive,
and (XB) gives the divisibilities required by the common-remainder norm.
None of these deductions has yet assumed F=t!.

## 5. One digit excludes the negative branch

For m>=1,t>=1,0<=j<=t the elementary bound

    binom(m+t,j) <= (m+1)^t

is proved in the inherited common-remainder proof by Pascal induction,
with the edge j=t handled by the product formula. Apply it with m=F².
Every binomial coefficient through position t of
(q+1)^(F²+t) is at most V<b². Therefore its true low remainder is

    r0 = sum_(j=0)^(t-1) binom(F²+t,j) q^j,
    0<=r0 < V*D0/(q-1) < D0/32.                      (LR)

The last strict inequality follows from (RQ), (XB), b>=2 and
V<b²:

    V/(q-1)<b²/(q-1)<2/b^(x-2)<=1/32.

The single common norm in the parent says

    M²=1+4 sum_i R_i²+G(...).

Together with D_i v_i=M and the normalized digit equations, it gives an
integral reconstructed remainder r_i=R_i/v_i with |r_i|<D_i/2. The
factorial r_i is congruent to r0 modulo D0. Equation (LR) then proves
r_i=r0. This is exactly the parent's reconstruction argument and needs
no sign of B.

The normalized exact-binomial row can now be divided by D0. It yields

    B = C mod q,       C=binom(F²+t,t)>0.             (FD)

The relevant binomial digits are carry-free since C<=V<q. More strongly,

    |B-C| <= b+C <= b+V < b+b² < q,                   (SD)

because q>=b^x and x>=8. The congruence (FD) and (SD) force B=C>0.
This rules out case II entirely. Thus r,s>=0 and F>=1. Also q>B, so
the deleted exact-output slack o=q-B-1 is nonnegative.

We can now restore all three deleted ternary guards using surjectivity of
G. The old exact factorial identity holds, so the inherited fixed-point
proof gives F=t!. The parent's remaining range-digit, prime-power CRT,
Horn-flow, C222 and syntactic-refutation arguments proceed unchanged.

This is an acyclic proof: the early bound V<b² came from (FG) and (CE),
not from factoriality; the single factorial digit resolves the sign branch;
only afterward is the factorial fixed point used.

## 6. Completeness

Start with a finite C222 refutation. Use the inherited cofinal witness
construction and the odd-square radix completeness theorem from
`ConZFC_Centered_Residues_2026-10-25/arithmetic/ODD_SQUARE_AND_WEIGHTED_PROOF.md`.
Briefly, all beta CRT periods are odd, so choose even x; B is odd; adjust
a third independent CRT representative's parity to make H0 odd, without
changing the even dominant-anchor parity. Then q=(BH0)^x is the square
of an odd integer and (OS) has an integer z. All original r,s are
nonnegative. The quantity (r+1)(s+1)-1=rs+r+s is nonnegative and so has a
G representation, satisfying (FG). Keep the normalized digit witnesses
and common norm witnesses from the common-remainder construction.
Every new raw row is satisfied. No r>0 or s>0 requirement is needed.

The raw modification therefore preserves the EXISTENCE of integer zeros.
It is not claimed to be a bijection on all old private witnesses. Exact
integer monic projections and integral translations are bijections after
restoration and are checked separately from this unbounded proof.

## 7. Scope

The new idea is (FG) together with a signed-base bootstrap that lets the
factorial digit itself orient B and thereby both old front signs. The
odd-square radix, canonical signed Pell frame, common-remainder norm,
underlying C222 source, and final projection machinery are credited
predecessors. The proof requires the actual retained power/endpoint
interface; (FG) alone does not imply r,s>=0 on arbitrary integer tuples.
