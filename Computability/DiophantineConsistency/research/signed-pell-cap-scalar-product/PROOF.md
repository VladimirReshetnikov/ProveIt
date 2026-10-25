# Eight nonnegative factors restore ten scalar guards

This is an ordinary proposal at the CURRENT sealed signed-cap source,
manifest53244a0a26bcfe2411c28adf2c6d74f7a4618c0c42c7904e8818be4e3f9a6ef5.
It generates no source, program, projection or census and changes no frozen
packet. It retains F, the original positive common helper and d graphs,
the direct cap lower graph and the cap term in the joint pool. It does not
compose the separate unoriented/refined source or helper/F deletions.

Omit exactly original scalar guards1 and6..14, on x=v1 and encoded
coordinates v16..24. Append fresh private quadratic product gates outside
the semantic frame for

    P = product_(j=16..23)(vj+1),

and one fresh Legendre graph P-1=a^2+b^2+c(c+1). The eight factors are
intentional: x and v24 are recovered separately below. Every original body
coordinate and row stays fixed. The proposed equivalence is pointwise on
that entire body and on all retained guard witnesses, with fresh graph
witnesses and new private product gates. No projected saving is inferred.

## 1. Negative-index power requests with a signed scale

The following lemma is uniform in signed A, for future separately bound
compositions. The current application will first recover A>=2 from its
unchanged positive-cap joint row.

Let a=|A|>=2 and let Xk(A),Yk(A) be the signed-base Pell recurrence,
with X_(-k)=Xk and Y_(-k)=-Yk. Suppose a square frame bounds

    |k|<W, 2<=n<W, |m|<W, n^2+1<a, a>W^W,

and the index module supplies y=Yk(A), x=+/-Xk(A). Keep the actual
linear request x+(n-A)y=m+Tz, T=2An-n^2-1. Its quotient is signed.
For j>=0 define H_j=Xj+(n-A)Yj and J_j=Xj-(n-A)Yj. Polynomial
identities, valid for all integer A, give

    H_j J_j=1+T Yj^2,
    H_(j+1)=n H_j+T Yj, H_0=1.

Hence H_j=n^j modulo T. Also |T|>W^W: for A>0 it is at least
4a-n^2-1>3a, and for A<0 its absolute value is at least4a+n^2+1.
The frame bounds give, for1<=j<W,

    |m*n^j-1|<=(W-1)^W+1<W^W,
    |m+n^j|<W^W, |m-n^j|<W^W.

If k=-j<0, then y=-Yj. The x=+Xj branch has left side J_j and implies
m*n^j=1 modulo T. The bound makes this an integer equality, impossible
because n^j>=2 cannot divide1. The x=-Xj branch has left side -H_j,
so it forces m=-n^j exactly. Thus every negative-index solution has a
strictly negative output of that form.

In particular, if n=q+1 with q>=3 and m=1 modulo q, k<0 is impossible:
the remaining output would be -(q+1)^j=-1 modulo q, so q would divide2.
Therefore such a request forces k>=0. At k=0 the norm gives y=0,
x=+/-1. The small residue bound then gives m=+/-1; the residue1 modulo
q selects m=1. Zero requested index is possible and is not discarded.

For a request at any n>=2 with m>=2, the same negative-index argument
excludes k<0, and k=0 is excluded by m=+/-1. Thus that request forces
k>=1. For a positive k, the familiar two branches give m=n^k or
m*n^k=-1; the latter is impossible by the same bounds. Its canonical
abscissa is selected, even for signed A.

These statements use canonical signed-base Xk,Yk, not an assumed positive
ordinate for a negative index. They fail in the stated residue argument
if q=2: -1 and1 then coincide modulo q. The t bootstrap below supplies
q>=3 before the lemma is used to recover any omitted sign.

## 2. Current cap recovery before the missing scalar signs

Use current compact source indices throughout. Retain the guards for
t0=v0, F=v3, r=v7, s=v8, r0=v11, o=v185, Zminus1=v247,
d=v252 and the comparison ordinate Vc=v251, together with every other
old predicate except the ten listed. The strict helper graph is Vc-1>=0.

Rows3 and167 give B=v5=r+s+1>=1 and q=v179=B+o+1>=2. Also
t=v0+16>=16. The unchanged row334 is

    W=2(2+sum37 semantic atoms^2),

which is valid without signs on x or v16..24. Thus W is even, W>=516,
all fifteen original requested indices satisfy |ki|<W, and every base
and output has its absolute frame bound. The retained frame ordinate and
rows202..204 give |A|>=(W+1)^W and |A-1|>4W^3 before any power.

The full cap anchor, its lower graph217, square graph218, and whole joint
row219 still have precisely their accepted hypotheses: C>=W, strict Vc,
d>=0, all fifteen primary norms and the common C^2 divisor. The accepted
joint index theorem permits arbitrary signed requested ki, including0.
It proves A>=2 and yi=Y_(ki)(A), xi=+/-X_(ki)(A). In particular the
t pair257/258 has positive requested index t. No positive encoded-index,
x, y or K ledger is supplied or invoked here.

This is the crucial replacement for an early invocation of the old whole
source theorem: that theorem expects the ten omitted scalar graphs.
It will be applied only after they are reconstructed.

## 3. t/F, y and x supply the needed q-power denominators

Actual call4, row254, has base q>=2, exponent t and output L=v181 on
pair257/258. Positive-index orientation proves L=q^t and orients that
same pair. Call0, row227, now gives V0=v6=(F^2+1)^t even at the possible
base-one endpoint. Its square base uses row0, v4=F^2. From rows1..3,

    F*B=V0+s.

Consequently F>=1. Since t>=16, V0>F^2, hence B>F and q>=3.
The stronger inequality needed later also holds. Put n0=F^2+1. Then
n0>F and n0^(t-1)>F, so

    F*B>=n0^t > F*n0, hence B>F^2+1.          (1)

No factorial, binomial or K power meaning is used in these inequalities.

The unchanged derived-pair recurrence from the oriented t pair gives
the canonical t+1 pair. Actual call6 at row267 therefore proves
Qt1=v189=q^(t+1). Both L and Qt1 are divisible by q.

Row7 and the retained r0 guard give y=v2=F+v11+1>=2. Thus its target
y+1 is positive independently of x or the encoded scalars. Call11 at
row297 has base q and output Qy=v211, so the canonical positive-index
argument gives Qy=q^(y+1), divisible by q.

The x request is NOT a successor-base request. Actual call14 at row312
has base q, target kx=x+1 and output Qx=v223. Its retained scalar
anchors are v225>=0 and v226>=0, original guards23 and24. Row191 gives

    Qx=q*v225+v226+2>=2.                      (2)

The generic index module has already supplied its canonical SIGNED
ordinate at kx, even if kx is negative or zero. The m>=2 case of
section1 rules out both possibilities. Hence x+1>=1, so x>=0, and
the same request gives Qx=q^(x+1), divisible by q. No product factor
for x is needed.

All four denominator powers L,Qt1,Qy,Qx have now been proved positive
and divisible by q. The register N=v26 is still an arbitrary integer
in this proof. No base-B K request or q=N^K meaning was used.

## 4. All eleven successor residues are literal consequences

The remainder reparameterizations do not, by themselves, say that each
successor output is1 modulo q: a quotient-product term also occurs.
The preceding denominator divisibility supplies that missing premise.
The following are exact lowered identities from unchanged rows. All
quotients on the right may be signed. N=v26 has no assumed power meaning.

| Call | Output | Digit row | Exact output identity |
| ---: | ---: | ---: | --- |
|3|v180|165|1+q*v183+L*(B+q*v182)|
|5|v188|170|1+q*v191+N*Qt1*v190|
|7|v195|173|1+q*v197+N*Qt1*v196|
|8|v200|176|1+q*v202+N*Qt1*v201|
|9|v205|179|1+q*v207+N*Qt1*v206|
|10|v210|183|1+q*v213+N*Qy*v212|
|12|v217|186|1+q*v219+N*Qy*v218|
|13|v222|190|1+q*v225+N*Qx*v224|
|15|v229|193|1+q*v231+N*Qx*v230|
|16|v234|197|1+q*v236+N*L*v235|
|17|v240|200|1+q*v242+N*Qt1*v241|

The multiplication gates in rows163..200 bind all displayed products.
Each identity therefore gives an actual integer representation m=1+q*u
and residue1 modulo q. This uses neither a sign of a quotient nor N/K
semantics, nor any omitted scalar. It is a divisibility inference in the
ordinary proof, not an extra variable or source substitution.

The nine encoded coordinates v16..24 have successor requests respectively
at calls5,7,8,9,10,12,13,15,16, with targets vj+1. Their actual primary
norms and pooled indices, unsquared congruences, complete modulus bounds
and these residues meet section1. Hence

    vj+1>=0 for every j=16..24.                (3)

The other successor calls3 and17 do not supply an x target. This proof
does not misidentify call14 as a successor-base request.

## 5. The encoded reciprocal index excludes its zero factor

Equation(3) gives v24>=-1. If v24=-1, rows11 and12 say

    v28=B*v27, F^2+v24+2=v28,
    hence B*v27=F^2+1.

By (1), the right side is strictly between0 and B. No integer v27 can
satisfy that equality. Thus v24>=0. This is a raw divisibility argument,
not an invocation of the full reciprocal-index/CRT semantics or a natural
sign for its quotient. No product factor for v24 is needed.

## 6. One product predicate restores the other eight signs

Use only v16+1,...,v23+1 in the product. All eight factors are nonnegative
by (3). Introduce fresh private quadratic gates, for example

    p2=(v16+1)(v17+1),
    p3=p2(v18+1), ..., p8=p7(v23+1),

and a fresh triple satisfying

    p8-1=a^2+b^2+c(c+1).

The graph gives p8>=1 and the monic gates give the exact product P.
If any nonnegative factor were0 the product would vanish. Hence each
factor is at least1, and v16..23 are all nonnegative. Along with x>=0
and v24>=0, this recovers every one of the ten omitted scalar signs.

The new product gates and graph witnesses are private and excluded from
W and all power interfaces. They do not create any additional requested
Pell index. A future literal adapter must prove their freshness and full
occurrence maps; this ordinary note emits no coordinates or new source.

The ten exact old graphs in the current guarded source are:

| Original guard | Coordinate | Row | Private triple |
| ---: | ---: | ---: | --- |
|1|1|336|405,406,407|
|6|16|341|420,421,422|
|7|17|342|423,424,425|
|8|18|343|426,427,428|
|9|19|344|429,430,431|
|10|20|345|432,433,434|
|11|21|346|435,436,437|
|12|22|347|438,439,440|
|13|23|348|441,442,443|
|14|24|349|444,445,446|

Every listed auxiliary occurs only in its own graph, in the complete
507-coordinate guarded equation. The thirty old graph witnesses can
therefore be independently discarded or chosen freshly without an
escaping body use. All other predicates, including the anchors used in
sections2..3, remain.

## 7. Both pointwise-body witness directions

For a zero under the new policy, sections2..6 prove the ten old signs
without invoking their old positive-seed/source proof. Choose a fresh
Legendre triple for each recovered nonnegative coordinate and restore
the ten old rows. The complete original402-coordinate body and EVERY
retained old witness stay fixed. This is now a zero of the exact sealed
current signed-cap source. Its whole positive-index, K/factorial/binomial/
range/native calibration may be used at this point, and not earlier.

Conversely every old zero has v16..23>=0. Compute the new private
product chain from those unchanged values, so P>=1, and choose its graph
triple. Forget the ten old private scalar triples. All other original
body and witness coordinates stay fixed. These constructions preserve
full canonical completeness and establish existential equivalence at
the fixed body. They are not a bijection of graph triples.

The signed-A negative-index lemma in section1 can be used in a future
combined policy after its own canonical signed-index and partial front
premises have been rebound. The present theorem does NOT drop F, change
helper signs, remove the cap lower graph or remove the joint cap term.
Those compositions need a separate proof and literal source binding.
No programs, source generation, optimizer or Lean are used here, and no
new variable, operation, degree or height frontier is claimed.
