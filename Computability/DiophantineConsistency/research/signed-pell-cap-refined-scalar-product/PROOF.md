# Eight-factor scalar compression on the refined signed-cap source

The eight-factor policy composes soundly with the CLOSED refined source.
This is a new ordinary theorem with an exact labelled interface, rather
than an invocation of the old compression theorem's positive-A stage.
It preserves every refined body coordinate and every retained old witness
in both existential directions. Helper reflection is used temporarily
inside the proof and does not change the body in the resulting witness map.
No new program, compiler, source equation, projection or Lean is executed
or emitted, and no projected numerical frontier is claimed.

The parent is research/signed-pell-cap-refined-source, manifest
73a5b427338c33cb5ff0365fc64a994b796b16837d9bdc2a987d63d5eef8ed51.
Its complete source/guarded/domain/transform bytes and the ordinary
ingredients are pinned in SOURCE_PINS.json. All v-indices and row numbers
below refer to that ACTUAL refined source. The separate old-policy note's
two wrong call-row addresses are corrected by the pinned outside erratum:
actual refined call11 is row291 and call14 is row306.

## 1. Exact labelled policy and boundary

Keep the entire refined body, every body row, its primary-only pooled row,
its squared-cap predicate, and its comparison-base-lower predicate.
Remove precisely original guard indices1 and6..14. The actual refined
graphs and their complete private triples are:

| Original guard | Coordinate | Refined row | Private triple |
|---:|---:|---:|---|
|1|1|335|402,403,404|
|6|16|339|414,415,416|
|7|17|340|417,418,419|
|8|18|341|420,421,422|
|9|19|342|423,424,425|
|10|20|343|426,427,428|
|11|21|344|429,430,431|
|12|22|345|432,433,434|
|13|23|346|435,436,437|
|14|24|347|438,439,440|

Each complete row is v-a^2-b^2-c(c+1). Each listed auxiliary occurs only
in that graph in the WHOLE refined guarded source; the exact occurrences
are recorded in INTERFACE.json. No original body coordinate is removed.
Every other predicate and its old witnesses remain fixed.

Introduce disjoint fresh integer symbols p2,...,p8,aP,bP,cP and rows

    p2-(v16+1)(v17+1)=0,
    pj-p_(j-1)(v_(15+j)+1)=0, j=3,...,8,
    p8-1-aP^2-bP^2-cP(cP+1)=0.                  (P)

Here j=3 uses v18 and j=8 uses v23. All new rows are quadratic.
All fresh symbols are private, outside the parent frame, power ports,
Pell/index/comparison rows and semantic front. There is no sign graph
on a partial product. This labelled system specifies the policy exactly;
it is not a newly generated numeric-coordinate source artifact.

## 2. Normalize the helper only for the argument

Let A=v246, W=v245, C=v387, h=v395. The refined helper graph is row366,
v255-4>=0, with triple495..497. Rows205/206/207/322 encode

    H=A*V, U^2+V^2-H^2=1,
    v255=4*V*(d+1), V=C^2*(e+1),

with V=v251,d=v252,H=v254,e=v375,U=v250. The accepted four-port
involution V->-V,d->-d-2,H->-H,e->-e-2 negates rows205/322 and fixes
every other refined body row, every retained graph and the helper graph.
It also fixes all product inputs and every row(P), with fresh symbols
unchanged. This follows from the exact parent occurrence ledger and
the absence of those four ports from the newly added rows.

The helper graph and row207 give V(d+1)>0. Normalize by the identity
when V>0 and by the involution when V<0. The normalized assignment has
V>=1,d>=0. The coordinates whose signs we will recover are all fixed
by this involution. Thus conclusions about their signs hold on the
ORIGINAL input assignment too. No positive-A or cap-sign conclusion
is inferred by normalization.

## 3. Signed cap recovery before F or the omitted scalars

Retained direct graphs give v0,v7,v8,v185,v247>=0. Front rows3/167 give

    t=v0+16>=16, B=v5=v7+v8+1>=1,
    q=v179=B+v185+1>=2.

Row0 gives v4=F^2 for the still signed F=v3. The complete unchanged
frame row333 is W=2(2+sum37 actual semantic atoms^2). It gives W>=516,
the absolute bound |ki|<W for every original target, and absolute bounds
on every actual base and output. The scale norm rows202..204, with
v247+1>=1, gives a=|A|>=(W+1)^W and |A-1|>4W^3. None of the ten
deleted signs, F>=0, A>0, C>0, y>0 or K>0 was used.

The refined squared-cap row217 gives C^2>=1+sum15 Yi^2. At |C|=1,
all Yi vanish and the primary-only pool row218 says

    sum15 ki^2=(A-1)h.

Its left side is strictly positive because the t target is nonzero,
and is less than W^3<|A-1| by the absolute frame. This is impossible.
Hence |C|>1. Pell classification gives its absolute index at least2,
and |C|>=2a>W. The normalized helper, complete comparison norm and
C^2 divisor now satisfy the accepted UNORIENTED absolute cap-anchor
lemma, giving |C|=Y_W(a). This lemma uses signed targets and only one
nonzero target; it does not require the missing scalar signs or F>=0.

The squared cap bounds each main absolute index ji<W. Reducing row218
modulo A-1 bounds its finite signed index-error representative by
4W^3<|A-1|. Divisibility forces that representative to vanish. Thus

    Yi=Y_ki(A), Xi=+/-X_ki(A)                         (1)

for all15 requested indices, including negative and zero ki. A and C
may remain signed. The actual huge pooled sum is not asserted small.
The old cap-in-pool positive-A theorem and its removed (C-W)^2 term
have not been used.

## 4. The signed-A request lemma used at both signs of k

For canonical signed-base Pell values put

    H_j=X_j(A)+(n-A)Y_j(A),
    J_j=X_j(A)-(n-A)Y_j(A), T=2An-n^2-1.

The universal identities H_j J_j=1+T Y_j^2 and
H_(j+1)=nH_j+T Y_j give H_j=n^j modulo T for j>=0.
For 2<=n<W, |k|<W and |m|<W the frame gives |T|>W^W and the
usual differences |m-n^j|,|m+n^j|,|m*n^j+/-1| are<W^W for
1<=j<W. These are absolute bounds and are valid for either sign of A.

For k=-j<0, the +canonical-abscissa branch gives m*n^j=1 exactly,
which is impossible. The opposite branch gives m=-n^j exactly.
For k=0 the two possibilities are m=+1 and m=-1. For k>0 the
canonical branch gives m=n^k, and the opposite branch would give
m*n^k=-1, which is impossible. This is the signed-index lemma proved
independently in the old compression note; its proof does not use that
note's later positive-A/current-cap stage.

Consequently output m>=2 at n>=2 forces k>=1. At n=q+1 with q>=3,
the additional residue m=1 modulo q excludes k<0 because -n^j=-1
modulo q. It permits k=0, selecting m=1. Canonical X and Y themselves
need not be positive when A<0.

## 5. Rebuild the denominator chronology at the actual refined rows

Call4, row253, uses q>=2, t>=16 and pair257/258. Equation(1) and the
positive-index part of section4 give v181=q^t and orient the abscissa
as X_t(A), rather than asserting that it is positive. Call0 at row226
uses this SAME canonical signed pair and base n0=F^2+1>=1. Its recurrence
and small-residue bound give v6=n0^t>=1, including n0=1. The real
opposite-abscissa base-one endpoint is already excluded by call4.

The exact front identity r1+r2-r3=v6+v8-F*B gives F*B=v6+v8>=1,
so F>=1. Moreover n0>F and n0^(t-1)>F, whence

    F*B>=n0^t>F*n0, so B>F^2+1 and q>=3.           (2)

No F graph is needed or restored in the actual refined source. The
inequality is a consequence of these t requests and ceiling alone.

Rows259..266 implement the unchanged SIGNED-A derived pair:

    X_(t+1)=A*X_t+(A^2-1)*Y_t,
    Y_(t+1)=X_t+A*Y_t.

In the literal lowering these are v303+v304 and v257+v259, respectively.
Call6 at row266 therefore gives v189=q^(t+1). No ordinate sign is
assumed in this recurrence. Both L=v181 and Qt1=v189 are divisible by q.

Row7 and retained graph v11>=0 give y=v2=F+v11+1>=2. The actual
q-base call11 has pair333/334, target y+1, output Qy=v211 and row291.
Its complete norm/request lowering is rows287..291. Section4 gives
Qy=q^(y+1), divisible by q.

Retained graphs v225,v226>=0 and row191 give Qx=v223=q*v225+v226+2>=2.
The actual q-base call14 has pair351/352, target x+1 and row306;
its complete lowering is rows302..306. Apply the negative/zero-index
part of section4 to (1). It forces x+1>=1, so x>=0, and gives
Qx=q^(x+1), divisible by q. This is a q-base request, not a q+1 request.
The literal labels/ports are included together in INTERFACE.json.

All four denominator powers L,Qt1,Qy,Qx are now interpreted. The
register N=v26 is still an arbitrary signed integer. No K power,
factorial meaning, N=B^K or q=N^K was invoked in this chronology.

## 6. Successor residues, the last scalar and the strict product

All front rows0..201 are unchanged by refinement. Their complete
eleven identities are the following; each stands for an exact source
row-ideal combination with all quotient products included.

| Call | Output | Digit row | Identity |
|---:|---:|---:|---|
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

Section5 proves these actual outputs are1 modulo q; no sign of their
quotients or of N is a premise. For v16,...,v24, the successor calls
are respectively5,7,8,9,10,12,13,15,16, all at base q+1. Their targets
are vj+1 and section4 proves vj+1>=0. Zero targets have not been discarded.

If v24=-1, unchanged reciprocal rows11/12 give

    B*v27=F^2+1,

contradicting 0<F^2+1<B from (2). Thus v24>=0. This uses no natural
sign for v27 and no CRT or reciprocal-index semantic theorem.

The eight product factors v16+1,...,v23+1 are nonnegative. The exact
fresh monic chain and graph(P) give their product>=1. Therefore no
factor is zero; v16,...,v23>=0. Together with x>=0 and v24>=0 this
recovers precisely the ten removed signs. All those coordinates are
fixed by the temporary helper involution, so the conclusions hold for
the original, possibly unnormalized, refined input tuple.

## 7. Complete witness maps at the whole refined body

From a new-policy zero, perform the argument above, but KEEP the original
unnormalized body and all its retained witnesses. The temporary reflected
assignment was used only to prove signs of reflection-fixed coordinates.
Choose a fresh Legendre triple for each of the ten recovered nonnegative
coordinates, and restore exactly its old graph row. This gives a zero
of the EXACT refined parent at the identical complete399-coordinate
body, identical h, identical signed A/C and identical retained witnesses.
The product chain and its fresh graph are forgotten. No physical F or
old V/d graph is added to the refined boundary.

Conversely start with any refined-parent zero, whose ten scalar graphs
already prove these signs. Compute p2,...,p8 uniquely from the unchanged
body. Their product is at least1, so choose a triple for(P). Forget
the ten old private graph triples and retain every other coordinate and
witness. This gives the new-policy zero without changing h or any Pell
coordinate. These maps establish pointwise-body existential equivalence;
they are not a bijection of Legendre triples.

Only after the old graphs are restored may the accepted COMPLETE refined
source theorem be invoked for calibration. It may normalize/reconstruct
fresh private Pell witnesses at the same native front0..245,376..385,
as its own proof specifies. Composing its ordinary soundness and positive
canonical completeness with the two maps above proves the same native
calibration for this labelled policy. No positive-A inference or old
cap-in-pool summand is imported into the new signed stage.

INTERFACE.json records the whole-parent hashes, complete retained-body
identity, exact removed graphs and private occurrences, literal early/
cap/derived/request rows, the corrected all18 call memberships, all15
signed target interfaces, all37 frame atoms, and the eleven source-ideal
recipes. It is an ordinary interface, with no new source/compiler or
projected measurement. A future implementation must independently check
every coefficient, graph map, fresh symbol and complete runtime closure
before its own separately reviewed execution release.
