# A sign-independent Round16 radix and coherent guard composition

This is a CODE-FREE ordinary design for the source131 direct cofinal/self-radix architecture. No source, compiler, checker, optimizer, projected equation or numerical frontier is emitted or executed. The source is not the accepted327 body. Its square horizon, cofinal beta base, self-sized radix, positive-A cap anchor and complete Round15/C222 calibration remain explicit dependencies.

Three separate policies are proved below: a square-radix architecture with the original guards; an additional eleven-remainder reparameterization plus a strict eight-factor guard, retaining x>=0; and an optional x-fused strict guard. The second and third policies require the remainder repair. Merely replacing the old positive sum by squares does NOT license the old compressed-guard theorem on the unchanged incoming body.

## 1. Exact input and actual namespaces

The original archive is `ConZFC_Shared_Pell_Caps_Round16_2026-10-25.zip`, SHA256 `97c828ef295d52ea53800dc0761e94cc5605dec306aae3eeecef1d074fa254f8`, from commit `fd3e384e92ed4813a5536f877c5cd835ca4c75d2`, Git blob `d48000bbfe86ad6a3d8ade43f8bdfd19d20f33d7`. The complete input artifacts below were byte-compared against their original ZIP members; no incoming code ran.

| Placed member, relative to source131/direct | SHA256 |
| --- | --- |
| `cap_cofinal_self/source.json` | `110c68baefdd955bd5af9af44564e81b9a43a08a088a3424c913bc185178a845` |
| `cap_cofinal_self/guarded.json` | `6cc3a1548b5829159f7c171d4c3e904d4448557becfb540efb809e23887cc817` |
| `cap_cofinal_self/transform_certificate.json` | `f0740929667f2e2f88ab8e921a45aee5890de0999676dad877e5b820fb0e2ebf` |
| `build_cap.py`, read inertly only | `522d5aee9a5ca0a017381da6f07d6d2dc87944ba6ffbe187afad4d79faf1ebc3` |

The actual source has coordinates0..540 and rows0..397. All indices in this note refer to that unprojected source, not the older refined/327 namespace. Write

    t=v0+16, x=v1, y=v2, F=v3, F^2=v4,
    B=v5, V0=v6, N=v26, q=v179,
    L=v181, Qt1=v189, Qy=v211, Qx=v223,
    R0=v25=2+t+x+y+F, K=2R0,
    W=v245, A=v246, baseBH=v522.

The independent positive CRT representatives intended by the original source are a_j=v_j+1, j=16..24. The actual frame row is381, not the certificate's pre-deletion frame-row address444. It is W=2+sum38 distinct complete affine base/exponent/output atoms squared. It includes a_16,...,a_24, q, q+1, K, N and baseBH. The cofinal rows are383 (`v0=v523^2`) and384 (`y=V0(V0-1)`). The source keeps A>=0, the positive linear cap and its common multiplier guard; this proposal does not silently import the refined signed-A/signed-cap policy.

## 2. Square majorant: one monic quadratic definition

Replace H0=1+sum(a_j)=10+sum(v_j) by

    Hstar=2+sum_(j=16)^24 v_j^2.                      (H)

For every integer v, |v+1|<=v^2+1. Hence, without any representative sign premise,

    Hstar>=2, |a_j|<Hstar, and a_j+1<=Hstar if a_j>=0.

Introduce one fresh unrestricted coordinate for Hstar with its monic quadratic defining row. Replace only the old self-radix definition at row382 by baseBH=B*Hstar. That consumer is quadratic too. Nine square terms need not be nine new square coordinates. No sign graph is needed for Hstar; it is outside the frame, while the existing baseBH port522 remains in the frame. Every actual occurrence of baseBH in the three private power-base rows and the frame remains the same port.

The alternative 1+sum(a_j^2) also works, but (H) has only its constant and nine square monomials, rather than additional linear terms. No optimizer retention or size prediction follows from this observation.

The entire existing W is an invalid shortcut. W>q^2 holds at its frame row. If one set q=(BW)^K after B>=2 and K>=2, then q>=4W^2>W, contradicting W>q^2. The nine-representative slice (H) is independent of q, its outputs and the future private Pell frame; the entire frame is not.

## 3. Actual requests and early order

The primary norms and pool retain the fifteen target/pair records of the certificate. The complete actual power membership is:

| Call | Congruence row | Base | Target | Output | Primary pair |
| ---: | ---: | --- | --- | --- | --- |
|0|217|v4+1|t|v6|257/258|
|1|228|B|K|N|274/275|
|2|233|baseBH|K|q|274/275|
|3|244|q+1|t+v4|v180|296/297|
|4|250|q|t|L|257/258|
|5|258|q+1|v16+1|v188|319/320|
|6|266|q|t+1|Qt1|derived from the t pair|
|7|274|q+1|v17+1|v195|341/342|
|8|282|q+1|v18+1|v200|355/356|
|9|290|q+1|v19+1|v205|369/370|
|10|298|q+1|v20+1|v210|383/384|
|11|306|q|y+1|Qy|397/398|
|12|314|q+1|v21+1|v217|411/412|
|13|322|q+1|v22+1|v222|425/426|
|14|330|q|x+1|Qx|439/440|
|15|338|q+1|v23+1|v229|453/454|
|16|346|q+1|v24+1|v234|467/468|
|17|354|q+1|v171+1|v240|481/482|

Keep factorial guards v7,v8>=0, q slack v185>=0, A>=0, the common multiplier v532>=0 and the positive cap. Rows3/166 give B=v7+v8+1>=1 and q=B+v185+1>=2. Row383 gives t>=16. Frame381 and scale rows201..203 give the original absolute port bounds and A>W^W, independently of the nine CRT signs. The cap rows385..397 with its guarded predicate at424 prove C=v525=Y_W(A) and recover all fifteen signed target ordinates. This original positive-A cap argument permits signed/zero proposed targets and does not use their scalar graphs.

Call4 at t>0, q>=2 fixes the t abscissa to its canonical value and yields L=q^t even for initially signed L. Call0 on the SAME pair then gives V0=(F^2+1)^t>=1, including the possible base one before F is known. The whole-row identity r1+r2-r3=V0+v8-FB forces F>=1. With n0=F^2+1, t>=16 gives n0^(t-1)>F, hence B>n0 and q>=3, without factorial/binomial semantics. Row384 now gives y=V0(V0-1)>=F+1>=2.

For the x-retained policy, x>=0 and row10 give K>0. The two genuine K requests then give N=B^K and q=(B Hstar)^K. L, Qt1, Qy and Qx are positive powers q^t, q^(t+1), q^(y+1), q^(x+1); the t+1 pair is the literal derived recurrence, not a new seed. Their interpretation uses their indices and signed-output request lemma, not any interval-product sign. In particular all four are divisible by q and greater than2 before interval signs or any CRT scalar restoration.

For clarity, at A>W^W, 2<=n<W, |k|<W, |m|<W, the signed-index request lemma is as follows. At k>0 the canonical branch gives m=n^k; the other would give m*n^k=-1. At k=-j<0 the canonical branch would give m*n^j=1; the opposite branch gives m=-n^j. At k=0 the outputs are +/-1. These follow from the canonical recurrence modulo T=2An-n^2-1 and the strict absolute frame bounds, which make the entire small differences less than T. In particular m>=2 at a positive base forces k>0. No initially signed output is assumed positive to prove this lemma.

## 4. What the squared radix alone proves

First retain ALL original scalar and interval guards. After the preceding powers, q=(BHstar)^K=N Hstar^K>=B^2>V0 follows from V0<=BF<B^2. The first binomial digit is exact, and the original square-radius fixed point gives F=t!. The product formula and pairwise coprimality of d_i=1+F^2/i are unchanged, so N=B^K remains the original CRT precision, with N|q.

Every independent representative satisfies 0<a_j<Hstar. For ordinary cutoff1<=k<R0 and j<=k, binom(a_j,j)<=a_j^k<Hstar^K<=q. For the derived label, the same actual monotone-constructor ledger gives Jlabel<=Hstar^ell, ell=4194304: its four syntax parameters plus one are bounded by Hstar. The retained t>=16 and F=t! give ell(t+1)<2F<K, so every needed derived-label coefficient is also below q. The local Horn bound R0^8388608<2^R0<2^K is unchanged. Thus all exact digit/range, prime-power precision and multiplicity arguments have the same required inequalities.

Completeness starts with a finite C222 refutation, pads to a chosen sufficiently large t=16+h0^2, sets F=t!, V0=(F^2+1)^t and y=V0(V0-1), and chooses the beta-CRT code x. The consecutive beta moduli remain pairwise coprime, and y exceeds the pending-multiset bound exactly as in the direct proof. Then fix R0,K,B,N and choose all nine independent positive representatives by CRT at d_i^(2K). Only AFTER those choices compute Hstar and q=(B Hstar)^K. No bound a_j<N^2 and no future-radix CRT choice is needed. Fill genuine powers/digits and reconstruct W, its odd frame, cap and every private Pell/comparison witness afresh as in the original proof.

This proves an architectural existence equivalence, with the same complete C222/ZF-to-ZFC ordinary calibration and cofinal promises. It is not a map fixing the old H0 source body: q, its powers, their remainders, W and private Pell witnesses generally change. Mapping an old-H0 zero to a new-Hstar zero goes through its decoded refutation and a fresh canonical construction, and conversely through that same soundness/calibration. The old324 polynomial or its coefficient census is not identified with this new source.

## 5. The actual obstruction to blind scalar composition

The incoming body uses RAW digit remainders. For example actual rows169/170 state

    v188=r191+N*Qt1*v190, Qt1=r191+s192+1.

They do NOT state v188=1+q*u191+N*Qt1*v190. The latter identity in the accepted compressed source uses a prior residue-one reparameterization. Raw r191*s192>=0 by itself does not imply r191=1 modulo q, nor can positivity of v188 be used to prove the missing sign of its target. Thus Hstar alone resolves the sum-majorant dependency but not this second, independent source-interface difference. No strict-eight or x-fused theorem on the unchanged raw remainder body is claimed.

## 6. Explicit eleven-remainder repair and privacy

On the Hstar architecture, simultaneously replace each listed raw remainder coordinate r by 1+q*u, reusing its coordinate as the unrestricted integer u. Change just its two body rows accordingly. Replace its old product guard r*s>=0 by u*s>=0 with a fresh private triple.

| Raw r / slack s | Digit row | Bound row | Output m | Denominator D | Product graph / old triple |
| --- | ---: | ---: | --- | --- | --- |
|183/184|164|165|180|L|412 / 583..585|
|191/192|169|170|188|Qt1|413 / 586..588|
|197/198|172|173|195|Qt1|414 / 589..591|
|202/203|175|176|200|Qt1|415 / 592..594|
|207/208|178|179|205|Qt1|416 / 595..597|
|213/214|182|183|210|Qy|417 / 598..600|
|219/220|185|186|217|Qy|418 / 601..603|
|225/226|189|190|222|Qx|419 / 604..606|
|231/232|192|193|229|Qx|420 / 607..609|
|236/237|196|197|234|L|421 / 610..612|
|242/243|199|200|240|Qt1|422 / 613..615|

In the WHOLE raw body each r occurs only in its listed digit and bound row; this was checked against every body residual. None is a frame atom, target, base, output, primary pair or cap/pool port. Each old interval auxiliary occurs only in its listed graph. Thus no power/frame/private Pell coordinate is changed by this reparameterization. The new row forms are quadratic:

    m=1+q*u+N*D*v, D-2=q*u+s,                  (R)

except choose0, where m=1+q*u+L*(B+q*high). Here the existing multiplication gates remain; (R) displays their exact elimination identities. For ranges a,b,c,d and the derived label the existing product gate is N*Qt1=v193; for S/Sp it is N*Qy=v215; for u/vq it is N*Qx=v227; for index it is N*L=v238. No cubic row is introduced by replacing the raw linear remainder occurrence in its two actual quadratic rows.

Whenever q>=3 and D>2 is a genuine denominator, u*s>=0 and q*u+s=D-2>0 force u,s>=0. Conversely in any complete Hstar raw-source zero, all targets are positive and each actual m=(q+1)^positiveindex is1 modulo q. Since q|D, its raw remainder satisfies r=1 modulo q (also in choose0 since q|L). The original interval bound gives r>=0, so r>=1 and u=(r-1)/q>=0. The source's derived-label positivity after restored representatives is the monotone-constructor sign ledger; actual row155 gives v171=20+6v16+8v17+2v29+v170 with its positive-prefix dependencies.

These observations give BOTH pointwise-kernel maps. From a repaired zero after D>2 is proved, restore r=1+q*u and choose a fresh old triple representing r*s; discard the new u*s triple. Conversely retain all other body/kernel ports of a complete raw zero, set u=(r-1)/q and choose a fresh triple for u*s, discarding its old r*s triple. Every other retained graph witness is fixed. No triple is reused for a different integer. These maps change exactly the eleven remainder coordinates and their specified private witnesses; they are not a bijection of representations or an equality of whole SOS polynomials.

## 7. Strict eight-factor compression, retaining x

After the repair, remove precisely the nine scalar graphs for v16..24: rows401..409, private triples550..576. Each of these27 auxiliary coordinates occurs only in its own removed graph in the whole guarded source. Keep x's graph at398 (541..543), factorial7/8 at399/400, q slack185 at410, A at411, common multiplier at423 and the cap at424. The eleven modified interval-product graphs remain.

Adjoin seven unrestricted monic partial products p2,...,p8, outside all old frame/kernel ports, with p2=(v16+1)(v17+1), pj=p(j-1)(v(15+j)+1) for j=3..8. Replace the nine old scalar graphs by one fresh Legendre graph P8-1>=0, P8=p8. No partial product is otherwise guarded.

The section3 chronology remains valid without these nine signs, because Hstar is positive independently and x is retained. Hence L,Qt1,Qy,Qx are genuine positive powers divisible by q before their interval signs. Every one of the eleven repaired identities (R) gives m=1 modulo q without any quotient sign. For calls5,7,8,9,10,12,13,15,16, a negative target vj+1 would give m=-(q+1)^ell=-1 modulo q, impossible for q>=3. Thus vj+1>=0 for all j=16..24. A zero target is still allowed here.

If v24=-1, rows11/12 give B*v27=F^2+1, impossible since0<F^2+1<B. Therefore v24>=0 independently of the strict product. The other eight factors are nonnegative before P8>=1 is used; their strict product then forces each positive, so v16..23>=0. The eleven genuine denominators are now >2, and their repaired product graphs restore u,s>=0 as in section6. All old Hstar scalar and interval predicates can therefore be restored with fresh triples on the original kernel ports, and the architecture theorem of section4 applies.

Conversely every complete Hstar raw-source zero maps through section6 to repaired remainders, has all eight factors positive, and extends uniquely to the seven partial products and existentially to a fresh strict-product triple. Retain every other body/kernel coordinate and unaffected witness. This proves the strict-eight policy's ordinary soundness and completeness, using fresh guard triples and the complete Hstar architecture theorem rather than an unchanged-body claim about324.

## 8. Optional x-fused theorem: a different ninth factor

After the same eleven-remainder repair, one may additionally remove x's graph at398 and replace the strict P8 graph by a single directly quadratic Legendre graph

    (x+1)*P8-1>=0.                              (X)

Its fresh triple is not reused from the strict-eight predicate. This is a new x-fused policy; it is NOT the old v11-fused theorem. There is no endpoint-r0 graph left to remove in Round16: cofinal y already restores it.

Without x>=0, repeat the t/q/F/y bootstrap first. Since B>F^2+1 and Hstar>=2, baseBH=B Hstar>=2 independently of all omitted scalar signs. Call2 has candidate output q>=2. By the signed-index request lemma it forces K>0 and orients the shared274/275 pair canonically. Call1 on that pair then gives N=B^K. This does not use positivity of R0 from its constructor or of x.

Qt1 and Qy are already positive genuine powers. For Qx, exclude its zero target without any output-sign premise. Actual rows4/8/9 give

    v13=(t+1)y, x-1=(1+v13)*v12.

Because t>=16 and y>=2, Mbeta=1+(t+1)y>=35. At x=-1 this would make Mbeta divide-2, impossible. Hence k=x+1 is nonzero. Call14 gives Qx=q^k if k>0 or Qx=-q^(-k) if k<0. In BOTH cases q|Qx. Its sign is not used before (X).

All eleven identities (R) therefore still give m=1 modulo q: those using Qx require only its divisibility, not positivity. The same nine successor calls give all factors v16+1,...,v24+1 nonnegative, and v24 is restored separately by the reciprocal-index rows. Thus P8>=0 before (X). Its strict sign forces P8>0 and x+1>0, so x>=0 and all eight factors are positive. Qx now becomes its genuine positive power as well. Only at this point are D>2 and the weighted interval-product sign lemma applied to the two Qx pairs and the other repaired pairs. There is no use of product signs to orient a denominator needed earlier.

The resulting old Hstar zero keeps every original kernel port and all unaffected witnesses. Restore x's old triple and the nine CRT scalar triples freshly; restore every raw remainder and interval triple as in section6; discard the new strict triple and partial products. In the converse, x>=0 and P8>=1 imply (x+1)P8-1>=0, so a fresh triple lifts. This proves both existential directions. It makes no projected variable-count claim.

## 9. Existing policies and remaining verification boundary

The original support pairs183/184 and191/192 are ALREADY interval product guards at412/413; there are no four scalar graphs there to compress again. After the repair their coordinate meanings are u/s, so all eleven product triples must be re-chosen under the maps, not silently inherited. The accepted strict-eight argument applies only after the explicit residue-one repair. The old v11 fused ninth factor removes no graph here; optional section8 uses x+1 instead and proves its own order.

All new majorant/partial-product/guard symbols are disjoint unrestricted integers outside the old frame. The architectural Hstar change requires fresh semantic and private witnesses, while the later remainder/guard maps preserve kernel ports pointwise as explicitly stated. The source131 square-horizon and beta-base completeness, derived-label/local-majorant ledger and entire C222/ZF/ZFC ordinary calibration remain required; none is inferred from the accepted327 body or its measurements.

Before implementation or endpoint acceptance, a fresh held source packet must bind every changed whole row, all old/new coordinate and graph namespaces, complete occurrences/privacy, all18 joined request rows/54 ports,15 targets/primary norms,38 affine frame atoms, the entire11 identity collection, full native/compiler dependencies and both witness maps. Any subsequent factoring/projection/free-coordinate/translation and every quartic coefficient require their own complete review and released replay. No incoming runtime closure, materialized source, numerical census or canonical promotion is supplied by this code-free proposal. Existing327 and every source/projection/page/Lean parent remain unchanged.
