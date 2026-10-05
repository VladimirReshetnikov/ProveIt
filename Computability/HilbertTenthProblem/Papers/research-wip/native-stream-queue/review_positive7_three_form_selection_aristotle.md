# Independent proof and all-r ledger review of three-form relator selection

The three-form relation and its revised arithmetic ledger pass independent mathematical review. For r>=1, the certificate has (277+50r+lambda) multiplications and (550+62r) additions/subtractions, where lambda=floor(log2(62+8r))+popcount(62+8r)-1. Its single-polynomial finalizer gives 895+112r+lambda operations, with 23 comparisons and 96+8r positive witnesses. These are symbolic compiler-family counts, not a numerical universal bound. The preceding r=0 source remains the intentional 903-operation branch.

One editorial statement in the frozen root primary needs qualification: its shared S4 producer is syntactically live through S even at r=0. Review remark 3 below retains and corrects that statement. This does not change the r>=1 projection, any operation count, or the adopted r=0 branch. No further correction was found.

This review checks the full new local proof, the full root primary proof, and the uniform stage ledger. Complete literal-source authentication belongs to the independent Riemann companion; no saved arithmetic source is evaluated or certified row by row here. Pascal authored the integer-form interface and simultaneous induction; root supplied the weighted-bound continuation and complete-source composition. The reviewer independently derived the projection and stage counts before reading the root primary.

## 1. Integral fixed data and positivity before any digit interpretation

For P=[p,q;s,t] with pt-qs=1, direct multiplication in the inherited representation

    S(P)=[p^2,-2pq,q^2; -ps,pt+qs,-qt; s^2,-2st,t^2]

fixes w0=(2q,p-t,-2s)^T. Its three resulting coordinates are 2q(pt-qs), (p-t)(pt-qs), and -2s(pt-qs). The inverse has the negative corresponding vector, so both S(P)-I and S(P^-1)-I have rows orthogonal to the same primitive w. A zero w0 forces P=I or -I; the specified zero E matrices and default u,v therefore handle all central cases without division by zero.

After a fixed coordinate permutation with w1 nonzero, put g=gcd(w1,w2)>0 and choose a*w1+b*w2=g. Primitivity gives gcd(g,w3)=1. Every integral row (x,y,z) orthogonal to w has g|z and equals

    (b*x-a*y)*(w2/g,-w1/g,0)
      +(z/g)*(-w3*a,-w3*b,g).

This proves an integral row-lattice basis, including negative entries or w2=0. Undoing the same coordinate permutation in the two basis rows supplies the stated integral E_plus,E_minus in the original output order. No runtime division or hidden witness is needed.

For C=[1,0,0,-1;1,1,0,-2;2,0,1,-4], let ell_j be the two basis rows composed with C. The prescribed lambda_j makes every a_ji=ell_ji+lambda_j at least one. Hence S4>0 and A_j>0 on all positive history assignments, and A_j<=M*S4<=M*S. These inequalities concern the whole integers, so they are available before proving any no-carry property. Fixed coefficients, offsets, M, K and kappa_minus_one must come from the same actual fixed alphabet and relator recipe; they are not independent existential parameters. There are 5+22r fixed roles in the adopted complete grammar.

With D=S0+height_slack, B=KD, J the sum of nonnegative selector unhats and P=(B-1)J+1, all packs are nonnegative and P>=1 off the comparison locus. Composing the native header to 16A_pack+12, 16M_pack+10 and 16Z_pack+8 is the inherited unconditional padding identity. At a zero, M*S+Ztot+g=P forces J>=1, B<=P and all H_i, selected outputs and formed inputs below P. The ordinary masks and power-test lane obey the inherited bounds as well. Thus native pretyping is established before interpreting any selected formed digit.

The prescribed native theorem first gives dyadic P, then its D lane gives dyadic D and B. Divisibility B-1|P-1 yields P=B^n, n>=1. Since m=8+2r<B, the Boolean selector checksum has no cell carry and is exactly one-hot. At this point the new native lanes select canonical digits of S4,A1,A2; unconditional linearity in the separate history digits has not been assumed.

## 2. Independent simultaneous state/form induction

Expand each canonical history and each formed input in n base-B digits. Every action word is a fixed linear expression in those streams and the raw selected streams. Its formal coefficients may be signed or noncanonical in the unrecovered suffix. Those higher coefficients do not affect lower modular recovery in the exact recurrence BV_i=H_i+PF_i-z_i.

At the lowest cell, reducing the recurrence modulo B recovers H_i(0)=z_i because S0<D<B. The subset mass is then below D and each positive form value is at most M*S0<MD<B. With no incoming carry at cell zero, all formed digits equal the intended linear expressions. Uncentering the selected forms and applying E_sigma therefore yields the genuine relator difference. The unchanged paired action and positive common baseline supply the genuine positive matrix update, whose total is Cmass*S0<B.

Suppose the earlier cells and their form digits have been recovered. Subtracting the known lower coefficients from the recurrence recovers the next history cell modulo B: the preceding genuine action has total at most Cmass*(D-1)<B, so no coordinate can wrap. Earlier aggregate masses were below D, hence there is no incoming carry in S. Its current canonical digit is the recovered mass, already below B; the aggregate AND lane forces that mass below D. Only now interpret the current S4 and A_j digits. Their earlier values caused no carry, and their current values are at most M*(D-1)<B. The form digits are therefore genuine and carry-free, and the selected, uncentered action is correct at this cell. This is the required order of implications; no typed form at cell j is used to recover its own history cell.

Induction reaches the last pre-state, and the top coefficient fixes the genuine positive terminal. F7=F1 imposes the same acceptance equality with six terminal witnesses. The initial coordinates 3 and 1 differ, so restricting the repunit duration to n>=1 discards no accepting empty word. The proof preserves accepted-word and ordinary-input projection; it does not assert an all-ring identity or a same-witness map to the former four-selection relation.

For completeness choose a dyadic D above every state mass in an accepted finite trajectory. The formed coefficients are then below MD<B. A paired cell's selected total is at most its mass, while a relator cell contributes S4+A1+A2<=(2M+1) times its mass. Therefore Ztot<=(2M+1)S and S<=(D-1)J. The new slack satisfies

    P-M*S-Ztot >= [(K-3M-1)D+3M]J+1 > 0.

All selected zero values have positive hat one; histories and endpoints are positive because the actual matrices and input are positive. The native converse supplies fresh positive auxiliaries at the changed packs and scale. This establishes positive completion without assuming that the old native auxiliaries or global slack can be reused.

## 3. Independent complete stage ledger

Let m=8+2r, N=52+6r and L=m+N+2=62+8r. Seven histories, six terminals, m selector hats, N selected-output hats, two slacks and 21 fresh native auxiliaries total m+N+36=96+8r positive coordinates. The new forms are computed, not additional witnesses. Only the global comparison, 15 native comparisons and seven recurrences are required, totaling 23.

The unchanged outer prefix at general m,N costs (m+5)M+(2m+2N+14)A. The weighted product M*S adds one M. The shared six-addition schedule computes both S4 and S, exactly the former S-only addition cost. Thus the revised prefix is (14+2r)M+(134+16r)A. This includes all selector/selected unhats, checksums, bounds and reused per-letter masks.

Two four-term positive forms per relator cost 8M6A. Each sign's two offset subtractions cost 2M2A and its E action costs 6M6A, including both additions into each of three existing accumulators. Across both signs the action append is 16M16A; no extra pair aggregation or unpaid accumulator update is omitted. Adding the inherited 30M168A paired cut and 12M21A fused postprocessor gives (42+16r)M+(189+16r)A.

The A and M Horner packs each need L-1 products and additions. The output pack's highest coefficient is literally zero, leaving L-2 of each. This gives 3L-4=182+24r of each operation type. The native certificate remains all 64 rows, 33M31A; only its separate standalone finalizer is replaced. The fixed binary chain for P^L costs lambda(L) products. Six distinct P*F_i products serve the seven right sides, each with one addition and one subtraction, giving 6M14A.

| Disjoint stage | M | A |
|---|---:|---:|
| Outer prefix, weighted guard and shared masses | 14+2r | 134+16r |
| Two positive input forms per relator | 8r | 6r |
| Three packs | 182+24r | 182+24r |
| Fixed prescribed scale | lambda(L) | 0 |
| Native certificate | 33 | 31 |
| Paired action, relator appends and fused lift | 42+16r | 189+16r |
| Seven recurrence right sides | 6 | 14 |
| Certificate | 277+50r+lambda(L) | 550+62r |
| Residuals, squares and sum | 23 | 45 |

The last row pays 23 residual subtractions, 23 squares and 22 additions. The resulting full count is 895+112r+lambda(L). Compared with the preceding plane compiler the exact delta is 10r-1+lambda(62+10r)-lambda(62+8r); neither power-chain difference is silently treated as zero or monotone. These uniform formulas are derived from the explicit grammar, not extrapolated from finite examples. They do not replace the separate full-source audit.

## 4. Retained boundaries and one editorial correction

**Review remark 1 (AND-linearity and the former mass bound).** The author's B=8 example is valid: (5+1+1+1) AND7=0, while the four individually selected values sum to 8. It refutes only unconditional linearity of selection. Likewise the old bound Ztot<=S fails here: at an all-ones relator cell S=7 but S4+A1+A2>=12. These are local interface examples, not claimed full compiler zeros. The simultaneous induction and weighted global margin address the actual two gaps.

**Review remark 2 (qualified two-form obstruction).** For noncentral P, minors 2q^2 and 2s^2 prove rank(S(P)-I)=2; the right invariant proves rank at most two. The decoder C has a unimodular three-column submatrix and kills the positive vector (1,1,2,1), so W=(S(P)-I)C has rank two and the same positive kernel vector. A homogeneous linear form nonnegative on every positive integer four-vector has nonnegative coefficients. If two such forms allowed a fixed linear reconstruction of W, their rows would span its rowspace and both annihilate that positive kernel vector, forcing both to vanish. This is a correct obstruction to that specific unconditional two-form linear interface. It does not exclude guarded affine offsets, nonlinear reconstruction or restricted state domains. The author's proposed DJ-centering alternative remains a credited separate open question.

**Review remark 3 (correction to frozen primary's zero-relator liveness rationale).** The root primary's Review remark 4 states: "Neither formula is asserted for r=0, where a new S4 producer would be unused; that branch retains the existing 903-operation source." The no-form branch and its 903 count are correct, but the unused-producer rationale overstates the situation after adopting the shared schedule. Its S4 feeds S=h123+S4 and is syntactically live even at r=0. Only a separate extra S4 producer with no consumer would be dead. The old r=0 source is intentionally retained; that choice is not forced by liveness of the shared S4. Root accepted this correction while preserving the frozen primary bytes. No source row, count, projection theorem or adopted branch changes.

**Review remark 4 (valid conservative schedule, not a false bound).** The earlier 898+112r+lambda bound charged a separate S4 producer and was a valid conservative r>=1 schedule. The shared six-addition mass schedule removes those three additions and gives 895+112r+lambda. Neither count is a numerical universal bound: the inherited fixed universal presentation and its numerical relator count remain unmaterialized. No new degree bound or arithmetic optimality claim is proved.

## 5. Exact bindings and execution limits

The principal frozen bindings are:

| Artifact | SHA256 |
|---|---|
| positive7_three_form_relator_selection_pascal.md | afafae86d814ef57041d54d511e35ae72f9ccd9ca47dc75ed1f12dcd68184ac5 |
| positive7_three_form_relator_selection_pascal.json | 3005d2a7389c6364b6f38905206fe47aec067f643cb4bd9da3fc1e92c4ac22aa |
| positive7_three_form_compiler_root.md | d1d794b3d1534b60094741ca3edc57cf0a48d099c701a0685a868abfc00bb3c2 |

The companion metadata pins the final author proof/receipt, the full frozen root primary, and the stated proof dependencies with byte counts and inclusive read spans. This reviewer read the author proof in full, followed by the final small fixed-linear-reconstruction/evidence update, and read the root primary in full. The preceding local plane proof and sparse stage derivation were read again; the inverse-pair, weighted7, one-AND geometry and native interfaces were fully read earlier in this same continuing review chain. Those inherited foundations are not claimed as new external group or native theorem audits.

The local author's complete-source question is resolved only through the separately emitted root source and its independent Riemann audit; the present note supplies its independent proof/ledger component. The review does not execute or import any supplied, archived, committed, predecessor or frozen helper, evaluate a saved source or coefficient array, propagate degrees, test native witnesses or run a build. Only new byte/metadata processing is used. There is no scientific test count or sample claim. Files are confined to /tmp; repository/Git and all earlier frozen artifacts are unchanged.
