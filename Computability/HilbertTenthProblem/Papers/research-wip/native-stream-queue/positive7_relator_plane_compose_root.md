# A complete positive7 compiler with integral relator-plane actions

The complete sparse positive7 compiler now uses the common fixed plane of each relator and its inverse. Each relator pair costs 21M+19A to update its three existing increment accumulators, replacing 24M+24A. The complete source therefore saves exactly 3r multiplications and 5r additions for r presentation relators.

Put ell=62+10r and lambda(t)=floor(log2 t)+popcount(t)-1. The certificate costs

    (276+53r+lambda(ell))M+(550+69r)A.

Its 23 comparisons and 96+10r strictly positive existential coordinates are unchanged. One combined finalizer adds 23M+45A, so the complete single-polynomial source has

    (299+53r+lambda(ell))M+(595+69r)A
      =894+122r+lambda(62+10r) operations.                 (1)

The source preserves the parent's final polynomial on all supplied integer assignments when both sets of fixed coefficients are prepared from the same actual relator matrices. It consequently preserves the same positive witness tuples and ordinary-input projection. The old and new fixed coefficient roles are different: equality is not asserted for arbitrary independent assignments to both sets of roles.

The actual universal presentation, its r and its numerical coefficients remain unmaterialized. The formal r=0 source still costs 903 operations; it has no relator action to improve and is not claimed to be universal. Formula (1) is a complete compiler-family count, not a new numerical universal bound. The complete general84 result is unchanged.

## 1. Exact integral factorization and fixed data

The [local proof](positive7_relator_plane_action_pascal.md) and [independent proof review](review_positive7_relator_plane_action_aristotle.md) establish the following recipe. For a fixed relator matrix P=[p,q;s,t] in SL2(Z), use the inherited congruence representation S(P) on three coordinates and the decoder

    C=[1,0,0,-1;1,1,0,-2;2,0,1,-4],
    W=[(S(P)-I3)C | (S(P^-1)-I3)C].

The eight runtime inputs are the existing four raw selected words from the positive relator slot, followed by the four from its inverse, in coordinate order 4,5,6,7. The pair increment is Wz. These raw inputs and the old (d,e,f) accumulators are computed values already available in the parent source; they are not newly introduced positive witnesses.

The row n0=(s,p-t,-q) fixes both S(P) and S(P^-1). If it is nonzero, divide by its positive gcd and permute the three output rows to obtain a primitive row n=(n1,n2,n3) with n1 nonzero. Apply the same permutation to W, obtaining W'. If n0 is zero, P is I or -I and W=0; use n=(1,0,0), identity permutation and W'=0. This central case avoids division by a zero gcd.

Let g=gcd(n1,n2)>0 and fix integers a,b with a*n1+b*n2=g. Since n is primitive, gcd(g,n3)=1. Every column (x_j,y_j,z_j) of W' lies in the integer plane n1*x+n2*y+n3*z=0, so g divides z_j. Precompile

    alpha_j=b*x_j-a*y_j, beta_j=z_j/g, j=1,...,8,
    u1=n2/g, u2=-n1/g,
    v1=-n3*a, v2=-n3*b, v3=g.

All 21 coefficients are integers. The exact factorization is

    W'=[(u1,u2,0)^T (v1,v2,v3)^T] * [alpha;beta].

For example, the first reconstructed column entry is

    (n2/g)(b*x_j-a*y_j)-(n3*a/g)z_j=x_j,

by the plane equation and Bezout identity; the other two entries follow identically. Thus the construction proves an integer factorization rather than merely noting a rational rank bound. Gcd computation, Bezout choices, permutations and exact division are all preparation of fixed numerals. None is performed on supplied runtime values.

The source also retains the actual alphabet's common positive7 lift, its fixed kappa_minus_one, dyadic K and program-slice alpha,gamma. These four base roles keep their previous meanings and constraints. The new 21 roles per relator must be derived from the same P that determined the old 24 relator_delta roles and the positive lifted letter. They are not independent coefficients or existential choices.

## 2. Paid local source and inverse coordinate permutation

For one relator pair the source computes two eight-term forms

    A=sum_j alpha_j*z_j, B=sum_j beta_j*z_j.

Each form has eight products and seven additions, totaling 16M+14A. It then computes

    X1=u1*A, X2=v1*B, Y1=u2*A, Y2=v2*B, Z=v3*B,
    X=X1+X2, Y=Y1+Y2,

at cost 5M+2A. Finally it adds X,Y,Z to the three old accumulators in the original coordinate order, at cost 3A. The complete append costs 21M+19A=40. Products by zero, negative or unit fixed numerals remain charged in this uniform schedule.

The fixed permutation is recorded as a list pi whose entry pi[k] is the original coordinate index of row k of W'. The emitted append is therefore accumulator[pi[k]]+chart_output[k]. This explicit indexing returns every value to the proper d,e,f coordinate. The permutation itself is a static register binding, not a runtime operation, witness or controller.

The full recipe accepts any fixed permutation for which the prepared normal has first coordinate nonzero, with the matching row permutation used in preparing all coefficients. The saved examples include nonidentity choices: r=1 uses (2,0,1); r=4 uses (0,1,2), (1,0,2), (2,0,1), (0,2,1). These are formal fixed chart choices, not a claim that numerically unknown universal relators have those particular normals. An actual instantiation chooses charts consistently with its actual P matrices. The proof and count apply to every valid fixed choice, not only these examples.

## 3. Complete source substitution and positive projection

The immediate parent is the [complete inverse-pair compiler](positive7_inverse_pair_compose_root.md). Its paired-letter subgraph already costs 30M+168A on 52 raw words. The new original metadata-only composer preserves that entire 198-row subgraph and every preceding row literally. It removes only the subsequent 24r relator products and 24r accumulator additions, replacing them by r sequential 40-row plane append blocks.

Each append starts with the current three d,e,f accumulators, so multiple relators are fully aggregated. The first three increments a,b,c remain the paired outputs. The final six outputs rebind exactly the six old increment exits in the parent's action suffix. All source rows in that suffix are otherwise unchanged, including the fused positive7 action, the right sides of all seven recurrences, every comparison residual, every square and final sum.

For the valid fixed coefficient recipe, each new append contributes the same Wz as its old pair. Induction over the r append blocks proves equality of the final three accumulated polynomials. The other three cut polynomials are unchanged. Substitution at these six exits then proves equality of every suffix value and of the final polynomial on all integer assignments to the common supplied coordinates. Reordering the finite sums changes no integer polynomial.

All ordinary input and positive supplied coordinates, raw selection producers, native lanes, packs, initial and terminal ports, comparison endpoint names and the final output name are unchanged. The 64-row native block and all its 15 comparisons remain literally present. The same-tuple positive-zero correspondence follows from the final polynomial identity; the parent's already proved ordinary-input projection applies without a new carry, sign or native-extension argument.

The named fixed-role count changes from 4+24r to 4+21r. This is a change in how the same actual relator action is prepared and evaluated; treating old and new coefficient roles as unrelated variables would remove the premise needed for the identity. No runtime division, normalization predicate, extra domain assumption or additional positive witness is hidden by that preparation.

## 4. Complete ledger and saved examples

The disjoint stage count is

| Stage | M | A |
|---|---:|---:|
| Input, mass, geometry, bounds and masks | 13+2r | 134+20r |
| Three sparse packs | 182+30r | 182+30r |
| Fixed power P_outer^ell | lambda(ell) | 0 |
| Complete prescribed native block | 33 | 31 |
| Paired increments, plane appends and fused action | 42+21r | 189+19r |
| Seven recurrence right sides | 6 | 14 |
| Certificate | 276+53r+lambda(ell) | 550+69r |
| Combined finalizer | 23 | 45 |

P_outer denotes the parent's computed lane radix, distinct from a fixed relator matrix P. The lane count ell remains fixed by r; the unbounded history length is still reconstructed through the same repunit geometry. There are no additional seven radix products on the already fused action outputs. All unhat conversions, mask products, fixed scalar products and final residual differences remain paid.

| Formal r | ell | lambda | Certificate operations | Polynomial operations | Positive witnesses |
|---:|---:|---:|---:|---:|---:|
| 0 | 62 | 9 | 835 | 903 | 96 |
| 1 | 72 | 7 | 955 | 1023 | 106 |
| 2 | 82 | 8 | 1078 | 1146 | 116 |
| 3 | 92 | 9 | 1201 | 1269 | 126 |
| 4 | 102 | 9 | 1323 | 1391 | 136 |
| 8 | 142 | 10 | 1812 | 1880 | 176 |

Three complete new graphs are saved, for r=0,1,4, totaling 3317 rows. The r=0 graph is identical to its immediate parent, since it has no relator block. Records for r=2,3,8 are count-only consequences of the inherited census and the all-r local delta. No other complete source graph or numerical universal instance is claimed. The all-r proof follows from the explicit uniform stage schedule, not from the finite examples.

## 5. Frozen evidence and retained corrections

The original emitter `positive7_relator_plane_compose_root.py` is 11223 bytes and 221 lines, SHA256 `a78776beff3d9113ef5f8cd1235fb180eedf01c50cde56c24f6bf92f3ef5a90b`. Its first receipt `positive7_relator_plane_compose_root.json` is 438629 bytes and 23214 lines, SHA256 `9992a6d5d81265b701e14d84e9a620ad816ee88dc1eadeb85bc13f6bd986c5c7`. Both are frozen after one original metadata-only emission; neither is to be executed or imported again.

The composer pins the immediate complete parent receipt (`182a9dc7a2efe4428a096263c1872bfbb5df264a79b50851de0b7b7c82b6a4f1`), the original 198-row paired cut (`b830a0644ae0b5ba8b04273a3ac445437af0af2c0b522c1caf3078203f7eab02`) and the full local plane proof (`374736feae3677e61a7e7676847d199956cef7a5664d1f83f5f57dc739ea3819`). It processes row labels, literal operands and graph dependencies only. It does not evaluate arithmetic sources, coefficient arrays, matrix recipes, native witnesses or source degrees.

The [independent complete-source review](review_positive7_relator_plane_compose_riemann.md) binds the full proof and every saved row, including fixed-role preparation, chart permutations, all accumulators, six-exit consumers, native preservation and final ledgers. Local algebra was independently challenged by root, Aristotle and Riemann. The inherited group-universality and native foundations remain dependencies and are not re-proved here.

**Review remark 1 (missing accumulator additions retained).** Root's preliminary alternative count 18M+25A per relator append was wrong: it omitted the three additions into the current d,e,f accumulators. The decoded alternative actually costs 10A for both decoded triples, 18M+12A for their two matrix differences, 3A for the inverse-pair sums and 3A for appending, totaling 18M+28A=46. The new plane schedule includes those appends and costs 40, compared with 48 for the uniform parent. The earlier incorrect append count remains recorded in the local proof and independent review.

**Review remark 2 (rank and support do not give free arithmetic).** A common two-dimensional image alone would not prove the integral coefficient recipe or the 40-operation append. The proof above supplies both and pays reconstruction. Likewise retained selected ports need only contain the nonzero support: a central or identity relator can have zero action while this uniform template still retains all eight raw inputs and its charged zero products. The parent's numbered support correction remains applicable.

**Review remark 3 (unchanged sparse geometry and scoped identity).** The inherited sparse equality Ztot=S remains false, as the a+ all-ones cell retains six rather than seven coordinates; its proven Ztot<=S margin is unchanged. The present same-tuple correspondence concerns only this arithmetic substitution within the sparse wrapper. It does not establish a same-tuple map from the older dense wrapper, and it does not permit arbitrary independent assignments to the old and new fixed coefficient roles.

## 6. Preserved research questions

**Open question 1 (numerical universal instance).** This packet resolves the local plane proof's complete-source composition question. The concrete universal presentation, its relator count and actual fixed coefficient numerals are still unmaterialized. Formula (1), the formal r=0 graph and the finite source examples supply no improved numerical general84 bound, source degree or minimality claim.

**Open question 2 (further coefficient and selection sharing).** The plane reconstruction retains a product by g and two dense eight-term forms. A cheaper fixed chart or a smaller selected-input interface could improve some or all relators, but requires an exact integer recipe, paid runtime operations and all native selection/positivity obligations. In particular the present proof makes no claim that a coordinate permutation can always force g=1. Pascal and Aristotle are separately investigating these possibilities; no further saving is included here.

**Open question 3 (outer compiler).** The earlier hatted global chart, packing and unhat sharing remain separate possibilities. Every current selection field and native lane is retained. Any later reduction must be shown at a complete source cut with its own positive projection or exact polynomial identity, rather than deducted from a rank or interface count alone.
