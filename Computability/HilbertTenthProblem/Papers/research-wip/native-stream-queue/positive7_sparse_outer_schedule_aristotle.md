# Independent projection and all-r ledger for the sparse positive7 compiler

The sparse one-AND history wrapper preserves the ordinary-input projection and has the proposed complete schedule. With r>=0 fixed presentation relators, put m=8+2r, w=52+8r, ell=m+w+2=62+10r, and lambda=floor(log2 ell)+popcount(ell)-1. The certificate costs

    (420+56r+lambda)M + (550+74r)A,

with23 comparisons and96+10r strictly positive existential coordinates. One combined sum-of-squares finalizer adds23M+45A, giving

    (443+56r+lambda)M + (595+74r)A
      =1038+130r+lambda operations.                         (1)

This note derives the positive projection and every all-r stage independently of the emitted source. The fixed universal presentation remains unmaterialized: r is not numerically known for that presentation, and r=0 is only a formal source shape. Equation(1) is not a new numerical universal bound. Complete literal-source certification is a separate companion task; no saved source is evaluated here.

## 1. Fixed compiler data and supplied domains

The raw alphabet has eight paired slots a+/a-, b+/b-, z1+/z1-, z2+/z2-, and one relator/inverse pair for each of r fixed words. Retain the accepted signed6 representation A_sigma and unimodular Q from the weighted positive7 construction. Write

    h=(1,1,1,1,1,2)^T, k=(h,1)^T,
    D0=[I6|-h], E=[I6;0], F=8E-k*1_6^T,
    G_sigma=Q A_sigma Q^-1,
    L_sigma=kappa*k*1_7^T+F G_sigma D0.                     (2)

Here D0 is the fixed decoder, distinct from the variable height D below. Choose one power of two kappa>28 max_(sigma,i) sum_j |G_sigma,ij|. The actual paired alphabet is nonzero, so this gives kappa>1; the more general zero-family convention in the predecessor is not needed. Every L_sigma is a strictly positive integer matrix with common column sum C=8kappa. Choose a fixed power of two K>max(C,m).

The signed relator coefficient roles are not independent witnesses. For a relator slot, its three-by-four table is the exact substitution of the rows of S(rho(R_j))-I3, or of the inverse word's matrix, into the last-block decoder. Explicitly a row (u,v,t) becomes

    (u+v+2t, v, t, -u-2v-4t)                              (3)

on selected coordinates4,5,6,7. The paired tables are the fixed174 nonzero coefficient terms of the paid sparse-action dependency. The uniform schedule keeps all24r relator products, including products by zero. Arbitrary independent assignments to these roles, or a kappa inconsistent with(2), are outside the compiler recipe.

The role kappa_minus_one denotes the compile-time integer kappa-1. This fixed numeral can be prepared with the rest of the fixed alphabet; its product with the variable history sum is paid. No runtime subtraction from a supplied kappa port is suppressed, since there is no such port. Signed fixed coefficients and signed computed increments are permitted by ordinary integer polynomial arithmetic. Only the existential coordinates and ordinary input are required positive. In particular a signed coefficient is not a negative existential witness.

For the inherited universal application alpha=12*2^(p+1) and gamma=12*2^p+1 are fixed by the program. Ordinary x>0 alone varies as relation input. Compute tau=alpha*x+gamma and tau2=tau*tau and use

    z=(3,tau,tau2,2,tau,tau2,1), S0=2tau2+2tau+6.           (4)

The alphabet, its relator list, kappa and K are fixed independently of x and p. The effective external group/universality theorem remains inherited; this note does not instantiate or re-audit it.

Supply seven positive history words, six positive terminals F1,...,F6 with F7 defined as a copy of F1, m positive selector hats, w positive retained selected-source hats, height/global slacks, and21 fresh positive native auxiliaries. Every native coordinate is separately prefixed; none is shared with these outer words. The witness count is

    7+6+m+w+2+21=m+w+36=96+10r.                            (5)

Terminal sharing is the already proved positive coordinate bijection within a fixed wrapper: restore F7=F1, or drop that equal copy. It removes the endpoint comparison and permits reuse of P*F1 in recurrences1 and7.

## 2. Geometry and retained selection before history recovery

Unhat selectors S_sigma=Shat_sigma-1 and retained products Z_sigma,i=Zhat_sigma,i-1. The retained coordinates are six for each a and b slot, seven for each z slot, and four for each relator slot, totaling w. Compute

    J=sum_sigma S_sigma, D=S0+height_slack, B=KD,
    P=(B-1)J+1, S=sum_i H_i,
    Ztot=sum_retained Z_sigma,i, mu=(D-1)J,
    S+Ztot+global_slack=P.                                 (6)

The correct hatted form of the last equation has P+w on its right. All unhatted fields are nonnegative on every positive supplied assignment, J>=0 and P>=1. On a full zero, the global equality forces J>=1 and hence B<=P. It also bounds every H_i and retained Z_sigma,i strictly below P. As S_sigma<=J, each mask (B-1)S_sigma<=P-1; D<P and mu<P follow from B=KD with K>=2 and J>=1.

Pack exactly m Boolean lanes (S_sigma,J,S_sigma), w retained-selection lanes (H_i,(B-1)S_sigma,Z_sigma,i), one aggregate lane (S,mu,S), and one height-power lane (D,D-1,0), at radix P. Their number is ell=m+w+2. Prescribe the native scale T_native=P^ell by a paid fixed-exponent chain. The raw packs are nonnegative on the entire supplied positive domain. Compose the same native header as in the dense compiler:

    q=16*T_native,
    padded_A=16*A_pack+12,
    padded_B=16*M_pack+10,
    F3=16*Z_pack+8.                                         (7)

These are exactly the former positive parameter hats A_pack+1,M_pack+1,Z_pack+1 composed with their private padding exits. All64 certificate rows,15 comparisons and21 auxiliary witnesses are retained. This equality at the padded exits is unconditional polynomial algebra; it does not assume typed selectors.

The prescribed native theorem now gives dyadic P. Its height lane forces D dyadic, so B is dyadic. Repunit divisibility P-1=(B-1)J then gives P=B^n for some n>=1 and J=sum_(j=0..n-1) B^j. The Boolean selector lanes and m<B force exactly one selected label per cell: their sum J has no possible base-B carry because each cell sum is at most m. The retained-selection lanes recover exactly the corresponding canonical coordinate products. These steps use the global bound and native equations only, before any signed increment or recurrence is interpreted.

## 3. Virtual omitted selections and the exact positive update

Write H_i=sum_j h_i(j)B^j with 0<=h_i(j)<B, and let e_sigma(j) be the one-hot selector bits just recovered. For purposes of the proof, define for every label and every coordinate

    Ztilde_sigma,i=sum_j e_sigma(j)h_i(j)B^j.               (8)

No new witness, source operation or native lane computes(8). For retained coordinates it equals the certified supplied Z_sigma,i. The complete virtual family partitions each history word: sum_sigma Ztilde_sigma,i=H_i as an exact integer identity.

The action structure dependency proves that every omitted selected coordinate has zero coefficient in the full original-coordinate difference (A_sigma-I6)Q^-1D0, including its later rank-one correction. Thus the six increment sums (a,b,c,d,e,f) computed solely from retained words equal

    sum_sigma (A_sigma-I6)Q^-1 D0 Ztilde_sigma.

Using(2) and the exact partition identity, the actual selected packed action equals

    V=8H+(kappa-1)k*S+FQ(a,b,c,d,e,f)^T.                   (9)

This is also sum_sigma L_sigma Ztilde_sigma. The common baseline is paid from the supplied H and its paid sum S; omitted words are not secretly supplied as free runtime products. The identity interprets the arithmetic after exact selection, not arbitrary untyped selected fields.

The paid sparse-action postprocessor realizes all seven entries of(9). Its fused version realizes B times each entry by unconditional integer-polynomial identities. In particular its outputs have the form sum_j B^j (B L_sigma(j)h(j)) even before the individual history digits have been proved genuine. Signed increments and cancellations therefore do not invalidate nonnegativity of the actual matrices used in the next step. The fused outputs have no other unscaled consumer in this schedule.

Enforce all seven recurrence comparisons

    B V_i=H_i+P F_i-z_i, i=1,...,7.                        (10)

The aggregate lane, initial mass S0<D and K>C put these equalities within the inherited simultaneous nonnegative-history induction. Once earlier digits are recovered, the next actual total is at most C(D-1)<KD=B. Hence every next coordinate is in[0,B), the recurrences recover its canonical digit, no carry enters the aggregate sum, and the aggregate mask forces that total below D. The initial step is supplied by z and S0<D; the top coefficient determines the positive terminal. This proves the exact genuine trajectory and its equality F1=F7.

For completeness, choose a power of two D above every mass in a finite accepted trajectory, with height_slack=D-S0>0. Use its genuine histories, one-hot selectors and retained coordinate products. Since the retained set at a cell is a subset of seven nonnegative coordinates,

    0<=Ztot<=S,
    S<= (D-1)J,
    global_slack=P-S-Ztot >= P-2S
      >=((K-2)D+1)J+1>0.                                  (11)

The packed inequality Ztot<=S follows directly from the nonnegative weighted cell sums, without assuming the selected sum itself has no carries. All histories and terminals are positive because the initial vector and every actual matrix are strictly positive. Zero retained selections have positive hat1. The complete native converse supplies fresh positive auxiliary witnesses at the new packs and scale.

Thus this sparse finite positive relation has exactly the nonempty accepted-word projection on ordinary x. The inherited initial vector has coordinates1 and7 equal to3 and1, so no accepting empty word is lost. The word length n is unbounded and reconstructed from the repunit; ell and r remain fixed compiler parameters.

**Review remark 1 (the dense mass identity is false here).** The tempting assertion Ztot=S is false. At a cell labelled a+ with seven coordinates equal to1, coordinate1 is omitted: retained mass is6 and full mass7. This is a local selector-interface counterexample, not an asserted universal input. Equation(11), not equality, is what the sparse global margin needs.

**Review remark 2 (projection is not a dense/sparse witness bijection).** Changing the selected coordinates changes the packs and prescribed scale. Extending a sparse accepted word to a dense certificate can require fresh native auxiliary witnesses and a different positive global slack. The result proved here is equality of ordinary-input/accepted-word projections. Only terminal aliasing within either fixed construction is asserted to be the simple supplied-coordinate bijection described above.

## 4. Independently derived paid stages

All fixed-coefficient products are charged, including zero products in the uniform relator template. At general m,w the outer prefix has (m+5) multiplications and (2m+2w+14) additions/subtractions. Its complete breakdown is:

| Stage | M | A |
|---|---:|---:|
| Input tau,tau2 |2|1|
| Initial mass S0 |0|3|
| D=S0+height_slack |0|1|
| B=KD |1|0|
| m selector unhats and checksum J |0|2m-1|
| w selected-source unhats and their total |0|2w-1|
| B-1, its product with J, and P |1|2|
| D-1 and mu |1|1|
| S=sum seven H_i |0|6|
| Global comparison left side |0|2|
| m reused selection masks |m|0|
| Prefix total |m+5|2m+2w+14|

At m=8+2r,w=52+8r this is (13+2r)M+(134+20r)A. The sum S is paid once and reused by the global bound, aggregate lane and common-baseline action.

The A and M packs use ell-1 Horner multiplications/additions each. Z has the literal zero in its highest height-power lane and uses ell-2 of each, starting at S. Total packing cost is

    (3ell-4)M+(3ell-4)A=(182+30r)M+(182+30r)A.              (12)

No other symbolically nonzero top coefficient is dropped. The fixed binary power chain for P^ell costs lambda multiplications. The native certificate costs33M+31A after the already justified header composition; its old44-row standalone SOS is not retained in the combined finalizer.

The six nonempty paired increment sums have174 fixed products and168 additions. The uniform relator template adds24r of each. The fused common-baseline postprocessor adds12M+21A, so its seven already scaled recurrence left outputs cost

    (186+24r)M+(189+24r)A.                                 (13)

The174 paired census and coefficient identities are inherited from the full paid sparse-action table and its separate root verification; no saved coefficient table was evaluated here. The nonempty paired contribution in every row persists at r=0, so no empty-sum convention or negative addition count is used.

Only the recurrence right sides remain to be paid after(13). Six distinct P*F_i products supply all seven terminals because F7=F1. Each right side uses one addition and one subtraction. Thus the remaining recurrence cost is6M+14A, with no additional seven B-products. Counting them again would miss the adopted consumer fusion.

Putting the disjoint stages together gives

| Stage | M | A |
|---|---:|---:|
| Complete outer prefix |13+2r|134+20r|
| Three packs |182+30r|182+30r|
| Fixed native scale power |lambda|0|
| Native certificate |33|31|
| Fused sparse selected action |186+24r|189+24r|
| Seven recurrence right sides |6|14|
| Total certificate |420+56r+lambda|550+74r|

The global comparison, native15 and seven recurrences total23. Forming their23 residual differences,23 squares and22 accumulation additions costs23M+45A, proving(1). No residual subtraction is hidden in a free comparison. Copies and the terminal alias are the only zero-cost data movements.

## 5. Formal boundary r=0 and exact scope

At r=0 the grammar has m=8,w=52,ell=62 and lambda=9. The certificate therefore has979 operations, the full polynomial1047, and96 positive witnesses. These are formal schedule parameters using the eight paired slots. No theorem says those slots with no relators implement the inherited universal language; substituting r=0 into a symbolic universal-family formula does not instantiate the unknown universal presentation.

**Open question 1 (retained source-audit boundary and numerical instantiation).** The preliminary draft recorded: "Root is emitting the complete sparse wrapper. Its literal bindings, every changed pack consumer, fixed coefficient-role recipe, topology, liveness and finalizer require independent source authentication." Root has since frozen the emitter and receipt identified below. The independent whole-source companion will bind this proof; the present all-r ledger and positive projection do not substitute for that source audit. The numerical universal relator list, r and lift constants remain unmaterialized; no improved numerical general84 bound or formal degree claim follows. Any later pruning or packed-hat optimization needs its own complete source accounting.

## 6. Bindings and review scope

The full frozen sparse emitter was read as inert text, including its retained-port grammar, literal paired-table binding, relator-role loops, native header, fused outputs, terminal-product sharing and finalizer. Its receipt's input pins, fixed-data recipe, six shape-census records and execution limits were read; the lengths of its three examples were inspected as metadata. The all-r formulas above were independently derived before this read and agree with those records. Full per-row certification of the three saved graphs remains the separate companion's scope.

| Frozen context artifact | SHA256 |
|---|---|
| positive7_complete_sparse_compiler_root.py | 923283521c4d15d717424196802564b02d3efd845b8de474370ae01660d6f9e9 |
| positive7_complete_sparse_compiler_root.json | 2c7e2b2d2345150644b47701eed9434eabad7159f0067154b6666750e2b48e3a |

The root primary proof is forthcoming and is not claimed as read or bound here. This independent derivation freezes first, so the subsequent primary/source review may bind it without a circular dependency. Riemann has fully challenged the present proof and ledgers, including virtual omissions, the fixed numeral recipe and the r=0 boundary, with no correction requested.

The current review reads the full paid sparse-action proof, its selected-action structural predecessor and the prior weighted7 and one-AND interfaces. The sparse action's finite coefficient verification is inherited with its exact source pins, not scientifically replayed. All new algebra is a handwritten proof, and only fresh byte/metadata processing is permitted. No supplied, archived, committed, predecessor or frozen program is executed or imported; no source or coefficient array is evaluated, no degree is propagated, and no build or repository/Git mutation is performed.
