# Independent audit: paired-sign quartics and the squared-radius improvement

## Verdict and scope

**PASS for the stated local transformation arguments and finite literal certificates, conditional on the incoming literal-source calibration and simultaneous signed-Pell theorems. This is not an independent end-to-end certification of the incoming 517-variable Con(ZFC) claim or the resulting 489-variable Con(ZFC) claim.** The paired endpoint has 493 unrestricted integer unknowns, 310 quadratic residuals, exact degree 4, 7,174 collected monomials and coefficient height 10,945,213. The stronger squared-radius endpoint has **489 unrestricted integer unknowns, 308 quadratic residuals, exact degree 4, 6,905 collected monomials and coefficient height 11,302,118** before any coordinate translation. The smaller variable count costs slightly greater coefficient height; this is not a global optimum claim. Relative to the incoming 517-integer derived-label endpoint, the paired endpoint removes 24 final coordinates and the squared endpoint removes 28. Before projection, pairing saves 36 sign-witness coordinates and 12 rows; the different projection opportunities account for the smaller final-coordinate saving. The square-anchor edit then removes three more guard witnesses and permits one additional coordinate elimination, producing 493 to 489.

The independent checker in this directory imports no producer compiler module. It checks source edits, the exact guard inventory, a fresh pre-power lower-bound DAG, the square budget, the Horn circuit identity with no escaping changed wires, every integral monic projection step, and every collected quartic coefficient. It runs under both ordinary Python and `python -O`; it does not depend on `assert`.

This is an ordinary mathematical audit of the specified local changes plus exact finite algebra replay. It neither re-establishes the complete transitive ordinary source calibration nor supplies a newly completed formal-kernel proof of the calculus/Pell library. These are two different scope limits: the missing full ordinary literal-source calibration cannot be dismissed as only a missing Lean run. The finite checks do not establish unbounded correctness by testing. That correctness is the argument below, composed with the clearly identified incoming theorems. No consistency or inconsistency assumption is used. In particular, a Diophantine reformulation of Con(ZFC) does not prove Con(ZFC).

Input baseline: the frozen round-14 release, especially `direct/derived16_signed_shell/{mixed_source,domain_certificate}.json`, `direct/section.tex`, and `architecture/{FACTORIAL_CARRIER_PROOF,DERIVED_LABEL_RANGE_PROOF,HYBRID_PROOF}.md`. Source index numbers in this report refer to the 550-coordinate, 469-row mixed source before new guard witnesses or Horn rewriting.

## 1. Exact nonnegative representation and pair lemma

For integer a,b,c, put Q(a,b,c)=a²+b²+c(c+1). Every summand is nonnegative: consecutive integers have nonnegative product. Conversely, for every integer n>=0, Legendre's three-square theorem applies to 4n+1, which is odd and congruent to 1 or 5 modulo 8, hence not of the excluded form 4^e(8d+7). In a representation of 4n+1 by three squares, exactly one summand is odd, because the sum is 1 modulo 4. Write the even coordinates 2a,2b and the odd coordinate 2c+1, and divide by 4. This yields n=Q(a,b,c). Thus this is exactly a three-witness nonnegativity guard, constructively realizable by a finite search once n is supplied.

For integers r,s with r+s>=0:

    r>=0 and s>=0  iff  rs>=0  iff  exists a,b,c: rs=Q(a,b,c).

For the reverse implication, a negative r and nonnegative s would give rs<0 unless s=0, in which case r+s<0. If both were negative their sum would be negative. The same argument interchanges r and s. This also treats r=0,s=0 and sum=0 exactly, without a strict-positivity loophole.

The sum premise is indispensable. The tuple (r,s,a,b,c)=(-1,-1,1,0,0) satisfies the product guard while both signs fail. The product premise is also indispensable: (-1,2) has positive sum but one negative coordinate. Neither negative control is asserted to extend to a full source zero.

## 2. The precise guard partition

There are 63 original single guards. Exactly these 12 disjoint pairs, hence 24 original coordinates, are replaced:

| Pair | Source coordinates | Retained sum row | Sum plus one |
|---|---:|---:|---|
| choose0 remainder/rslack | 187,188 | 169 | pow4.output = q^t |
| choose1 remainder/rslack | 194,195 | 174 | pow4.output = q^t |
| range0 remainder/slack | 202,203 | 179 | pow7.output = q^(t+1) |
| range1 remainder/slack | 208,209 | 182 | pow7.output = q^(t+1) |
| range2 remainder/slack | 213,214 | 185 | pow7.output = q^(t+1) |
| range3 remainder/slack | 218,219 | 188 | pow7.output = q^(t+1) |
| range4 remainder/slack | 224,225 | 192 | pow12.output = q^(y+1) |
| range5 remainder/slack | 230,231 | 195 | pow12.output = q^(y+1) |
| range6 remainder/slack | 236,237 | 199 | pow15.output = q^(x+1) |
| range7 remainder/slack | 242,243 | 202 | pow15.output = q^(x+1) |
| range8 remainder/slack | 247,248 | 206 | pow4.output = q^t |
| range9 remainder/slack | 253,254 | 209 | pow7.output = q^(t+1) |

Every sum row is checked literally as output-r-s-1=0, not inferred from its name.

The 493 endpoint retains all other 39 single guards. The 489 endpoint retains 38 and separately removes the proposed factorial F's guard. It recovers F>=1 by a different argument in Section 4, not by pretending F was one of the paired coordinates.

Both variants retain the two factorial ceiling remainders `fact0.remainder` and `fact0.slack`, the two exact-digit output slacks `choose0.oslack` and `choose1.oslack`, the proposed reciprocal product B=`choose1.output`, t0,x, endpoint r0, all encoded representative leaves, the aggregate representative slack, A and Zminus1, q4minus1, every seed index YminusK, and Vquotient_minus1. No sign guard has disappeared by implication from a variable name. The checker verifies the complete list and constructs every emitted guard row independently.

A useful distinction: the two removed `choose*.rslack` coordinates bound digit *remainders*. The retained `choose*.oslack` coordinates bound digit *outputs*. Removing the latter is not this transformation and would destroy the bootstrap used below.

## 3. The pre-power dependency DAG is genuinely noncircular

Write t=t0+16, D=`choose0.output`, V=`pow0.output`, B=`choose1.output`, N=`pow1.output`, q=`mul.400`, F=`fact0.output`, and S=F²=`mul.36`. The 493 source uses rho=Ft², y=F+r0+1, R=2+t+x+y+F. The squared source changes only rows 1,8,11 to

    rho=S t²,     y=S+r0+1,     R=2+t+x+y+S.

The unchanged row 12 states S=F². Thus S>=0 before F has a sign. This is why the squared version can omit F's guard; merely omitting that guard from the old source would not establish the same prerequisites.

The independent lower-bound engine starts from the retained single signs and the proved square-budget value W>=2 only. It uses exact monic row rearrangements with nonnegative monomials, treating even powers as nonnegative even when the underlying variable is still signed. It does **not** use any of the 12 product guards, any sign of their 24 coordinates, any power-output interpretation, or F>=0 in the squared variant. Its emitted DAG establishes:

- t>=16, x>=0, S>=0, rho>=0, y>=1, R>=19;
- all 19 requested exponents are positive, including the large derived-label constructor exponent J, whose nonnegative gate DAG is evaluated compositionally rather than expanded;
- every guarded seed relation Y_i=k_i+e_i has Y_i>=1;
- the unchanged product V_aux=(product_i Y_i)²(v+1) is strictly positive;
- the comparison base 4 V_aux(q4minus1+1)+1 is at least 5.

The square budget is verified as W=2+sum a² over the actual base, exponent, and output atoms of all 19 power requests. It supplies |a|<W without presupposing any output's sign. The common norm with A,Zminus1>=0 supplies the usual A>=(W+1)^W>=2. Since V_aux is a positive integer, U²-(A²-1)V_aux²=1 gives U²>=A²>=4. Consequently the inherited signed indexed-Pell theorem has its required |U|>=2 premise without a new nonzero guard.

The recorded independent DAG has 208 steps for the original-radius variant and 192 for the squared-radius variant. It derives none of the 24 removed signs. It does not derive the omitted F sign in the squared variant. This is a dependency audit, not a claim that F is semantically negative or that no other proof of a sign exists.

The old baseline positivity certificate contains an F>=0 leaf and must not be copied as the new squared-radius justification. This audit replaces it with a fresh literal-row certificate.

## 4. Power orientation before restoring any paired sign

The crucial retained raw equations are:

    D=u+v+1,          q=D+o+1,
    DF=V+v,

where u=`fact0.remainder`, v=`fact0.slack`, o=`choose0.oslack` are all still nonnegative. Hence D>=1 and q>=2 before interpreting *any* binomial or power. The identities follow from rows 2,3,4,170 and ordinary gate definitions. In particular, they do not use `choose0.remainder` or `choose0.rslack`.

Recall the inherited signed-power lemma in the square budget. For positive base n and exponent k with n,k<W and |m|<W, the indexed-Pell system gives either the true value m=n^k with the positive principal abscissa, or the only possible opposite-orientation case n=1,m=-1. Its proof uses T_n=2An-n²-1>W^W+W and the conjugate identity: a negative abscissa gives m n^k congruent to -1 modulo T_n, while |m n^k+1|<T_n. Thus m n^k=-1, forcing n=1,m=-1. For a positive abscissa, m congruent to n^k and the strict bound give equality. A request with base at least 2 therefore orients every request sharing that index pair.

Apply this in the following order:

1. The retained q^t request, with q>=2 and t>=16, orients the t pair. The shared request (rho+1)^t therefore has V=(rho+1)^t>=1 even if rho initially vanishes.
2. D>=1 and DF=V+v now force **F>=1**, in both variants. Therefore rho>=t², and V>=2. This is the first use of a positive F in the squared construction.
3. The unchanged reciprocal index equation is C+F²+1=B i_q, with C>=1 and B>=0 retained. Its strictly positive left side forces B>=1. K=2R is already positive.
4. The B^K request yields N=B^K>=1, except possibly the case B=1,N=-1. In either case N+V+1>=2. The second K-indexed request, at this base, orients that shared pair and excludes the exceptional case. Thus N=B^K>0 and q=N(N+V+1)^K has its true positive value.
5. Every other seed has a request at q or q+1, both at least 2. The t+1 pair is the unchanged addition of the now-positive t pair and the unit pair. All 19 powers are consequently recovered with their intended positive values.
6. Only **now** read the 12 retained sum rows. Their right sides are q^k-1>=0 with positive k. Each product guard therefore restores both original signs by Section 1.

This breaks the feared circle: the digit remainder signs do not establish q positivity, seed positivity, or Pell orientation. Those are established first by other retained rows. The product guards are consumed only afterward. The finite negative controls remove each of u,v,o in turn from the presemantic seed set and confirm that the above q>=2 derivation is then unavailable.

## 5. Squared-radius factorial theorem, with both implications

The squared source changes arithmetic meaning and is not an affine coordinate change of the 493 source. A new source-level argument is required.

The following wider-radius lemma suffices. Let n>=1, let f be an integer, and let rho be a nonnegative integer. Put V=(rho+1)^n and D=binom(rho+n,n). Suppose u,v>=0 satisfy

    V+D=Df+u+1,         D=u+v+1.

These equations first imply D>=1 and Df=V+v>=1, hence f>=1. Assume now rho>=f n². Then f=n!. Conversely, if f=n! and rho>=f n², the two required natural witnesses exist.

Proof: the rows are exactly f-1<V/D<=f. Put G=n!. For z_i=(i-1)/(rho+i),

    V/D=G product_(i=1)^n (1-z_i),
    sum z_i <= n(n-1)/(2rho) <= (n-1)/(2fn) < 1/(2f).

For n=1 the sum is zero and the final strict inequality is still valid. Every factor lies in (0,1]. The elementary product bound therefore gives

    G(1-1/(2f)) < V/D <= G.

The ceiling upper bound gives f<=G. The lower bound together with V/D<=f gives

    G < 2f²/(2f-1) = f+f/(2f-1) <= f+1.

Integrality gives G<=f, hence equality. Conversely take f=G. The same bound gives G-1/2<V/D<=G. Define u=V+D-DG-1 and v=DG-V. Both are nonnegative integers, and direct substitution verifies both rows.

For rho=F²t², Section 4 has already established F>=1 before the exact digit is interpreted. Hence rho>=Ft², precisely the hypothesis needed here. There is no signed-radius loophole and no circular premise F=t!.

The exact-binomial bootstrap also survives:

- rho>=t, so all coefficients binom(rho+t,j), j<=t, are at most binom(rho+t,t)<=V.
- From the true radix, q>V^K>=V², so the first exact digit correctly determines D, then the wider-radius lemma gives F=t!.
- F²+t <= (Ft²+1)² <= (rho+1)². Thus all coefficients through index t in the second exact digit are <=(F²+t)^t<=V²<q. It determines B=binom(F²+t,t) exactly.
- Only after that recovery use the unchanged reciprocal product theorem B>=2 and N>=2^K.

The finite regression independently checks 4,737 signed proposed-factorial cases, including f<=0, neighboring values around the true factorial, and explicit constructive witnesses for n=1,...,9. These are useful controls only; the proof above is unbounded.

## 6. All remaining source obligations survive the stronger carrier

After F=t!>=1, the modified endpoint gives y=F²+r0+1>=F+1. Thus every old use of y>F remains valid. The start accumulator weight remains F+1, not F²+1: row 7 and the logical local polynomial are unchanged.

For the same t,x,y,F, R_new=2+t+x+y+F² is at least R_old=2+t+x+y+F. Therefore every old majorant proof that bounded the local polynomial and J by R_old^E also bounds them by R_new^E. The factorial floor R_new>=F>=16! still gives R_new^E<2^R_new<2^K. The derived-digit inequality 3 ell(t+1)<=2F<2R_new=K still holds. Ordinary range indices remain <=R_new-1. The aggregate bound is unchanged and still excludes J(A), exactly as required by the incoming derived-range proof. Consequently the ordinary and derived carry bounds, precision-2K CRT lift, reciprocal-modulus decoding, pairwise-coprime label weights, and Horn-flow extraction all remain valid.

Constructive completeness has no new bound-dependent horizon circle. Start with a finite calibrated refutation and choose t>=16 beyond the finite proof-tree length, every row parameter, and every relevant derived label sum, exactly as before, **before** choosing F or any accumulator encoding. Then put F=t!, form the pending-multiset accumulator path, and pad with truth steps. Choose y to be a sufficiently large positive multiple of t!, exceeding all needed accumulator sizes and F². Such multiples always exist. Ordinary beta CRT then supplies x. Set r0=y-F²-1>=0 and use the unchanged endpoint quotient equations. Define R_new,K, the reciprocal product B, and the precision-2K representatives only after these choices. The stronger R is permitted in the CRT completeness proof. Define rho=F²t²,V,N,q and the exact/fused digit witnesses; the wider-radius factorial lemma supplies its u,v. Finally choose the shared Pell witnesses and all single/product guard witnesses. No step feeds a required larger bound backward into the already chosen finite horizon.

## 7. Complete constructive maps and compiler semantics

### 7.1 Paired 493 source versus incoming guarded source

Forward from an incoming guarded source zero: keep its 550 source coordinates and all surviving single-guard witnesses. Each of the 12 original pairs is nonnegative, so enumerate a representation of its nonnegative product by Q. Add those 36 witnesses and discard the old 72 witnesses. This produces the paired source zero.

Backward from a paired source zero: Sections 3-4 recover every removed sign, without assuming them initially. For each removed individual coordinate enumerate a representation by Q. Reinsert those 72 original witnesses and discard the 36 product witnesses. This is an incoming guarded source zero. Thus the 493 change preserves zero existence over the same source-coordinate projection, although its nonnegative witnesses are not a bijective encoding.

### 7.2 Squared 489 source versus the calibrated refutation relation

Soundness: a 489 polynomial zero lifts through the exact compiler to the squared paired source. Sections 3-5 recover all signs, powers, factorial and reciprocal arithmetic. Section 6 then permits the existing CRT decoding and Horn-flow extraction of a finite calibrated refutation.

Completeness: a finite calibrated refutation is re-encoded by the explicit procedure in Section 6, then furnished with Q witnesses and projected to a 489 zero. Combined with the incoming source theorem this proves equality of existential zero statements with the original endpoint. It does **not** claim that changing three coordinates of an arbitrary incoming numerical zero is enough, that the original x,y,t are preserved, or that the new source is a bijective reparameterization of the old source. If a direct old-zero/new-zero conversion is desired, first extract its finite refutation and then perform the constructive re-encoding. The reverse uses the same extraction/re-encoding through the common relation.

### 7.3 Horn factorization, without relying on names or numerical samples

The checker verifies all 17 declared affine square roots and the complete 11-link product chain. The changed ordinary factors and intermediate products occur nowhere outside the audited network. Writing its 11 ordinary/inference balances as L_i and its nonnegative bundle as B0²+G², the exact identity is

    (product_i L_i²)(B0²+G²) = (product_i L_i)²(B0²+G²).

The bundle is also preserved because ((c-a)²(c-b)²-D0²)²=(((c-a)(c-b))²-D0²)². No final square is omitted, and the beta squares outside the Horn product remain outside it. The independent checker reconstructs all 18 row rewrites, the new output interface, both deleted rows, and the no-escape conditions.

Given the old zero, define each new signed factor by its affine root, multiply the signed factors in their chain, square the final product, and define the new external Horn value. Given a new zero, restore every old factor as its corresponding square and every old product by its old multiplication chain; restore the discarded bundle squares from their affine roots. The external Horn value agrees by the identities above. Since protected internal wires have no other uses, every untouched equation remains satisfied. This is a complete existential equivalence over integers, without any sign premise on the new intermediate factors.

### 7.4 Integral monic projection and one polynomial

Each recorded elimination is checked as a current row z-f=0 or its negative, with integral coefficients, no self-dependency, and only still-live dependencies. Substitution into every remaining row is performed afresh; the result is checked to retain degree <=2. The 493 endpoint has 209 such eliminations, the 489 endpoint 210. Both remove two final unconstrained coordinates, indices 136 and 138 in the factored source.

A source zero maps forward by keeping the retained coordinates. An endpoint zero maps backward by setting the unconstrained coordinates to zero, undoing the retained-coordinate renumbering, and evaluating the recorded restorations in reverse order. Every restored coordinate is integral and every removed equation holds. Unconstrained coordinates are irrelevant, not uniquely determined; only the monically defined coordinates have a unique lift conditional on the retained/free choices.

Over integers, sum_j R_j²=0 holds exactly when every residual vanishes. The checker independently multiplies and collects every row square and compares the complete sparse polynomial coefficient list, with no modular arithmetic or probabilistic equality test. The degree is exactly four, not merely at most four. The final equation therefore has no external inequalities, variable exponents, deferred ports, or hidden sign conditions.

## 8. Adversarial checks and release notes

`check_negative_controls.py` rejects a product-guard sign change, wrong sum output, missing retained bootstrap guard, corrupted monic restoration, altered expanded coefficient, and corrupted declared affine square root. It separately checks that deleting each of the three essential bootstrap signs destroys the advertised pre-power q>=2 lower-bound derivation. It also checks 1,681 bounded pair-sign fixtures and Q coverage of 0,...,256, while clearly separating these tests from the unbounded proof.

A minor metadata defect was found and repaired: the emitted equation named `terminal_elimination_certificate.json` while initially only `projection_certificate.json` existed. The producer now supplies the exact alias; the independent checker verifies both its existence and equality to the actual projection certificate. The polynomial and its equation hash did not change. The fresh producer presemantic certificates have also been independently checked, including every ordered dependency and all 16 seed indices. The audit additionally rejects deleting F's guard without making the three square-anchor source edits.

No endpoint is preferred merely by its producer's claimed count. The independently certified uncentered 489 endpoint is the stronger variable-count result; the 493 endpoint remains a conservative exact-source-projection fallback. Both remain ordinary-proof endpoints inheriting the calibrated calculus and signed-Pell bridge, with the full transitive formalization explicitly outside this audit's claim.


## 9. Late upstream overlap and exact attribution

A late upstream review at commit `59ee8f21244635b42f706a74c4e9631226dd1f7c` explicitly accepts the same general product-sign principle and the same three-witness nonnegative representation. Its source is [Root acceptance of six anchored product guards](https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/59ee8f21244635b42f706a74c4e9631226dd1f7c/Computability/DiophantineConsistency/reviews/shared-remainder-product-guards-root-peer.md). The retrieved review's SHA-256 is `a873ebd46ad8662f421fa5c864c9a7aa3a00e649cbdb310c78e510ce40f713c3`; a verbatim attribution copy is included here.

That review materializes six fixed replacements in a different unprojected parent: 1,436 integer coordinates and 1,242 residuals. Retained nonnegative anchor pairs establish the new pair sums before invoking the inherited source proof. It explicitly says that projected quartic measurements remain to be made in a separate packet. The general paired-product guard must therefore **not** be represented as an original or priority result of this iteration.

The specific contribution checked here is a different completed application: twelve listed remainder/slack pairs in the 550-coordinate derived-label source, their nonnegative sums justified only after the independently verified signed-power orientation, the exact projected 493-coordinate coefficient list, and the separately proved square-anchored 489-coordinate endpoint. These statements describe concrete checked artifacts and proof dependencies, not worldwide novelty. The overlap does not alter any finite replay or mathematical conclusion above, and this audit does not establish that no other source has already developed the same further application.


## 10. Exact inherited-reading ledger and calibration boundary

The late upstream `TRIAGE.md` correctly notes that the incoming 517-variable architecture changes the native proof-label weights and bounded-universal elimination. Its interpretation cannot follow just from the projection inverse certificates. This independent audit does not claim otherwise. Upstream's decision to reserve acceptance for a later full review is not evidence of a mathematical counterexample.

### Proof texts actually read

The following round-14 proof texts were read completely by this reviewer, including the final scope-check pass:

- `architecture/FACTORIAL_CARRIER_PROOF.md`, 242 lines: factorial label weights, pairwise-coprime separation, unordered Horn-flow soundness, finite proof-tree/padding completeness, carrier/CRT assembly, and horizon-16 note.
- `architecture/DERIVED_LABEL_RANGE_PROOF.md`, 139 lines: derived-polynomial range theorem, the local label expression J, horizon-16 amplification, separate carry bounds excluding J from the aggregate, and both semantic directions.
- `architecture/HYBRID_PROOF.md`, 242 lines: reciprocal moduli, one-sided prime-power binomial range decoding, the precision-2K bounded-universal CRT theorem, amplification, factorial/radix chronology, and constructive arithmetic completeness.
- `direct/section.tex`, 258 lines: signed square-budget and power orientation, presemantic seed positivity, Horn factorization, monic projection, and the separate derived-label 517 variant.

The full self-bounding factorial proof and digit/radix proof in `architecture/section.tex`, lines 241-390, were also read. `architecture/build_derived_label_range.py` was read, including its `source_and_labels` constructor, but this is not a claim that all of its transitive imported constructors, numerical source data and compilers were independently rederived or replayed. Earlier reads of the factorial-carrier text concentrated on its later soundness/completeness and arithmetic sections; the final scope pass completed the earlier label and native-rule-interface sections. The final ledger above records what has now actually been read, not what was complete at the first progress update.

### What this ordinary mathematical review covers

At the stated abstract rule interface, the factorial-weight argument is valid: all relevant positive labels lie in [1,t], the weights 1+j t! are pairwise coprime, the beta remainders telescope, positive accumulators permit cancellation, and valuation balances force falsity into the finite rule closure even when the supplied rule multiset has cycles. The reverse proof chooses the finite horizon before weights and accumulator encodings and then constructs a padded proof-tree flow. The reciprocal-modulus, precision-2K CRT and derived-range arguments were also checked as ordinary mathematical arguments. No defect was identified in these arguments.

The audit checks that the new square-anchor changes satisfy the hypotheses used by those arguments, and proves the wider-radius factorial lemma independently. It checks the new literal source edits and all downstream finite algebra exactly. Thus the component conclusions are stronger than a numerical census or a successful call to a producer verifier.

### Substantive imported dependencies, not discharged by this audit

1. **The exact native rule interface.** The concrete square-shell formula/variable constructors and the bundled side-condition must represent exactly the intended C222 axiom/schema and inference instances, with the stated truth/falsity codes and all recoding positions correct. This audit reads the abstract source proof and the top-level local constructor, but does not independently re-establish the entire concrete syntax/schema calibration.
2. **The literal binding of that interface and its bounds.** The full raw circuit must emit exactly the specified local polynomial L and label sum J, its two majorant certificates must bound those exact polynomials, and the incoming raw-to-mixed transformations must bind them to the frozen 550-coordinate mixed source. This audit pins the inherited mixed source and domain certificate and verifies the new edits after that boundary. It does not turn the inherited hashes, compiler receipts, or new projection inverses into a fresh proof of the complete earlier binding.
3. **The complete simultaneous indexed-Pell theorem.** The signed indexed-Pell classification and its simultaneous completeness construction are imported from the incoming source. This audit checks the relevant sign/orientation chronology and square-budget estimates, but does not reprove the full indexed-Pell divisibility/congruence theorem or its entire literal graph implementation from first principles.
4. **The C222-to-ZF/ZFC bridge.** The claimed equivalence uses `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`, together with their transitive source interpretation. No new complete ordinary recalibration or end-to-end kernel execution of this bridge is claimed here.

A false theorem or mismatched literal binding in any of these dependencies could invalidate the claimed Con(ZFC) interpretation while leaving all new quartic coefficients, paired-guard calculations and projection inverses correct. This is an explicit dependency risk, **not a discovered defect**. In particular, this audit's finite PASS cannot be cited as independent approval of the entire incoming 517-variable calibration. The safe conclusion is: the 493 and 489 local transformations and their measured polynomials pass this component audit, and their Con(ZFC) interpretation is conditional on the identified inherited ordinary source/Pell/calculus theorems.
