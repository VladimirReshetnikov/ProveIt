# A normalized presentation grammar for the closed Higman expression

Under the attributed group-theoretic premises below, this note gives explicit finite presentation and subgroup-word recurrences for every primitive used by the committed unary recognizer and its commutator-pattern substitution. The next step can be literal, namespaced expansion of that fixed expression tree. No new recognition construction or existential choice of a benign pair is needed at that step. Several final displays and count simplifications in the primary source cannot be copied literally; the normalized recipes below follow their preceding free constructions and retain the discrepancies in numbered remarks.

The group-theoretic premise is Mikaelian's star-construction identities and the operation-specific subgroup identifications in Sections 5--6 of [arXiv:2507.04347v8](https://arxiv.org/pdf/2507.04347v8). I read those sections, checked the presentation syntax and counts below, and checked the stated local corrections by hand. This is not an independent audit of all the imported normal-form lemmas or the full Higman embedding theorem. In particular, the operation-to-subgroup identifications remain attributed premises; the word-list/count compiler is explicit conditional on them. The omega construction is used only with its needed zero-block hypothesis, which is proved for all three block relations in our actual expression.

## 1. Representation and elementary presentation operations

A presentation object is an ordered generator list X, an ordered relator list R, three distinguished generators a,b,c, and an ordered list L of subgroup words. It asserts that F=<a,b,c> embeds in K=<X|R> and F intersect <L> is A_E=<a_f:f in E>, where b_i=c^(-i)bc^i, b_f is the increasing-index product of b_i^f(i), and a_f=b_f^(-1)ab_f. Write (g,r,l)=(|X|,|R|,|L|). These are literal syntactic sizes, not group ranks, minimal presentations, or arithmetic-circuit counts. All private names are fresh for every occurrence in the expanded expression tree. A bar means a complete bijective renaming of generators, relators and subgroup words. Powers and conjugates are finite group words; x^v means v^(-1)xv.

The following are explicit string operations, with no group word-problem oracle:

* `fix(t;W)` appends one fresh generator t and the |W| relators t^(-1)wtw^(-1), one for each listed word w. Fixing a list fixes its generated subgroup. A repeated word need not be listed twice.
* `map(t;U -> V)` appends t and one relator t^(-1)u_i t v_i^(-1) for each matched pair. Injectivity/isomorphism of the associated subgroups is a mathematical premise checked in the corresponding source construction, not inferred from the strings.
* Amalgamation along a named free factor identifies its marker names, concatenates all other generator names, and retains both relator lists. A product of disjoint presentations retains their relators and adds one commutator for every pair of generators from the two lists.
* For a subgroup-word list W, `W^v` is the list of conjugate words. At every finite-base step below, `X_B` means the distinct declared generator names of that base B, each once. Identifying the common a,b,c is done before taking such a list.

The source's Section 6.4.1 describes the optional initial normalization for a presentation supplied with a,b,c only as words: three new names and three defining relations. Our two bases and every recipe already have the markers as names, so this extra normalization is not charged repeatedly. The three output embedding words are always the literal a,b,c.

A common extraction operation will be useful. Suppose Q is benign in Fbar x F inside a given presentation K_Q, with subgroup list L_Q, and Q is the graph subgroup described in the relevant primary proof. Append

    fix(w1; abar,bbar,cbar),  fix(w2; L_Q),
    fix(w3; a,b,c),          fix(w4; C6^w1, C6^w2),
    C6=(a,b,c,abar,bbar,cbar).

Return subgroup list C6^(w3 w4). This adds four generators and |L_Q|+18 relators, and returns six words. It is exactly the join with Fbar x {1}, followed by intersection with {1} x F, from Sections 6.5.2, 6.6.2, 6.9.4 and 6.10.3.

## 2. Bases and binary operations

For Z, take K_Z=F and L_Z=(a): (3,0,1). For S, take the fixed group A of (5.10), with nine names

    a,b,c,t,t',u1,u2,d,e

and these twenty relations, where each `fix` or `map` now refers to the already declared letter:

    b^t=b; b^(t')=b^(c^-1); c^t=c^2; c^(t')=c^2;
    u1 fixes b^c,t,t'; u2 fixes a,b,t,t';
    d fixes a^u1,b^u1,c^u1;
    d sends a^u2,b^u2,c^u2 to a^(b u2),b^u2,c^(b u2);
    e sends a,b,c to a,b^c,c.

Put d_i=d^(e^i). Return L_S=(a^(b^c),d d_1), so the size is (9,20,2). Lemma 5.12 increments the chosen coordinate by conjugating a_f by d_i. Thus (d d_1)^n sends a_(0,1) to a_(n,n+1); the source's normal-form argument proves the required intersection for all signed n. [Primary Sections 5.2--5.3 and 6.2, pp. 22--26.](https://arxiv.org/pdf/2507.04347v8)

For two normalized inputs, amalgamate their presentations over the literal F, append fix(v1;L1), fix(v2;L2), and retain both inherited relator lists. For intersection return (a,b,c)^(v1 v2); for union return (a,b,c)^v1 concatenated with (a,b,c)^v2. The two exact recurrences are

    intersection: (g1+g2-1, r1+r2+l1+l2, 3),
    union:        (g1+g2-1, r1+r2+l1+l2, 6).             (1)

These are the star-construction of Section 6.3, using its Lemmas 5.4--5.6. The named-word recipes and inherited presentations are part of (1), not hidden subgroup data.

## 3. The six unary wrappers

Each wrapper copies only its indicated input occurrence. All sets of paired words below mean products of the two coordinates in a direct product; the coordinate factors commute there.

**Reflection rho.** Form Kbar_0=Kbar_E *Fbar Abar, then P=Kbar_0 x A. Append fix(v1;abar a,dbar d,ebar e^-1) and fix(v2;Lbar,a,d,e). The graph list L_Q is (X_Abar,X_A)^(v1 v2), with eighteen words. Apply the common extraction. P has g+15 generators and r+9g+94 relations; the two fixes add l+6 relations and the extraction adds 36. Hence

    rho: (g+21, r+9g+l+136, 6).                        (2)

**Shift sigma.** Form P=Kbar_E x F. Append fix(v1;abar a,bbar b^c,cbar c) and fix(v2;Lbar,a,b,c). Set L_Q=C6^(v1 v2), then extract. P has g+3 generators and r+3g relators; the first two fixes add l+6 and extraction adds 24. Thus

    sigma: (g+9, r+3g+l+30, 6).                        (3)

**Single-site liberation zeta.** Let B=K_E *F A, with g+6 generators and r+20 relators. Append, in this order,

    fix(v1;L), fix(v2;d),
    fix(v3;X_B^v1,X_B^v2), fix(v4;a,b,c).

Return X_B^(v3 v4). Its sizes are

    zeta: (g+10, r+2g+l+36, g+6).                      (4)

**Right liberation pi.** Enlarge A by fresh x,x' sending (d,e) to (d,e^2) and (d_(−1),e^2), respectively. This A* has eleven generators and twenty-four relators. Let B=K_E *F A*, with g+8 generators and r+24 relators. Append the same four fixes as in zeta, except v2 fixes (d_1,x,x'). Return X_B^(v3 v4). Then

    pi: (g+12, r+2g+l+46, g+8).                        (5)

The differences between (4),(5) and the paper's +42,+52 relator constants are deliberate duplicate elimination: its v3 lists X_A and all input generators, hence repeats the common a,b,c once on each conjugate side. Removing precisely those six duplicate relators is valid, and our returned list uses each base generator once. No group simplification is assumed.

**Even-coordinate projection theta.** Form B=Kbar_E *Fbar Abar*, where Abar* adjoins y sending (dbar,ebar) to (dbar_2,ebar). Here dbar_2=ebar^(-2)dbar ebar^2, not dbar squared. The unbarred markers a,b,c do not yet occur. B has g+7 generators and r+22 relators. Append

    fix(v1;Lbar), fix(v2;dbar_1,y),
    fix(v3;X_B^v1,X_B^v2), fix(v4;abar,bbar,cbar).

Call the result J and its subgroup list V=X_B^(v3 v4). J has g+11 generators and r+2g+l+41 relators. Form J x F, introducing the unbarred markers now. Append fix(v5;V,a,b,c), fix(v6;abar a,bbar b,cbar^2 c); set L_Q=C6^(v5 v6), then extract. The relator increments after J are 3(g+11), (g+7)+3, 3, 24. Consequently

    theta: (g+20, r+6g+l+111, 6).                      (6)

**Swap tau.** Build the fixed B from A by adding x0,x0',x2,x2',y0,y1,y2. Each x maps (d,e), with images respectively

    (d_1,e^2), (d,e^2), (d_(−1),e^2), (d_(−2),e^2).

The y0,y1,y2 fix (d_(−1),x0,x0'), (d,d_1), (d_2,x2,x2'), respectively. Hence B has 16 generators and 20+8+8=36 relators. Form Kbar_0=Kbar_E *Fbar Bbar and P=Kbar_0 x B. Append fix(v1;T20), where T20 consists of

    xbar^ybar0 x^y0 for every x in X_A;
    dbar^ybar1 d_1^y1, dbar_1^ybar1 d^y1;
    xbar^ybar2 x^y2 for every x in X_A.

Append fix(v2;Lbar,a,d,e). The graph list L_Q=(X_Bbar,X_B)^(v1 v2) has 32 words. Extract as above. P has g+29 generators and r+16g+280 relators. The first two fixes add l+23 and extraction adds 50. Therefore

    tau: (g+35, r+16g+l+353, 6).                       (7)

All the recipes in this section are finite word lists; the source identifies their intersections with the intended A_operation(E) in Sections 6.5--6.10. The displayed sums independently derive their counts. Fresh renaming preserves all fixed marker inclusions and the named subgroup words.

## 4. The block wrapper, including its necessary domain

Fix an integer d>=1 and suppose E is supported at 0,...,d−1 and contains the zero block. These hypotheses hold at each actual omega input below. The following reconstructs the fixed auxiliary D_d from Sections 6.11.1, 6.11.4--6.11.6; d is the block size, distinct from the number g of input presentation generators.

Start with the eight generators b,c,t_d,t_d',t_0,t_0',r1,r2. The four t letters send (b,c) respectively to (b_(1−d),c^2),(b_(−d),c^2),(b_1,c^2),(b,c^2); r1 fixes (b_d,t_d,t_d') and r2 fixes (b_(−1),t_0,t_0'). These give fourteen relators. Adjoin g0,h,k, each fixing b^r1,c^r1,b^r2,c^r2. Denote the eleven-generator, twenty-six-relator result G_d. Write h_i=h^(k^i).

For s=1,...,d and j=0,...,s−1 add l_(s−1,j), acting on (b_(s−1),g0,h_0,...,h_(s−1)) as follows: fix b_(s−1); send g0 to g0^h_j; send h_i to h_i^h_j when i<j, and fix h_i when i>=j. These are exactly s+2 relations per letter, the table (6.36). Add p0 fixing g0; for each s>=1 add p_s fixing

    g0^h_(s−1) b_(s−1)^(-1) g0^(-1),
    l_(s−1,0),...,l_(s−1,s−1).

The result F_d has

    11+d(d+1)/2+(d+1) = 11+(d+1)(d+2)/2 generators,
    26+sum_[s=1..d] s(s+2)+1+sum_[s=1..d](s+1)
       =27+(d^3+6d^2+8d)/3 relators.

Adjoin a fixing every word in X_(G_d)^p_i for i=0,...,d; there are 11(d+1) such words. Adjoin q sending (a,b,c) to (a,b^(c^d),c). Call the result D_d, and put

    dgen=13+(d+1)(d+2)/2,
    drel=41+(d^3+6d^2+41d)/3.                           (8)

Rename the input markers (a,b,c) to (g0,h,k) throughout its generators, relators and L. Amalgamate it with D_d over these three literal names. Append

    fix(q1;L), fix(q2;a,q),
    fix(q3;X_(D_d)^q1,X_(D_d)^q2), fix(q4;a,b,c).

Return the list X_(D_d)^(q3 q4). Every marker in this description is a named finite word; no extra subgroup membership test is required. The resulting recurrence is

    omega_d: (g+dgen+1,
              r+l+74+(d^3+9d^2+50d)/3,
              dgen).                                 (9)

Indeed the generator count is g+dgen−3+4, and the relator count is r+drel+l+2+2dgen+3. The three sizes actually needed specialize to

| Primitive | g output | r output | subgroup words |
|---|---:|---:|---:|
| omega_2 | g+20 | r+l+122 | 19 |
| omega_4 | g+29 | r+l+210 | 28 |
| omega_18 | g+204 | r+l+3290 | 203 |

The group-theoretic input is Lemmas 6.4--6.7 with the zero-block condition retained. The syntax/count proof above does not replace their normal-form proofs.

## 5. Applicability and remaining materialization work

The closed unary note's omega_2 input is zeta_1 Z union tau S, so it contains zero and is supported on two coordinates. Its omega_18 input is the union of Run, Clear and Restart; all branches are supported on eighteen coordinates, and Restart contains zero. The pattern note's omega_4 input is L1 union L2, where L1={(0,0,m,n):m,n in Z}; it too is supported in its block and contains zero. Thus no omega_6, uncertain zero-membership test or arbitrary-input omega wrapper is needed for this particular unary/pattern expression. Repeated macro occurrences may be copied with fresh private names. The count recurrence concerns a fully expanded expression tree, without assuming sharing of already constructed overgroups.

The finite macro expansion from the committed recognizer and pattern can therefore be traversed from Z,S upwards using (1)--(9), recording at each node the generators, relators, the three marker words and the exact subgroup-word list. This is a concrete next materialization recipe under the scoped group-theoretic premises, not a numerical count of the final universal presentation. Named words, not counts alone, must be retained; in particular theta and omega rename the old free factor while introducing a new literal a,b,c.

**Question 1 (next finite object, credited to root).** Expand the specific closed expression with deterministic namespaces, the corrections below, and certified block inputs, producing an authenticated finite presentation K_(X_U) and subgroup list L_(X_U). Independently audit the resulting word lists and syntax counts. That expansion has not been performed in this note.

**Question 2 (subsequent embedding).** Feed those actual words into the Section 7 embedding with the already recorded fixed generator swap for its parity inconsistency. The prior conditional formula for the final relator count and the recipe-only lower floor do not become numerical universal compiler bounds merely from (1)--(9). Named embedding words, the exact final finite relator list, and the subsequent signed/positive matrix alphabet still require materialization and review. No matrices, relator values, Diophantine operation bound, minimality, or complexity estimate are supplied here.

## 6. Retained literal-source boundaries

**Remark 1 (omitted inherited relations in (6.2)).** The final binary presentation on p.26 omits S1,S2 although the preceding construction is an amalgam of the given presentations. They must be retained. This is substantive for literal transcription: take K1=F3 * <t|t^2=1>, L1=<a>, and K2=F3,L2=<a>. Both are valid benign pairs for <a>. The displayed relation list without t^2 maps onto an infinite cyclic group by sending t to its generator and all other names to identity. Hence the prescribed named map from K1 would not even respect its relation t^2=1. Formula (1) includes both relation lists.

**Remark 2 (copy and pi name slips).** Page 27 prints the barred rank-three factor with generators abar,cbar,cbar; the intended copy is abar,bbar,cbar. Page 36 declares x1,x2 but its relations use x1,x1', and writes X where the input list was Z. Recipe (5) uses the two consistently named stable letters x,x' and the normalized base list. The +42,+52 counts for zeta/pi can be realized as redundant relation lists; their six-relation reduction in (4),(5) is a declared choice, not a claim those larger counts were arithmetically false.

**Remark 3 (theta's premature unbarred factor).** On p.37, after defining K=Kbar_E *Fbar Abar*, the presentation and (6.18) also insert unrelated unbarred a,b,c. The later construction explicitly takes the resulting benign overgroup times F3. To implement that preceding construction, the early base must omit those unbarred names; they are introduced at that direct product. Thus its base size is g+7, not g+10. Its displayed unsimplified final relator sum on p.39 would evaluate to r+6g+l+120, not the printed +111. The corrected base lists in (6) give precisely +111. The map y uses dbar_2 (subscript), as visually checked on pp.37,39; interpreting this as dbar squared would be a different map and is not used here.

**Remark 4 (tau's final display and counts).** In (6.30), y0,y1,y2 are repeated after already appearing in X_B; the purported barred y relations repeat the unbarred ones; and the last w4 line loses the two separately conjugated six-word lists. The preceding constructions and the extraction recipe specify all three repairs. Count distinct names once, use the complete barred copy of B's relations, and make w4 fix C6^w1 and C6^w2. This gives (7). Even the paper's printed unsimplified relation-count expression equals r+16g+l+353, whereas its last simplification prints +345. No operation-specific lemma is refuted by this literal-transcription correction.

**Remark 5 (omega generator arithmetic, marker overlap and stable-letter name).** On p.49 the raw number 11+d(d+1)/2+(d+1)+2 is simplified incorrectly to 13+(d+1)^2/2. At d=2 that expression is not even an integer. Its correct value is dgen in (8). The error propagates into (6.47),(6.48) and p.50. In addition, the input alphabet already contains the renamed g0,h,k, so they are counted once when amalgamated with D_d. Equations (8),(9) derive the corrected recurrence from the actual generator and relation families, including the 2dgen centralizer relations. Riemann also identified the s=2 stable letter printed as t_2 in (6.38), whereas H and the subsequent generator lists use p_2. At d=2, t_2 is already an earlier generator, so literal reuse violates the required fresh-name construction. The consistent p_s names in Section 4 implement the intended construction. I confirmed this discrepancy visually on p.47.

**Remark 6 (omega needs zero).** In Section 6.11.3 the proposed W_E=<g_f,a,q:f in E> always contains a, and the proof later explicitly uses '(0) in E' without a prior general hypothesis. If E={(1,0,...,0)}, omega_d E is empty: any finitely supported sequence has a distant all-zero block. This is a valid supplied input, with the finite benign pair K_E=F3, L_E=(a^b). Consequently A_(omega_d E) is trivial, whereas F3 intersect W_E contains the nontrivial a. This disproves the unqualified equality for that proposed construction, not the general existence theorem for benign subgroups. When zero is known absent, a trivial pair for the empty output could be chosen, but deciding that condition from an arbitrary recursively enumerable input is not granted here. Our actual three block inputs have explicit zero witnesses, so (9)'s restricted use avoids this boundary.

**Remark 7 (a uniform finite-expression repair, not a membership test).** The preceding counterexample does not obstruct an arbitrary-input recipe. Aristotle supplied the following set identity; root and Pascal independently checked the exact freeing directions and both cases. For a block-supported E define, with composition right to left,

    Gate(E) = zeta pi rho pi(E intersect Z),
    omega_d(E) = omega_d(E union Z) intersect Gate(E).    (10)

If 0 belongs to E, the inner intersection is Z. Starting from Z, the inner pi frees positive indices, rho changes these to negative indices, the outer pi frees the positive indices too, and zeta finally frees index 0. Each patch is finitely supported. Hence Gate(E) is the entire universe of finitely supported integer functions. If 0 does not belong to E, the inner intersection is empty and all four unary operations preserve emptiness, so Gate(E) is empty. In that case omega_d(E) itself is empty because any finitely supported candidate has a distant zero block. In the other case E union Z=E. These two cases prove (10), without deciding which one holds.

For an input E without a prescribed block-support restriction, first replace it by E intersect Box_d, where Box_d=zeta_{0,...,d-1} Z; this does not change its omega_d output. Thus (10), the finite box, and the restricted omega recipe give a finite presentation grammar for arbitrary omega inputs, conditional on the same imported subgroup-identification lemmas. Each occurrence of E is independently namespaced in an expression-tree expansion. This wrapper is unused in the actual closed recognizer/pattern, so it changes none of (1)--(9) or the three actual case counts; no extra numerical compiler bound is claimed for it.

The old pattern projection/swap corrections, the embedding parity correction, and the recognizer's retained remarks remain in their frozen source notes. No predecessor bytes are changed by this note.

## 7. Evidence and scope

Primary text was read from the exact v8 PDF cache and a fresh ordinary `pdftotext -layout` extraction: extracted LF lines 301--410 and 1009--2835, covering the relevant definitions and all of Sections 5--6, plus the start of Section 7. Numbered pages 26,27,36,37,39,42,47,49,50 were visually checked for the literal displays above. The full primary article, its antecedent papers and Section 7 embedding proof were not audited. The committed recognizer/pattern interfaces were read previously in full; their exact omega and marker clauses were reread here. Whole-byte and exact span bindings will accompany the final metadata. Ordinary PDF extraction/rendering, read-only repository authentication and fresh byte metadata are the only machine operations; no scientific code, supplied helper, stored array, arithmetic-circuit evaluation or degree propagation was run.

Root independently read the complete initial draft and checked all normalized word-list counts and recurrences, including the actual block-support/zero prerequisites; the hand challenge passed. He then read the full final 187-line mathematical note and its complete metadata, including Remark 7 and the finite-box preprocessing, with no correction. His selected primary source read covered LF1240--1260,1380--1439,1639--1692,1868--2020,2025--2175. Riemann independently checked the tau and omega word recipes, exact primary count lists, zero-block counterexample and actual zero witnesses, and supplied the extra stable-letter correction retained in Remark 5. Root, Pascal and Riemann separately passed the uniform set identity in Remark 7; Riemann also read its complete final paragraph. These challenges do not claim independent verification of every primary normal-form lemma. No executable presentation expander or complete group/matrix list has been emitted.

This author note and its metadata are frozen after those scoped challenges. The operation-specific subgroup-identification lemmas remain attributed premises throughout. Final edits after the complete mathematical review change only this provenance/status.
