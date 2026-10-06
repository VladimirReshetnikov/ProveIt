# A persistent common ambient for explicit Higman compilation

The normalized Higman recipes can reuse previously constructed benign-pair data in one finitely presented group. Binary operations need no copies of that ambient. For unary recipes that change the distinguished free subgroup, one explicitly paid HNN letter transports every stored pair to the new subgroup. Moreover, a single initial group supports every fixed affine-lattice relation needed for constants, equality, opposite pairs and finite coordinate boxes. These are concrete presentation and word-list constructions, not an assumption that expression-tree sharing is harmless.

The operation-specific subgroup identifications of the frozen normalized recipe note remain imported premises. The new ingredients proved here are the common-ambient binary construction, persistent transport, one universal shift letter, the affine-orbit intersection lemma, and their exact syntactic accounting. The ambient embeddings use the ordinary HNN/amalgam normal-form theorem. No complete universal presentation, arithmetic compiler bound, optimized machine table, expander, scientific code or saved-source evaluation is supplied.

## 1. Exact state and the affine bases

A state consists of a finite presentation K=<X|R>, a distinguished embedded free subgroup F=<a,b,c> of rank three, and finitely many stored lists L_j satisfying

    F intersect <L_j> = A_(E_j),
    A_E=<a_f : f in E>,  a_f=b_f^-1 a b_f,
    b_f=product_[i increasing] b_i^f(i), b_i=c^-i b c^i. (1)

No free-product-factor property of F in K is assumed. Each E_j is the already specified set whose pair is cached. Counts g,r,l_j are numbers of declared generator names, relators and subgroup words, not ranks or minimum sizes. Every fresh presentation letter is distinct. All word transformations below are explicit finite concatenation, inversion and renaming; no group word problem or semantic equivalence oracle is called.

Start with the fixed group A of primary (5.10), with generators a,b,c,t,t',u1,u2,d,e and twenty relators, as transcribed in the frozen normalized note. The source's Lemma 5.12 states

    a_f^(d_i)=a_(f+epsilon_i),
    a_f^(d_i^-1)=a_(f-epsilon_i),  d_i=e^-i d e^i.       (2)

Its Remark 5.13 shows that these translations commute in their action on the a_f, although the d_i themselves are not assumed to commute. This signed action is the explicit imported fact used for the following lemma. [Primary Section 5.3, p.24.](https://arxiv.org/pdf/2507.04347v8)

**Affine-orbit lemma.** For a fixed finitely supported integer function f0 and fixed finitely supported integer vectors v_1,...,v_q, define the finite words

    w_j=product_[i increasing] d_i^(v_j(i)),
    Lambda=f0+span_Z(v_1,...,v_q),
    L_Lambda=(a_f0,w_1,...,w_q).                        (3)

Then F intersect <L_Lambda>=A_Lambda inside A. This costs no additional presentation generators or relators and supplies exactly q+1 subgroup words. Redundant or zero vectors may be retained and counted; no lattice-basis minimization is assumed.

To prove it, map A to the free group on d,e by killing its other seven named generators. Every one of the twenty displayed relators becomes the identity, so this is a retraction. Consequently <d,e> embeds in A and its intersection with F is trivial. Let H=<w_1,...,w_q> inside this embedded group. By (2), the H-orbit of a_f0 is exactly {a_f:f in Lambda}; negative coefficients use the inverse half of (2). Conjugate collection rewrites any word in <a_f0,H> as a product of signed orbit conjugates followed by a residual h in H. The orbit conjugates are in F. If the original word lies in F, the retraction forces the image of h to be identity; its restriction to <d,e> is injective, so h=1. This proves one inclusion. Conversely every orbit conjugate is in both F and <L_Lambda>, proving equality.

Thus the following lists coexist already in A. Put w=d d_1 and v=d d_1^-1.

| Set | Subgroup-word list in A |
|---|---|
| Z={(0)} | (a) |
| fixed singleton tuple {f0} | (a_f0) |
| C_k={(k)} | (a^(b^k)) |
| S={(n,n+1)} | (a^(b^c),w) |
| Eq={(n,n)} | (a,w) |
| tau S={(n+1,n)} | (a^b,w) |
| D={(n,-n)} | (a,v) |
| Box_I, arbitrary entries on fixed finite I and zero elsewhere | (a,(d_i)_(i in I)) |

In particular Box_d has d+1 words, reset2={(0,n)} has (a,d_1), and Box_1 has (a,d). The words w=d e^-1 d e and v=d e^-1 d^-1 e are nontrivial cyclically reduced free words; their nonzero powers cannot disappear in the retraction. Formula (3) proves the more general multi-vector assertion without needing these powers as a separate assumption.

These are precompiled benign pairs for sets already defined by the H-expression, not new logical primitives or oracles for arbitrary recursively enumerable data. A fixed finite set of explicit tuples also has the trivial list of its a_f words in F, and the empty set has an empty list. Fixed affine atoms in a finite window can be supplied by giving their offset and integer directions explicitly. For example, equality at i,j uses direction epsilon_i+epsilon_j and each other free coordinate direction; successor uses the same directions and offset epsilon_j. A fixed value k at i uses offset k epsilon_i and the remaining free coordinate directions. Intersections/unions with other relations must still use the constructions below.

## 2. Binary operations inside a shared ambient

Suppose L_1,L_2 in the same K represent H_i=F intersect <L_i>. Adjoin distinct v1,v2 centralizing the respective lists:

    Q=<X,v1,v2 | R, [v1,u]=1 (u in L1),
                         [v2,u]=1 (u in L2)>.

K embeds by the HNN normal-form theorem. Inside Q, the subgroup generated by F,v1,v2 is the HNN extension of F in which v_i centralizes H_i: a Britton-reduced word over F stays reduced in Q, since its possible pinch coefficient f belongs to <L_i> exactly when f belongs to H_i. Hence

    F intersect F^(v1 v2)=H1 intersect H2,
    F intersect <F^v1,F^v2>=<H1,H2>.                   (4)

For the first equality, reduce v2^-1 v1^-1 f v1 v2: reaching F requires successively f in H1 and f in H2. For the second, consider the star amalgam with central vertex F and two leaf copies F1,F2 joined along H1,H2. Map its leaves to F^v1,F^v2. The same normal-form argument embeds this star in Q. Write H=<H1,H2> in the central F. The smaller star with central group H and the same leaves embeds in the larger one and meets its central F exactly in H. It is generated by the leaves because H is generated by their edge subgroups. This proves the second equality. Pascal independently supplied this explicit star-amalgam proof.

For our indexed free-basis subgroups, H1 intersect H2=A_(E1 intersect E2) and <H1,H2>=A_(E1 union E2), as in the primary binary identification. Return respectively

    (a,b,c)^(v1 v2),  or  (a,b,c)^v1,(a,b,c)^v2.

The exact updates are

    g'=g+2, r'=r+l1+l2, l_new=3 or 6.                 (5)

All previously stored lists remain valid by the embedding. There is no second copy of R. This is also the specialization G=F,M=K,K1=K2=K of primary Lemmas 5.4--5.6; Example 5.1 explicitly permits coincident ambient groups. [Primary Section 5.1, pp.20--21.](https://arxiv.org/pdf/2507.04347v8)

## 3. Persistent transport through any unary wrapper

Apply one normalized unary recipe to a selected list L_E in the entire current ambient K. Its construction contains an injective, explicitly named copy phi(K), and the inherited R is retained once. It produces a new distinguished free triple F_out=(a_out,b_out,c_out) and a new list L_new. Let F_in=(phi(a),phi(b),phi(c)). If the two triples are already the same, leave all stored data in their embedded copies; this is the case for zeta and pi.

Otherwise adjoin one fresh stable letter t and exactly three relations

    phi(a)^t=a_out, phi(b)^t=b_out, phi(c)^t=c_out.      (6)

Both triples are free bases of embedded rank-three subgroups, so the prescribed map is an isomorphism. The HNN normal-form theorem embeds the entire unary output group in this extension. For every old stored list define

    L_j'=(phi(L_j))^t.                                 (7)

Within the extension, conjugation gives the literal intersection identity

    F_out intersect <L_j'>
       =(F_in intersect <phi(L_j)>)^t
       =(phi(A_(E_j)))^t=A_(E_j) in the new marker.     (8)

The last equality follows by mapping the three free generators in the definition (1), so the order of the b_i factors is preserved. The new list L_new remains unchanged: its intersection with F_out is preserved by the embedding. Each old list keeps the same number of words. Thus one paid t restores every stored pair at once; no t per cached set is needed.

Keep also an explicit embedding of the initial A with its marked F. Under this step, update that embedding by phi followed by conjugation by t. Its distinguished markers become F_out by (6), and its d,e words are updated by the same rule. Formula (3) can therefore create further fixed affine lists on demand in the current group, even after many unary steps. Its proof is transported inside this embedded A; a retraction of the whole current ambient is neither assumed nor needed.

The input embeddings in the frozen recipes are concrete: rho, sigma, theta and tau use a barred renamed copy of K; omega_d renames its input markers to g0,h,k; zeta and pi retain the input markers. No unary recipe duplicates K. Calling the whole current K the input ambient does increase the new centralizer/commutator lists according to g, and the table below pays for all of them.

## 4. One shift letter for every future fixed shift

Initially adjoin s to A with

    a^s=a, b^s=b^c, c^s=c.                             (9)

The map on F is an automorphism, with inverse fixing a,c and sending b to cbc^-1. The ambient embeds. Since b_i^(s^k)=b_(i+k) and the index order in b_f is preserved,

    F intersect <L_E^(s^k)> = A_(sigma^k E)             (10)

for every integer k and every stored list. This remains true even though the words of L_E need not lie in F: s normalizes F, so conjugation commutes with taking its intersection. Fixed shifts cost no further presentation rows and do not change the list length; their finite word spelling is retained, not declared free of storage cost.

The initial shared ambient thus has ten generators and twenty-three relators. After a marker-changing unary step, update the distinguished shift word to (phi(s))^t, as in (7). It still satisfies (9) for F_out by conjugating the three identities. It may now be a word rather than a single named generator, which is allowed. If the marker does not change, use phi(s). No extra shift letter is added.

Root independently supplied the fixed-singleton initialization and checked the shift automorphism. The affine-orbit bases strengthen that initialization to whole fixed affine lattices; they do not identify distinct input-dependent sets without proof.

## 5. Exact persistent recurrences

Here g,r refer to the whole ambient immediately before the update, l to the chosen input list, and l1,l2 to the two binary lists. Every old cached list retains its length. The new-list sizes and all added presentation rows are:

| Update | new generators | new relators | new list size |
|---|---:|---:|---:|
| intersection / union | 2 | l1+l2 | 3 / 6 |
| rho | 22 | 9g+l+139 | 6 |
| sigma, if using the generic recipe instead of (10) | 10 | 3g+l+33 | 6 |
| zeta | 10 | 2g+l+36 | g+6 |
| pi | 12 | 2g+l+46 | g+8 |
| theta | 21 | 6g+l+114 | 6 |
| tau | 36 | 16g+l+356 | 6 |
| omega_d | D_d+2 | l+77+(d^3+9d^2+50d)/3 | D_d |

Here D_d=13+(d+1)(d+2)/2. The generic sigma row is displayed only to account for every normalized wrapper; after initialization (9), use (10) instead, adding no rows. The rho/theta/tau/omega rows add exactly one generator and three relations to the frozen normalized recipes. Zeta/pi do not require this transport.

| Fixed block size | new generators | new relators | new list size |
|---|---:|---:|---:|
| 1 | 18 | l+97 | 16 |
| 2 | 21 | l+125 | 19 |
| 4 | 30 | l+213 | 28 |
| 18 | 205 | l+3293 | 203 |

The block-supported, zero-containing hypothesis for the direct omega recipe is unchanged. N is one-supported and contains zero, so the d=1 row is available if a subsequent compiler chooses a global omega_1(N) condition; no acceptance-machine change is certified by this note. Arbitrary omega inputs may instead use the frozen Gate/Box repair. Its added primitive nodes must then be counted. No membership test is inserted.

For an actual stored expression DAG, process a topological order. A request for an already stored node returns its current subgroup list without modifying K. A unary request uses the whole current K once; a binary request uses (5). Fixed affine leaves use (3), and fixed shifts use (10). The invariant (1), the stored embedding of A and the shift word are preserved by induction. This proves a conditional shared-presentation compiler; it does not assert that arbitrary identifications of tree copies are safe.

There is a concrete size consequence, even before optimizing the graph. Suppose the fixed affine leaves have at most nineteen listed words, every non-shift update uses a binary operation or one of the displayed unary operations with d in {1,2,4,18}, and there are N such updates. Initially g=10,r=23, and every stored list length is at most g+9. This remains true: new liberation lists have lengths g+6 or g+8 before the update, new graph lists have length at most six, and D_d is smaller than the new ambient size. Each update adds at most 205 generators and at most 17g+3302 relators. Consequently

    g_N <= 10+205N,
    r_N <= 23+3472N+(3485/2)N(N-1).                   (11)

These are conservative declared-row bounds, not minimality or running-time claims. Fixed word lengths, the number of cached lists and their storage remain separate data. The bound is on the actual shared graph's updates, not on a secretly expanded tree. The exact table is preferable when a particular graph is known.

## 6. A concrete reusable N prefix

Here is one complete small hand-counted schedule, using the frozen recognizer's original nonnegative-chain formula, without adopting any later machine simplification. All the affine lists of Section 1, including Eq, remain available in the initial A and are transported with it. Let B0 be reset2={(0,n)}, represented by (a,d_1), let T=tau S be represented by (a^b,d d_1), and let Box_1 have (a,d).

    U=B0 union T;
    V=omega_2 U;
    W=V intersect sigma^-1 V;
    N=(pi rho pi rho W) intersect Box_1.               (12)

The last line is exactly Right_0 Left W intersect Box_1. Each adjacent pair of a witness for W either starts at zero or decreases by one. Finite support excludes a negative entry; a finite descending string realizes every nonnegative entry. Thus N={(n):n>=0}, as in the frozen recognizer proof. U is two-supported and contains zero, so its omega use is valid.

The row sizes of the shared ambient after each update are derived directly from Section 5:

| Stage | g | r | new list length |
|---|---:|---:|---:|
| A plus global s | 10 | 23 | B0,T,Box_1 each 2 |
| U=B0 union T | 12 | 27 | 6 |
| V=omega_2 U | 33 | 158 | 19 |
| W=V intersect sigma^-1 V | 35 | 196 | 3 |
| rho W | 57 | 653 | 6 |
| pi rho W | 69 | 819 | 65 |
| rho pi rho W | 91 | 1644 | 6 |
| pi rho pi rho W | 103 | 1878 | 99 |
| N, after intersection with Box_1 | 105 | 1979 | 3 |

For example, the first rho adds 9*35+3+139=457 relations, and the last intersection adds 99+2. This is an exact recipe/count schedule, not an emitted or machine-audited presentation. It leaves an explicit 105-generator,1979-relator common ambient with N's three-word list and the embedded A supporting Eq, S, all fixed constants, opposite pairs and coordinate boxes. That is a bounded fragment, not a final universal relator count. No assertion of optimality is made.

## 7. Retained boundaries and next step

**Remark 1 (joining witness lists for free fails).** Take K=F3 x <z>, L1=(z), L2=(az). Each has trivial intersection with F3, but <z,az> contains a. Therefore simply concatenating L1 and L2 in a common group does not compute the union's indexed subgroup. The paid two-letter construction (5) is essential to the stated recipe. A literal intersection of subgroups does have the correct set intersection with F, but a finite generating list for that subgroup is not provided for free; (5) supplies three explicit words.

**Remark 2 (identifying the two free markers is unsafe).** In F3 x F3, identifying the corresponding generators of its two commuting factors forces the common a,b,c to commute. In particular the old nontrivial commutator [a,b] dies. Thus direct marker identification can destroy the very free-group embedding required by the construction. It is not a substitute for (6). The HNN letter implements an isomorphism between embedded subgroups while keeping the entire preceding group injective.

**Remark 3 (not every auxiliary copy has been shared).** The theorem reuses the whole ambient and previously stored pairs. It does not silently reuse the fixed A or B auxiliary factors inside each normalized unary wrapper; their prescribed fresh names and all their paid rows remain in the table. Previously embedded affine data are reused through the tracked copy of the initial A, not by changing those wrappers' amalgamation hypotheses. Likewise an arbitrary semantic equality between two requested sets is not detected automatically; only an explicitly identical cached node or a separately proved replacement such as Section 1 is reused.

**Remark 4 (draft terminology).** The preliminary invariant called F a 'free factor' while immediately disclaiming any free-product decomposition of K. The intended and now consistently stated property is an embedded free subgroup. Neither the proof nor any count used the stronger free-factor property.

**Question 1 (next materialized object, credited to root).** Choose the exact optimized recognizer/pattern DAG or the independently verified affine transition grammar, then emit its literal presentation using this state invariant, every named subgroup list, the tracked marker maps and the exact table. Authenticate and independently audit it before reporting a final universal presentation or converting it to the named embedding/matrix alphabet. The present hand construction proves that sharing is legitimate and supplies a concrete reusable prefix; it does not perform that expansion or audit.

The seven source corrections and restricted/uniform omega distinctions in the frozen normalized note remain retained there without modification. The newly proved affine-orbit identities use the explicit signed action (2) as their source premise. The unary operation-to-subgroup identifications are still attributed to the primary constructions, not independently re-proven here. No scientific execution, presentation expansion, saved-array evaluation or degree propagation occurred.

## 8. Scoped evidence and review

For this note, the primary v8 reading cache was reread at LF1009--1134 (star-construction and binary normal forms) and1240--1410 (A's explicit relators, signed action and S). The frozen normalized recipe note was previously read and checked in full, and its first100 lines were reread here for the named wrapper embeddings. The frozen unary-recognizer note was previously independently reviewed in full; LF74--107 were reread here for the N relation and finite-support proof. These exact bytes and read spans are bound in the metadata. No full independent verification of all imported unary subgroup-identification lemmas is claimed.

Root independently passed the entire core draft, including all new proofs, the recurrence table, the conservative quadratic bound and the105/1979 prefix. Pascal independently supplied the detailed common-ambient union proof and checked the affine retraction/signed-action argument and local transport identity. Riemann independently read the full draft and passed the binary proof, transport invariant, carried A and shift word, affine lemma, every count row, quadratic bound and complete N prefix; his source reread covered primary LF1240--1382. The only ensuing wording clarification is retained as Remark4. The separate prospective whole recognizer/pattern schedule is deliberately outside this artifact.

This core proof and its byte/read-scope metadata are frozen after those scoped challenges. There is no presentation expander, emitted universal word list or numerical universal Diophantine bound in this packet. Standard byte metadata and inert source reads are the only machine work.
