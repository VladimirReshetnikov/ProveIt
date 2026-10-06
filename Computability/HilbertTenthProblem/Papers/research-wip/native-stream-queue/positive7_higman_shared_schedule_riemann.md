# A complete hand schedule for the shared Higman presentation

Combining the frozen affine recognizer with the persistent common-ambient construction gives a complete hand-counted presentation schedule ending at

    X_U: (g,n,l)=(499,17678,3).

Here g is the declared ambient generator count, n is its declared relator count, and l is the selected subgroup-word list length. A subsequent conditional embedding ledger would give20808 relation slots. These are counts for a specified conditional word-construction schedule, **not a materialized universal presentation, matrix alphabet or numerical universal Diophantine bound**. No presentation expander or word-list audit has been run.

The strongest shortcut, proposed by Aristotle and independently challenged by root and Riemann, transfers the accepted subgroup directly to the affine pattern using one new HNN letter and two relations. Its finite proof is given below. The valid full-F automorphism decoder, root's `theta sigma^-1` projection and the earlier Keep route are retained as alternatives, including the old two-relation count correction. Root supplied the shared schedule and projection shortcuts; Riemann independently checked every displayed recurrence by hand. The affine semantics and persistent compilation are imported from the separately frozen proofs, with their own scoped peer challenges.

## 1. Frozen premises and counting conventions

The semantic source is `positive7_affine_typed_recognizer_pascal.md`, SHA256 `78e26e7b637378c5568a7da1127f5b39996572d3f254c3a65bf0065ffb61fcd0`. It proves the46 running affine branches, two delimiter branches, one global omega_1(N) condition, accepted-input equivalence with the fixed universal set U, and the final affine pattern/cylinder identity. Its imported Korec universality theorem is not independently re-proved here.

The compilation source is `positive7_higman_shared_ambient_aristotle.md`, SHA256 `12692f7c9037bef148e7a9cb7788c78465745b797889ebed4098da415b24c562`. It proves common-ambient binary operations, persistent HNN transport of every cached pair, one carried shift word, and direct affine-lattice lists in the embedded initial A. Its operation-specific subgroup-identification lemmas remain attributed premises. We use the whole current ambient as the input to every unary wrapper; its g is not replaced by the smaller size of an earlier local subgroup construction.

Start with A and its single global shift letter, giving(10,23). All fixed affine leaves use the tracked embedded A and cost no new ambient generators or relators; a lattice with q specified directions has q+1 subgroup words. Every needed integer offset/direction is explicitly prescribed by the affine note. Word lengths, copying/transport of those words and memory costs are separate from these declared-row counts. Fixed shifts use conjugation by powers of the current tracked shift word, so they add no presentation rows and preserve list length.

The persistent updates needed in this schedule are:

| Update on the current ambient | Added generators | Added relators | New selected list length |
|---|---:|---:|---:|
| intersection/union of lists l1,l2 | 2 | l1+l2 | 3/6 |
| rho on list l | 22 | 9g+l+139 | 6 |
| pi on list l | 12 | 2g+l+46 | g+8 |
| zeta on list l, retained older route only | 10 | 2g+l+36 | g+6 |
| theta on list l | 21 | 6g+l+114 | 6 |
| omega_1 on list l | 18 | l+97 | 16 |
| omega_2 on list l | 21 | l+125 | 19 |
| omega_18 on list l | 205 | l+3293 | 203 |
| direct two-pair transfer, proved in Section5 | 1 | 2 | l |

The g in the pi/zeta output-list column is the ambient size **before** that update. Every other cached list preserves its length while its words are transported. The omega calls below are all supported in their declared blocks and contain zero; no zero-membership decision or additional Gate/Box repair is needed.

## 2. The shared nonnegative prefix and global type list

Reuse the core note's explicit nonnegative construction. The initial affine leaves are B0={(0,n)}, T={(n+1,n)} and Box_1; each has two listed words. Put U0=B0 union T, V0=omega_2(U0), W0=V0 intersect sigma^-1 V0, and N=(pi rho pi rho W0) intersect Box_1, with operations composed right to left. Its full prefix is:

| Completed update | g | n | New list length |
|---|---:|---:|---:|
| A plus carried shift | 10 | 23 | affine leaves available |
| union B0,T | 12 | 27 | 6 |
| omega_2 | 33 | 158 | 19 |
| meet shifted copy | 35 | 196 | 3 |
| rho | 57 | 653 | 6 |
| pi | 69 | 819 | 65 |
| rho | 91 | 1644 | 6 |
| pi | 103 | 1878 | 99 |
| meet Box_1 | 105 | 1979 | 3 |
| global type G_N=omega_1(N) | 123 | 2079 | 16 |

N is the one-supported nonnegative relation. Its adjacent-pair construction contains zero and finite support excludes a negative descending tail, as proved in the core note. Thus the final omega_1 call is legitimate and G_N expresses coordinatewise nonnegativity. Cache its16-word list; it will be reused after building the history relation, with all intervening marker changes transported as prescribed.

## 3. All48 affine edge leaves and the typed history

Take the exact affine note's edge table. It has13 increment branches and17 positive-decrement branches, each represented by nine subgroup words, and16 zero-decrement branches represented by eight words. Thus the46 running lists contain

    30*9+16*8=398

word occurrences. Clear has nine words and Restart ten, giving417 words across48 leaves. These are list lengths in the existing common ambient, not ambient relation counts and not48 copies of A.

For definiteness, order the leaves as the13 increment branches in the note's listed order, the17 positive-decrement branches in increasing source-state order, the16 zero branches in their listed order, then Clear and Restart. Form a left-associated chain of47 paid binary unions. Every original leaf is an input once. The first46 union outputs have six words and are used as an input once; the final output is not reused inside this chain. Consequently it adds

    94 generators and417+46*6=693 relators.

The resulting list represents R_bare and has six words. This fully specifies the union ordering and its syntactic count without enumerating the expanded presentation words.

| Completed update | g | n | New list length |
|---|---:|---:|---:|
| R_bare after47 unions | 217 | 2772 | 6 |
| Omega=omega_18(R_bare) | 422 | 6071 | 203 |
| H_bare=Omega intersect sigma^-9 Omega | 424 | 6477 | 3 |
| Hist_aff=H_bare intersect cached G_N | 426 | 6496 | 3 |

Restart supplies a zero18-block, so the omega_18 hypothesis is explicit. The shifted copy of Omega costs no presentation rows and has the same203-word list length. The next two intersections add406 and19 relations respectively. The affine recognizer proves that the global G_N condition restores precisely the nonnegative counter typing of every adjacent edge; bare signed edges alone are not accepted computations.

## 4. Reachability block and the initial line

Apply Block_9=Right_8 Left followed by intersection with Box_9. Ignoring the paid-zero fixed shifts, its unary application order is rho,pi,rho,pi. The first three wrappers implement Left; shifts around the last pi put its right boundary at site8. The affine Box_9 has ten words. The initial line Init_aff=23delta_0+Z*delta_1 has two words.

| Completed update | g | n | New list length |
|---|---:|---:|---:|
| rho | 448 | 10472 | 6 |
| pi | 460 | 11420 | 456 |
| rho | 482 | 16155 | 6 |
| right-boundary pi, with its fixed shifts | 494 | 17171 | 490 |
| Reach_aff, after meet with Box_9 | 496 | 17671 | 3 |
| Accepted=Reach_aff intersect Init_aff | 498 | 17676 | 3 |

Every accepted function is now exactly(23,n,0,...,0), with n in U; its only possibly nonzero sites are0 and1. The prior Init intersection establishes this precise support. Its three-word list therefore satisfies F intersect <L_Accepted>=<a_(23,n):n in U>. This is the interface used by every alternative finish below.

## 5. Direct transfer to the affine pattern with two relations

This is Aristotle's separate frozen affine-line transducer lemma, `positive7_higman_affine_line_transducer_aristotle.md`, SHA256 `e431ab657885f06502be8685cbdd2cef92fe65c75e3d8692b8302aac355dc42f`, independently hand-challenged by root, Pascal and Riemann. It is a new local theorem beyond the frozen persistent core. We give the complete finite argument needed here, rather than assuming that an arbitrary conjugation transports F-intersections.

Let K be the current Accepted ambient. In its distinguished F=<a,b,c>, put

    alpha=a^(b^23), beta=b^c.

Then a_(23,n)=alpha^(beta^n). The pair(alpha,beta) is free of rank two: the assignment a→a^(b^23),b→b^c,c→c is a free-group automorphism, obtained by first fixing a,c and conjugating b by c, then fixing b,c and conjugating a by b^23. Thus(alpha,beta,c) is a free basis of F. Put P_in=<alpha,beta>.

Use the final pattern's fixed vectors

    f0=(0,0,1,0,1,0,-1,0,-1,0),
    v =(0,-1,0,1,0,-1,0,1,0,0),

and the explicit words in the tracked initial A,

    a0=a^(b_2 b_4 b_6^-1 b_8^-1),
    w=d_1^-1 d_3 d_5^-1 d_7.

The imported signed translation action gives a0^(w^j)=a_(f0+jv) for every integer j. Because v is nonzero, these are distinct indexed generators and form a free family in F. For clarity, the b_i freely generate the exponent-c kernel in Free(b,c), so their sorted words b_f are distinct for distinct f. The kernel of F=<a>*Free(b,c)→Free(b,c) has free basis{a^u:u in Free(b,c)}. Hence the displayed a_(f0+jv) are part of a free basis. Similarly, the d_i freely generate the exponent-e kernel in the embedded Free(d,e). The reduced word w is nontrivial and has infinite order there. Only the existing retraction A→Free(d,e) is used; no retraction of the whole K is assumed.

Here is an explicit proof that(a0,w) is a free rank-two pair. Write a nonempty reduced word in abstract x,y as

    y^k0 x^e1 y^k1 ... x^ep y^kp,

where every e_i is nonzero and every internal k_i is nonzero; the pure-y case is allowed separately. Its image under x→a0,y→w can be collected as a product of orbit conjugates followed by w^k, where k=sum k_i. If k is nonzero, the retraction detects the nontrivial w^k. If k=0 and p>=1, the orbit indices are j_i=−(k0+...+k_(i−1)); consecutive indices differ by the nonzero internal exponent−k_i. Thus the collected orbit-generator product is nonempty and reduced, with nonzero exponents and distinct adjacent free generators. It cannot be identity. A pure-y nonempty reduced word has nonzero k. This proves freeness by reduced words, not merely by total exponent data.

Consequently alpha→a0,beta→w defines an isomorphism from P_in to P_out=<a0,w>. Add one fresh HNN letter t and exactly the two relations

    alpha^t=a0, beta^t=w.                                (1)

The HNN normal-form theorem embeds K. Return the three-word list L_Accepted^t. For any h in <L_Accepted>, Britton's lemma says that t^-1 h t lies in K exactly when h belongs to P_in. All elements of the conjugated subgroup have that single-conjugate form. Hence

    K intersect <L_Accepted^t>
       =psi(<L_Accepted> intersect P_in)
       =psi(A_Accepted)=A_X_U.                           (2)

The middle equality uses P_in⊂F and A_Accepted⊂P_in. The final equality follows from psi(alpha^(beta^n))=a_(f0+n v). Its target already lies in the old marker F, so intersecting(2) with F gives exactly the desired benign pair. All old cached lists and the tracked A remain valid through the embedding. No marker transport, unary projection, pattern intersection or global cylinder is added after(1). In particular t is **not** claimed to normalize F: w generally lies outside F.

The exact finish is therefore

| Completed update | g | n | Selected list length |
|---|---:|---:|---:|
| Accepted | 498 | 17676 | 3 |
| two-relation transducer to X_U | 499 | 17678 | 3 |

The explicit three returned words are specified as conjugates of the three Accepted words, but those long Accepted words have not yet been materialized. Equation(1) is a finite word recipe, not an emitted universal presentation.

## 6. Three valid weaker finishes retained

The first two alternatives extract a unary E_U and then form C_U=sigma^3(Left pi E_U). The cylinder uses pi,rho,pi,rho in application order; the fixed shift adds no rows. The pattern P_pat=f0+Z*v has a two-word affine list in the tracked A. Since its coefficient at site3 is one, P_pat intersect C_U is exactly X_U. These alternatives are sound, although the direct transducer avoids their entire cylinder/pattern phase.

### 6.1. The full-F automorphism decoder

Aristotle's earlier decoder uses the free-group automorphism phi(a)=alpha,phi(b)=beta,phi(c)=c described above. Adjoin a fresh s_dec with those three HNN relations. It normalizes F, so conjugating L_Accepted by s_dec^-1 transports its F-intersection to A_U. The existing marker, cached lists and tracked A stay unchanged. This costs one generator and three relators, preserving the three-word list.

| Completed update | g | n | New list length |
|---|---:|---:|---:|
| decoded E_U | 499 | 17679 | 3 |
| pi | 511 | 18726 | 507 |
| rho | 533 | 23971 | 6 |
| pi | 545 | 25089 | 541 |
| rho and fixed shift | 567 | 30674 | 6 |
| meet P_pat | 569 | 30682 | 3 |

This one-generator/three-relator construction does normalize the whole F. That proof is different from the two-relator construction, which requires the exact Britton boundary(2).

### 6.2. Root's theta projection

For f=(23,n,0,...,0), the primitive definitions give

    (theta sigma^-1 f)(i)=f(2i+1).

The input value at site1 becomes the sole possible value at site0; the tag at site0 is not sampled. Conversely every n in U has its Accepted witness. Therefore theta sigma^-1 Accepted is exactly E_U. The shift is free in this presentation-count model, and theta adds21 generators and6*498+3+114=3105 relators.

| Completed update | g | n | New list length |
|---|---:|---:|---:|
| E_U via theta | 519 | 20781 | 6 |
| pi | 531 | 21871 | 527 |
| rho | 553 | 27316 | 6 |
| pi | 565 | 28474 | 561 |
| rho and fixed shift | 587 | 34259 | 6 |
| meet P_pat | 589 | 34267 | 3 |

### 6.3. The original Keep projection

The older route applies Keep_({0,...,8},{1}) to Accepted and then shifts left by one. Apply the eight zeta operations in the order0,2,3,4,5,6,7,8, using fixed shifts around each:

| Completed update from Accepted | g | n | New list length |
|---|---:|---:|---:|
| zeta_0 | 508 | 18711 | 504 |
| zeta_2 | 518 | 20267 | 514 |
| zeta_3 | 528 | 21853 | 524 |
| zeta_4 | 538 | 23469 | 534 |
| zeta_5 | 548 | 25115 | 544 |
| zeta_6 | 558 | 26791 | 554 |
| zeta_7 | 568 | 28497 | 564 |
| zeta_8 | 578 | 30233 | 574 |
| meet Box_{1}, then shift left | 580 | 30809 | 3 |

Box_{1} has two words. The same cylinder/pattern finish gives:

| Completed update | g | n | New list length |
|---|---:|---:|---:|
| pi | 592 | 32018 | 588 |
| rho | 614 | 38073 | 6 |
| pi | 626 | 39353 | 622 |
| rho and fixed shift | 648 | 45748 | 6 |
| meet P_pat | 650 | 45756 | 3 |

**Remark1 (root's preliminary count correction, retained).** A preliminary schedule message used620 rather than622 for the pi list at input g=614. The exact rule is g+8, so the list has622 words. This adds two relations at the following rho, correcting the old X_U relator total45754 to45756 and its conditional embedding total49790 to49792. The preliminary numbers were hand-schedule errors, not values from an emitted or audited presentation. The valid weaker E_U580/30809/list3 and corrected X_U650/45756/list3 remain recorded; none of the newer routes silently discards them.

**Remark2 (theta needs the established support).** Theta sigma^-1 is not a generic replacement for Keep_{1}. For a finitely supported f with f(1)=0 and f(3)=1, theta sigma^-1 f retains value1 at site1, whereas keeping only site1 of f and shifting gives zero. Accepted's prior Init restriction excludes this counterexample.

**Remark3 (the two-relator boundary is not full-F transport).** In(1), beta belongs to F but beta^t=w has nontrivial retraction to Free(d,e), while every F element has trivial retraction. Thus F^t=F is false. Formula(2) is the required proof, and it uses the exact accepted intersection with the associated source subgroup. Also v=0 would give w=1 and fail the rank-two hypothesis; the fixed pattern has nonzero v. These limitations are retained from the separate transducer lemma.

## 7. Conditional embedding counts, parity and unresolved materialization

The frozen gap note, Section3, gives the unpruned subsequent embedding/naming formula

    r_cond=n_H+6g_H+k_H+133.                            (3)

All four finishes preserve its named-F3 normalization. Substitution by hand gives:

| Valid finish | Ambient(g_H,n_H), list k_H | Conditional relation slots |
|---|---|---:|
| two-relator transfer | (499,17678),3 | 17678+2994+3+133=20808 |
| full-F decoder then cylinder | (569,30682),3 | 30682+3414+3+133=34232 |
| theta then cylinder | (589,34267),3 | 34267+3534+3+133=37937 |
| corrected Keep then cylinder | (650,45756),3 | 45756+3900+3+133=49792 |

These applications retain the gap note's parity correction. The pattern uses the normalized even-a/odd-b convention; the primary source's inconsistent odd-first display is reconciled by the fixed generator relabelling x=b,y=a and corresponding relabelling of embedding images. The two free words are not declared identical, and relation-slot counts do not change under that relabelling.

This note counts the entire specified shared presentation schedule, conditional on the imported affine/persistent/operation-identification premises and the proved local transducer. It does not furnish the actual499 generator names,17678 literal relators,three final subgroup words,embedding images,two-generator presentation or signed/positive matrix alphabet. In particular20808 is not recorded as an instantiated universal r in the positive7 arithmetic compiler, and no numerical universal arithmetic bound follows here. Existing arithmetic examples and general formulas remain separate artifacts.

**Open question1 (complete literal compiler, credited to root).** Materialize the exact schedule with deterministic fresh namespaces, all marker maps and carried shift/A words, every cached list and all literal relations. Authenticate and independently audit that output. Then carry out and audit the named embedding with its parity convention, retaining the exact matrix data before instantiating the arithmetic compiler. Count correctness alone does not replace this missing word-level evidence.

Root supplied the global typing, persistent schedule, affine pattern/cylinder and theta shortcut. Aristotle supplied the affine/persistent proofs and both direct-decoder proposals; Pascal supplied the affine-machine/global-type proof and scoped independent challenges. Riemann's work here is the full hand schedule, recurrence arithmetic, explicit reduced-word transducer challenge and preservation of all weaker routes/corrections. No scientific helper, expander, instruction evaluator, group-word computation, saved-array evaluation, degree propagation or build was run. Only inert text and fresh byte/read-span metadata are used.

Root and Aristotle each read the complete230-line mathematical draft and independently passed every recurrence/table, the417+46*6 union count, cached typing, Block9/support, reduced-word transducer proof, all weaker finishes, four conditional totals and the retained two-relation correction; neither requested a correction. The separate frozen component notes retain Pascal's semantic and local-transducer challenges without attributing a new whole-schedule read to him. This schedule and its byte/read-span receipt are now frozen. Final edits after the full challenges change only this status/provenance. No complete universal word list, embedding or matrix alphabet is materialized or independently audited by this packet.
