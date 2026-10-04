# Independent manuscript review of Report 67

Review date: 4 October 2026 UTC. Review scope: the complete article, its mathematical transcription and semantic boundaries, attribution, and visual inspection of every rendered page. This is a new review written outside the candidate release and all frozen scientific inputs.

## Verdict and exact candidate

**PASS on the final manuscript and all 24 final rendered pages.** The mathematical review passes, conditional on the stated pinned constructive Pell theorem pair and, only for physical transport, the separately retained physical compiler theorem. No substantive mathematical correction was found. Four local presentation corrections were requested or agreed during review; all are resolved in the final pinned candidate. There is no remaining required correction within this review's scope.

Candidate root: `/workspace/shared/report67-power-reductions-release-20261004`.

The initially reviewed candidate had PDF SHA-256 `37005d94aa9a6037c35f64638a2443fdb471aff9cee8eb56c1529c32566fa58d`, flattened-source SHA-256 `44c9d952d39b0538855780fe6f3a420232b63f7fda1f9f33886f72ff732ccb35`, and manuscript-pin-map SHA-256 `fae9d4bcd2e199f70a136f73ac42f22aa21e4c368ac6ff2c1878aa5640a00822`. All three were checked by a read-only hash command. Its 24 bootstrap PNG pages were inspected individually.

The final candidate has PDF SHA-256 `20ef1b64f4a87496bd6c64a72cb760d9d555f4d0d459f84b57cdfd910e1dd800`, flattened-source SHA-256 `fa316a86ba5aa9ddaf15127b52addc3b3f27e85118b1caa1bece85c941caa511`, and manuscript-pin-map SHA-256 `99a8beb275e70e66aa4426f1497ccad79a2a4ed13617cce7e6d912ec98a11656`. These were checked directly, and each of the eight module hashes agrees with the map. All 24 PNGs in `/workspace/shared/report67-author-work-20261004/locked3/pages` were individually reopened and visually inspected after the author's repairs. A direct byte comparison confirms the candidate PDF equals the PDF belonging to this render. The review does not transfer initial visual acceptance merely on the author's unchanged-page assertion.

## What was independently read

All eight manuscript modules were read completely: the main article and power, elimination, twelve-leaf, compiler, degree, composition, and scope modules. The full relevant scientific proofs were read as text: baseline POWER and elimination variants, twelve-leaf proof, exact-degree proof, bounded compiler, and the retained native-gap, trace, physical, POWER58 and POWER60 dependency proofs. Repeated copies of the same proof are not separate mathematical evidence. The relevant locally pinned Lean header, recurrence, theorem declarations and constructive branches were inspected as text. The complete three accepted mathematical AUDIT.md dossiers were read, as were their scope/README records and pertinent preserved receipts.

The review distinguishes this fresh proof/transcription review from historical exact-expansion evidence. No scientific checker, author scientific program, upstream implementation, Lean, native-machine interpreter, physical simulator, or saved schedule was executed. No candidate or frozen input was modified by this reviewer. Read-only shell listing, text inspection, hashing, source comparison and image viewing were used; newly written review records are confined to this external review directory. The author made the reported manuscript repairs separately.

## Mathematical findings

### Positive domains and the 26 to 22 normalization

The 22 leaves are exactly thirteen direct positives, two shifted Pell-parameter leaves, and seven natural adapters. Zero aliases use positive leaf 1. The fifteen residuals agree with the retained construction, with the four signed quotient pairs replaced by single natural quotients.

The sign argument is noncircular. The first two Pell norms and v=y²q_v with q_v≥1 imply u≥alpha and u≥x. The residue lemma permits the endpoint residue=modulus. Its applications establish the first three quotient signs. The auxiliary norm gives alpha>w≥b, and the independent square difference x²−[y(alpha−b)]²=(2alpha b−b²−1)y²+1>0 makes h=x−y(alpha−b)>0 before the final congruence is used. Because 0<bo<M, that congruence forces its quotient nonnegative too.

The forward map takes differences of each old pair and then restores the new positive adapter. The reverse map sets the first natural alias to zero and the second to its quotient, hence old positive leaves 1 and q+1. It is a section, not an inverse on every old tuple. Common shifts must be added to both members of a pair. The corrected wording reflects this.

### Imported all-exponent semantics and positive completeness

The retained Lean bytes have SHA-256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`, matching the article's pin. They identify mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, file `Mathlib/NumberTheory/PellMatiyasevic.lean`, and declarations `Pell.matiyasevic` and `Pell.eq_pow_of_pell`.

The index is C, not C−1. The first nine residuals give the nonzero Pell branch; y≥C≥1 excludes its zero case. The last six specialize the power theorem to (n,k,m,t,z,a)=(b,C,bo,M,g,alpha). Thus b^C=bo and cancellation gives o=b^(C−1). Natural subtraction is translated correctly: A−B=1 for naturals means A=B+1, and alpha>b separately makes alpha−b an ordinary nonnegative difference.

Constructive completeness recovers every stated domain: g cannot be zero, x/u/s are positive Pell coordinates, v>0 and y²|v give q_v>0, beta>1 and its residue give q_b>0, the t congruence excludes t=0, and M>bo gives J>0. The positive-index shift includes exponent zero without allowing zero positive leaves. This conclusion remains conditional on the named theorem pair; no fresh formal verification or remote Git authenticity claim is inferred from the local pin.

### Bijective eliminations to sixteen, fourteen and thirteen leaves

The sixteen-leaf reconstruction uniquely restores w,y,beta,M,x,s. The retained norm yields alpha>w≥b, and the retained modulus residual yields M=bo+J>0 before x and s positivity are asserted. Thus the six removed positive domains are genuinely recovered. The fourteen-leaf substitution restores v=y²q_v>0 and t=C+4yq_tau>0. Both maps are inverse to restriction on full solution tuples at fixed arguments.

For thirteen leaves, A_*=d alpha, X=dx and S_*=ds in the forward direction give the listed scaled residuals. Conversely alpha=A_*/d is a positive rational whose square is integral by F6. The reduced-fraction lemma makes it integral, and the same norm gives alpha>w≥b, restoring alpha_plus>0. Modulus and positive x,s follow, and division uses only nonzero d or d². The article correctly notes the independent simpler integrality implication from F4; it does not make the later twelve-leaf proof circular.

### Strict twelve-leaf recovery and exact image

The direct leaf q_alpha is strictly positive, while only six other quotient/slack aliases use minus-one adapters. The five H residuals match the accepted lean formula; H1 carries no redundant q_alpha² factor.

First H5 gives integral positive alpha independently of u. Then H2 gives rational u=U/(d q_alpha) with integer square. The rational-square lemma proves u integral. Its norm yields |u|≥alpha, and beta=alpha+u q_alpha together with integer q_alpha≥1 excludes negative u; zero is also excluded. All restored x,s,v,t, parameter adapters, and the old q_alpha adapter meet their domains. Every one of the old fifteen equations is supplied either by a divided residual or a definition.

The map is precisely W13+↔W12, translating q_alpha_plus to q_alpha_plus−1 and restoring u uniquely in the reverse direction. W13+ is the subset q_alpha≥1, equivalently beta>alpha. It is neither a literal coordinate projection nor a bijection with all W13. The beta progression at k≥1 establishes existential completeness from any old witness without asserting injectivity of that preliminary step. The two nontrivial polynomial identities against F4 have the correct factors and signs.

The zero-quotient boundary example with q_v=2 has accepted output o=1 but would require u²=1153, between 33² and 34². It demonstrates failure of the enlarged-domain reconstruction, and is correctly not described as a false-output counterexample to the theorem.

### Exact module degrees and infinite full fibers

Every stated residual-degree list is consistent with the literal substituted formula, after all positive adapters and before constraints. Fixed/variable SOS degrees are 12/12, 12/12, 16/16, 16/20, and 20/24 for 22,16,14,13,12 leaves respectively. The coefficient-one monomials use the unique residual containing the relevant g or q_v leaf. Their factor restrictions exclude hidden cross-term cancellation. The last two variable-base conclusions are not incorrectly inherited from fixed-base degrees, and an external B with b=B+1 is excluded from module leaf counts explicitly.

The Pell recurrence proves its norm invariant, positivity, and values X_n(1)=1,Y_n(1)=n. Congruence preservation supplies the beta progression. Nonnegative reconstructed quotients follow from the same residue bounds, and q_b,k=q_b,0+u k strictly increases. This retained leaf proves infinitely many distinct complete tuples in every accepted module fiber, including after all eliminations and after restricting to k≥1 for twelve leaves. The explicit C=o=1 fixture and its endpoint are coherent.

### Bounded compiler, exact interpolation theorem and costs

The clipping induction uses T−t>0 at entry times t<T, not at the terminal configuration. It covers loops, initial halt, exact-horizon acceptance and T=0, and does not assert equality of final counters. The smaller-threshold example is a clipping fact, not an arity or degree lower bound.

The scaled Lagrange basis has value c=(N−1)! at its own node and zero elsewhere. The six residuals enforce exactly the unique clipped node and the two positive slacks. Empty/full acceptance sets and zero/duplicate residual slots are handled correctly. At T=0 the two displayed possibilities have exact degree two and nine supported monomials.

The reflection identity, finite-difference tail formula, even-K strictly negative boundary sum, and odd-K root filter are correct. The phase sign and factor 2^(n+1)/K agree after conjugate pairing. The stated inequality puts all sampled angles in the strictly decreasing positive range, so the alternating sum has the asserted strict sign. Odd K is explicitly qualified by K≥3 and K=1 is separately treated; V=z+K−KU is likewise limited to K≥2.

The classification residuals alone attain top degree 4 delta_K. Their entire top homogeneous sum is (1+K^4)a_K^4 j^(4 delta_K), with positive coefficient independent of the acceptance subset. This proves d_T=2 at zero, 4(T+1)²−4 at positive odd T, and 4(T+1)²−8 at positive even T. The support types are disjoint and sum to 16 delta_K+11, a ceiling rather than an equality.

The coefficient norm bound 66 Lambda^4, coefficient magnitude-bit bound, O(N² log(N+1)) expanded binary storage, at-most-NT native transitions to construct the N Boolean table, and O(N³) integer arithmetic generation bounds are properly paid and qualified. They are not bit-complexity, polynomial-in-log(T), optimal storage, or faster bounded-decision claims. Varying T changes coefficients and degree; the report does not internalize the table into one fixed unbounded-halting polynomial.

### Paid native-gap and finite-trace ledgers

The gap equations have positive denominators on any solution and enforce the encoding as part of the predicate on all positive triples. Two shifted counters, both complete modules including their outputs, and the three compiler witnesses yield 2 ell+5 witnesses; the two gap, 2r_ell module and six compiler residuals yield 2r_ell+8 slots. Every row of Table 2 is correct, including the final 29 witnesses, 32 total variables and 18 residuals. Independent module degree certificates and the compiler's top term prove the exact maximum degree, including ties. The examples d0=2,d1=12,d2=28,d3=60 are correct.

Fixed gaps uniquely determine p,q and hence A,B, then j,r,s; this is only projected uniqueness. Varying the retained beta family in one module preserves that projection and proves infinite complete fibers.

The finite trace has TE selectors plus 2T next counters. Its slots are TE selectors, T one-hot, 2T updates, TZ zero guards and T+1 state links: T(E+Z+4)+1. Positive successor counters enforce the positive decrement guard, and one-hot selection prevents an illicit mixed update. A unique deterministic path fixes inactive selectors too. The single nonnegative halt-loop sum excludes early halt for T≥1, adding one residual only. T=0 uses the stated constant residual. Adding paid decoding gives exactly the displayed trace witness, slot, all-variable and module-dominated degree formulas.

## Attribution and semantic limits

The retained source header credits Mario Carneiro and Apache 2.0, and the original header, license and notice are present. The article credits the exact theorem pair rather than claiming the established Pell exponentiation theorem as new. The official Dudenhefner publication record confirms author/title/volume/DOI and its instruction-model warning. The official DLMF section confirms the cited elementary Lagrange formula. The official Pąk–Kaliszyk paper confirms the title, authors, publication details, and its explicit discussion of parameters, unknowns and hidden subrelation unknowns (sections 3–4). These are appropriate bounded citations, not support for a priority or minimum-variable claim.

Sources inspected on 4 October 2026: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.16 ; https://dlmf.nist.gov/3.3#i ; https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2022.26 . The DOI redirect for the last initially failed in the web tool; its official publisher page and linked PDF were accessible.

The physical section copies only the inherited encoded-input interface: five live signals, fixed ordered sections, invariant D, at most 32 binary collisions and duration between D and 10D per nonhalting transition. It explicitly conditions transport on that theorem, distinguishes instruction horizons from collision horizons, and treats halt padding as arithmetic. It does not classify arbitrary unencoded executions or establish new universality. This review checked faithful use of that interface, not a fresh independent physical audit.

The article consistently excludes novelty, priority, minimality, optimized gates, small-height Pell witnesses, finite-fold complete fibers and a fixed-polynomial unbounded-halting claim. Historical independent audit counts are accurately described as evidence already obtained, not tests performed by the article build or by this review. Release-tool reproducibility and archive authentication are outside this manuscript review's independent execution scope; they require their separate release-tool review and final receipts.

## Corrections identified before final acceptance

1. Six TeX superscripts `^{,8}` in elimination.tex and twelve.tex rendered a stray comma before an exponent 8 in equations (18), (25), (26). Required replacement: `^{8}`.
2. Section 2.2 said a common natural shift was added to “either member” of each old pair. Required wording: “both members”.
3. Figure 1's coordinate-positioned explanatory text overlapped W12 in the lower arrow row. Required repair: place the explanation wholly below the diagram, preferably in ordinary caption/prose.
4. Table 2 interrupted the sentence “The module … sums have degree” on initial page 20. Explicit paragraph boundaries were requested so the table sits between sentences.

The author also moved the contents to a dedicated page. This is an organizational improvement rather than a mathematical correction. All four repairs and the new contents organization were inspected in the final source and final raster pages. Equations (18), (25), (26) have ordinary exponent 8; “both members” is correct; Figure 1's caption no longer intersects its nodes or arrows; and Table 2 is between complete sentences.

## Final presentation acceptance and dossier

The per-page record is `PAGE_REVIEW.md`; exact final PNG hashes are in `PAGE_SHA256SUMS`. Every page is legible, with no clipping, overlap, missing mathematical glyph, obstructed equation number or broken table. The complete final PNG pass was performed on all pages rather than only changed pages. The compact diagram is now clear and correctly distinguishes normalization, three bijections, inclusion and strict-domain recovery. Both resource tables and the residual-degree and support tables are readable.

The final build log was inspected as ancillary presentation evidence. It has no overfull-box or undefined-reference diagnostic. It records the expected disabled-shell-escape epstopdf warning and two underfull-box warnings in the bibliography paragraph; the final references page was visually inspected and is legible. Those warnings are not hidden or treated as a scientific failure. The author build receipt is supporting provenance, not an independently rerun build in this review.

`CANDIDATE_SHA256SUMS` pins the final PDF, flattened source, map and eight modules. `SCIENCE_TEXT_SHA256SUMS` pins the retained text/manifest/license scope used for comparison, including duplicated copies; it is an inventory, not a claim that every duplicate is new independent evidence. `RECEIPT.json` supplies the machine-readable verdict and exact scope. `MANIFEST.sha256` hashes every other file in this review dossier and deliberately excludes itself. Its externally reported digest authenticates the dossier. No scientific execution is needed to reproduce its byte checks.
