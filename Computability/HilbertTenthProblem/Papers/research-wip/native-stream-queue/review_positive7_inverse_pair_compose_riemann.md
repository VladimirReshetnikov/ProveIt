# Independent review of the complete inverse-pair positive7 source

The complete substitution passes: it removes exactly144 multiplications and preserves the entire final polynomial on the same supplied integer coordinates, for the inherited fixed coefficient recipe. Consequently the same positive witness tuples and ordinary-input projection are preserved. No correction to the new author packets is requested.

With ell=62+10r and lambda=floor(log2 ell)+popcount(ell)-1, the certificate is (276+56r+lambda)M+(550+74r)A. Its unchanged23-comparison finalizer yields (299+56r+lambda)M+(595+74r)A, or894+130r+lambda operations, with96+10r positive witnesses. The formal r=0 polynomial has903 operations. The actual universal presentation remains unmaterialized, so this is not a numerical universal bound or an improvement of general84.

## 1. Frozen artifacts and review scope

| Artifact | SHA256 |
|---|---|
| positive7_inverse_pair_compose_root.md | d9c91919e240c1a2e9256561b28be16e05f35cead962ec1b4e4f9ecda52fcff3 |
| positive7_inverse_pair_compose_root.py | 2758522766ea4c2fba3e8d8a0800e72e0063b533990596f84e879b6171a8e47a |
| positive7_inverse_pair_compose_root.json | 182a9dc7a2efe4428a096263c1872bfbb5df264a79b50851de0b7b7c82b6a4f1 |
| positive7_inverse_pair_action_pascal.md | 3129c00815a83267220dc45fffccf7fa3b05e2523706461221df288fda52a3a2 |
| positive7_inverse_pair_action_pascal.py | 9e079cbef18bc2895113cb42149343fda79dcb6fab2182456f3e1fca325b2dbf |
| positive7_inverse_pair_action_pascal.json | b830a0644ae0b5ba8b04273a3ac445437af0af2c0b522c1caf3078203f7eab02 |
| review_positive7_inverse_pair_action_aristotle.md | 740f9df909d936024a8bc22136c713b60befff1d631aa557f585b6276e5ac3b8 |
| review_positive7_inverse_pair_action_aristotle.json | 908e0f9773b3c17b81d6413a80a09727495421771dd11f481224f7c7acd09f67 |
| positive7_complete_sparse_compiler_root.json | 2c7e2b2d2345150644b47701eed9434eabad7159f0067154b6666750e2b48e3a |

I read the full105-line new primary proof,185-line composer,322-line local proof,271-line local emitter, all198 local rows, and Aristotle's full final94-line local review. The complete parent was independently reviewed in the preceding packet, including all3,789 rows and the support-containment correction. This review independently checks all3,357 rows of the composed graphs as literal records and graph structure. It does not execute/import either emitter, evaluate a saved array, propagate degrees or infer identities from sampling.

## 2. Independent hand challenge of the exact local identity

The congruence representation on G(v)=[[v1,-v2],[-v2,v3]] gives S(PQ)=S(P)S(Q). Thus

    S(U)(x,y,z)=(x-2y+z,y-z,z),
    S(U^-1)(x,y,z)=(x+2y+z,y+z,z),
    S(V_t)(x,y,z)=(x,y-tx,z-2ty+t²x).

For each fixed conjugator C, (S(CPC^-1)-I)v=S(C)(S(P)-I)S(C^-1)v. This applies to the plus and minus slots independently; their inputs are arbitrary integers. The b and z conjugacies in the proof match the actual signed macro matrices from the predecessor. For example UV_tU^-1 has rows (1+t,-t),(t,1-t), while V_tUV_-t has rows (1-t,1),(-t²,t+1). Conjugating the latter by U gives rows (1-t-t²,(t+1)²),(-t²,t²+t+1). These handwritten identities identify the specified t=12,4,8 matrices and their inverses without evaluating stored source or coefficient arrays.

The decoder Q^-1D0 has coordinates (Z1-Z4,Z2+Z4-2Z7,Z3+Z4-2Z7,Z4-Z7,Z5+Z4-2Z7,Z6+2Z4-4Z7). With u=Z4-Z7 and h=u-Z7, the author recovers exactly the coordinates its differences consume. The a schedule omits Z1 and the b schedule omits Z6; z consumes all seven. No omitted selected field is introduced, and all52 existing paired ports remain live.

For the upper inverse pair the increment is (2(l_minus-l_plus)+m_plus+m_minus,m_minus-m_plus,0), costing five additions after the needed decoder values. For the lower12 pair it is (0,12(x_minus-x_plus),144(x_plus+x_minus)+24(y_minus-y_plus)), costing3M+4A per block. For z, the inner V_-t supplies L=tx+y and M=t²x+2ty+z with2M+3A. Applying the upper pair and then V_t yields (A,D-tA,t²A-2tD), with a further2M+3A per block. The displayed signs, independent-slot inputs and paid doublings all check.

The a body costs0M24A; b before its final first-block chart costs6M26A; each z before that chart costs12M50A. The b/z first-block outputs share the same S(U). Summing before that map takes5A, applying it once takes4A, and adding the already final-basis a outputs afterward takes2A. The second block has3,4,3 terms, costing7A. This gives30M168A=198 for all six outputs, replacing174M168A=342. In particular a is not accidentally transformed by the shared chart. The c output is the existing joint_C0 register, so its alias is a free data movement, not a missing operation.

The complete198-row local source was read against these instruction patterns. An independent static check confirms its five stage cuts, constants4,8,12,24,144,52 supplied names, six-exit order, unique definitions, topology and full backward liveness. Its compact source digest is cbbbf4e41204dce42aeb3b6ec379bba34aea5cb162cb42269e5a938077d766d8. Arithmetic equality comes from the hand proof, not this structural check. Numerical derivation of the predecessor's48 coefficient rows remains the previously pinned evidence rather than a repeated scientific execution.

## 3. Whole-source binding and complete fanout closure

The static audit authenticates the parent and local input pins, then inspects every child row. In each graph the prefix before the increment cut is literally identical to the parent's prefix. The next198 rows are literally the entire pinned local source in its original order and on the same selected_SLOT_PORT names.

Every old relator product is retained literally: same name, operation, signed fixed role and selected coordinate. For each of the last three increments, the child adds each product to the already nonempty local paired accumulator, paying one addition per product. There are24r relator products and24r such additions. No zero-role product is pruned and no new witness or parameter is introduced. The replacement cut costs (30+24r)M+(168+24r)A, versus (174+24r)M+(168+24r)A.

The full external-consumer census of the removed cut contains only its six final increments. The a,b,c,e,f exits feed their designated five-term sum and their matching history-plus-increment rows. The d exit feeds only five_d and scaled_eight_d. No removed internal decoder, product or partial sum escapes the cut. The child rebinds exactly these operands to the six new exits. Its121-row suffix is otherwise literally identical, including the fused action, recurrence right sides and the complete finalizer.

The c alias joint_C0 also has the two local consumers joint_G1 and joint_G2 inside the new cut. These uses are explicitly counted by the audit and do not invalidate the six-exit boundary. The other externally bound names for r>0 are the final paid relator accumulators. Their precise names and operand-side consumer lists are recorded in the JSON.

The supplied coordinate lists and domains, all lane records, initial/terminal fields, ordinary parameter x, all nonincrement ports, comparison endpoint names, fixed numeral roles and output name are unchanged. All64 native rows are literally unchanged, as are their15 comparison pairs. The source still has one global comparison and seven recurrence comparisons, totaling23. P*F1 still has exactly its recurrence1 and recurrence7 consumers, while every scaled action output still has only its recurrence residual as consumer. There is no extra radix multiplication or lost unscaled-action consumer.

Both the certificate rooted at its comparison endpoints and the full polynomial rooted at polynomial_sum_22 are topologically closed. All applicable rows and supplied coordinates are live; every fixed role remains live. Definitions are unique, and all prefix/local/suffix name bindings close without a collision. This is syntactic liveness, consistent with charging uniform fixed products even if their eventual numeral is zero.

The six local polynomials equal the six former paired increment polynomials for arbitrary integers. Adding identical relator products preserves equality of the complete cut exits, regardless of their reassociation. The authenticated suffix substitution therefore proves equality of every subsequent polynomial, including every residual and the final sum of squares. The positive supplied domains and coordinates are identical, so the positive zero sets correspond by the identity map. This source change does not need a new native completion or a new carry proof; the already reviewed parent projection applies verbatim.

## 4. Ledgers and static example scope

| Saved r | Prefix rows | Old/new increment rows | Suffix rows | Certificate M/A/total | Polynomial M/A/total |
|---:|---:|---:|---:|---:|---:|
| 0 |584|342 /198|121|285 /550 /835|308 /595 /903|
| 1 |664|390 /246|121|339 /624 /963|362 /669 /1031|
| 4 |912|534 /390|121|509 /846 /1355|532 /891 /1423|

All3,357 saved child rows are accounted for by these disjoint comparisons. The positive witness counts are96,106,136 and named fixed-role counts4,28,100 respectively. The count-only records for r=2,3,8 have full polynomial totals1162,1293,1944; they are inherited formula consequences, not extra saved arrays.

The all-r arithmetic count follows from the parent's independently checked grammar and the exact144M/0A cut delta. Its factored increments plus unchanged fused postprocessor cost (42+24r)M+(189+24r)A. Everything else is unchanged, including the paid hats, unbounded-history geometry, pack chains, prescribed native scale and23M45A finalizer. The all-r result is not inferred from the three finite source shapes.

## 5. Preserved boundaries and remaining questions

**Review remark 1 (valid earlier136 saving).** The initial30M176A local schedule was correct and saved136 operations. Sharing the first-block chart removes eight additional additions, yielding the final30M168A cut and144-operation saving. These are successive valid schedules, not two savings to add again.

**Review remark 2 (signed factorization is not a longer positive word).** The proof factors a fixed signed macro-letter inside one arithmetic cut. It does not expand that letter into separately lifted positive letters. The identity-letter example D0L(I)=8D0 versus D0L(I)^2=64D0 explicitly refutes that replacement. No extra word, selector or macro controller is introduced here.

**Review remark 3 (parent support correction and sparse mass scope).** Retained relator ports contain the nonzero support; equality with that support is not required. An identity relator has zero difference support while the uniform four-port template and its charged zero products remain. The parent review's numbered correction stays applicable. Likewise Ztot=S remains false for sparse selections: the a+ cell on seven ones retains6 rather than7. Its valid Ztot<=S completeness argument is inherited. These are already recorded parent boundaries, not new source failures.

**Review remark 4 (which witness correspondence is proved).** The earlier dense-to-sparse change preserved ordinary-input projection and could require new native witnesses. The present change is an exact polynomial substitution between two sparse sources with identical supplied coordinates, so it preserves the same positive tuples. No dense/sparse same-tuple assertion follows from this stronger local substitution.

**Open question 1 (materialized universal data).** The current composition resolves the local packet's emitted-wrapper and complete-binding question. The actual universal presentation, numerical r and fixed coefficient materialization remain open. Neither the formal903-operation shape nor the symbolic894+130r+lambda formula is a new numerical universal bound. External group/native foundation proofs remain inherited; degree and optimality are not claimed.

**Open question 2 (further sharing).** Additional inverse-pair, relator, positive-lift or hatted-global sharing remains a separate research direction requiring an exact local identity, complete consumer closure and a paid whole source. This review includes no prospective saving. All author, parent and coefficient artifacts remain frozen and unchanged.
