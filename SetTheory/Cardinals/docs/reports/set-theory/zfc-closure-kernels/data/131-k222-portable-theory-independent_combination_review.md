# Independent mathematical review: merged equality and seed request

Reviewed 2026-10-20. This review concerns theory compatibility, not a newly compiled transition table or an end-to-end proof-assistant theorem.

## Verdict

The merged equality-row reduction and the seed-request reduction compose at the level of native deductive theories. No new interpretation of equality, no stronger helper, and no new K consistency theorem are needed for that composition. Source/compiler/runtime certificates must still be regenerated for the combined bytes.

The essential modular fact is that the equality transformation is independent of every K instance. Its proof uses only the retained rows rho1, rho2, rho6, the rho8/rho6-derived classical propositional calculus, MP, and closed-theorem generalization. Thus its proof is valid with the output-root, seed-request, or already-calibrated conditional core in the bundle.

## Exact combined formulas

Let I,Q,R,E denote the exact numerical constructors; N(t)=I(t,1), F=1. Let i=R(a,b), e=E(a,b), and

G(a,b,c) = I(E(c,a), I(E(c,b), Q(R(a,b), E(a,b)))).
H(a,b) = I(E(a,b), Q(R(a,b), E(a,b))).
V(a,b,c) = I(R(a,b), Q(c,R(a,b))).

In the witness-request package, let w,h be its exact request and hereditary closure codes, and J=Q(c,I(h,N(w))). Its existing bundle is N(I(V,I(H,J))). The simplest helper-deleted version is N(I(V,J)); reordering conjunctions or using the equivalent And(core,V) requires literal AST/emitter checks but no new theory argument.

From the retained classical bridge, old_bundle implies new_bundle and H, and new_bundle together with H implies old_bundle. This statement is valid at the literal numerical level; J is merely an opaque formula for this proof.

## Equality proof checked for circularity

1. Quantifier monotonicity follows from theorem GEN and rho2. Existential monotonicity follows by contraposition.
2. Seriality Q_i A -> Ex_i A uses rho1(i,i), not equality reflexivity: apply quantified/existential modus ponens to Q_i(A -> (Eq(i,i) -> A)).
3. Seriality at Q_i A followed by rho6 gives Q_i Q_i A -> A.
4. For x, put z=R(x,x). G(x,x,z) contracts to Eq(z,x) -> Q_z Eq(x,x). Existential monotonicity and rho1(z,x) give Ex_z Q_z Eq(x,x); rho6 yields Eq(x,x). This does not use old rho7 or H.
5. G(a,b,a) and reflexivity yield exactly H(a,b), including diagonal and zero-label cases.
6. Generalizing H at its own binder and applying rho2 yields Q_i e -> Q_i Q_i e. Step 3 then gives Q_i e -> e.
7. Compose G with step 6 to recover literal old rho7(a,b,c).
8. Conversely, old rho7 and H derive G by propositional composition.

Only closed theorem derivations are generalized; formulas can contain free labels. No open-hypothesis GEN, equality substitution rule, or raw-falsity freshness rule was smuggled in.

Freshly regenerated the supplied finite proof DAG and independently replayed it using the separately implemented reviewer: 315 nodes, 290 formulas, 33 roots. Digest 622653bffd6b72e952344a8439d012c3bd6ee33917880830196bc175d89f03c5. Forward roots reject OLD_H and OLD_RHO7 leaves; reverse roots reject G leaves. These are finite syntactic checks accompanying the uniform proof, not a new kernel endpoint.

## Source obligations that must not be lost

- G replaces the independent logical rho7 row and must be enumerated for every numerical triple. Do not put G behind the K gate.
- The K bundle retains exactly the gate c != a and c != b. Disabled cases return the original truth code 0.
- Every old H(a,b) can be extracted by selecting any enabled c, such as max(a,b)+1; this step needs no truth of K and uses only bundle projection.
- All other logical rows, MP, theorem GEN, proof enumeration, cutoff and seed remain unchanged, or must receive a separate proof.
- Removing H from the source does not license removing the H/equality interpretation proof from the dependency chain: it is now derived via G.

## Seed-request calibration and native edge cases

The inherited seed proof is supported by actual pinned source definitions/theorems inspected in KPSeed.v and KPrimeCore.v: output_root_to_seed, kprime_core_to_seed, seeded_core_to_kp0. KQuotZFTransfer.v supplies K0_ZFc_inconsistent. These justify finite-proof transformations, not an assertion that ZFC contains a set model of itself.

For the upper direction, the exact numerical decoder must handle all enabled triples. The private label c is free-variable-fresh in D(c), including c=0 (closed exceptional tautology with bound zero occurrences) and c=1 (R(0,0)). Distinct active roles use the inherited abstraction lemmas. If a=b, the subset antecedent becomes tautological and shadowing changes the matrix to a unary psi. Split on whether any psi witness exists: empty C in the negative case, a singleton containing a witness in the positive case. Splitting only on psi at the initial environment would be wrong.

For the lower direction, first translate equality by membership indiscernibility, then pad the translated matrix and choose c=enc(not not theta(f)). Choosing c before translating equality would leave newly introduced names uncontrolled. The outer seed template has no primitive equality, so it commutes with theta. The merged G transformation recovers the literal H and old rho7 needed by this existing adapter; it does not alter the adapter.

Native negation is relative to F=1=R(0,0), but the total decoder recognizes I(x,1) as genuine named negation. At output binder zero, do not assert raw syntactic freshness of F. Use the already calibrated decoder/relative-falsity bridge.

## Remaining boundary

This review approves only the modular theory composition. It does not establish the combined emitted AST, all-natural macro execution, enumeration coverage, a count below 223, contextual decoder folds, or unbounded binary runtime. Those must be checked against the exact eventual source and table.

## Exact 222-candidate source audit completed

The subsequent independent source audit passed for source SHA-256
cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e.
The source has 4,744 primitive occurrences, 208 distinct internal subtrees,
maximum depth 36, and maximum zero run six. Relative to the pinned 4,799-leaf
baseline, precisely the old rho7 interval [486,786) and old K-bundle interval
[2541,4618) are replaced. Their new lengths are 409 and 1,913. Every other
primitive is unchanged. The checker constructs expected ASTs independently,
checks symbolic postfix execution, links all optimized arithmetic macros by
all-register bisimulation, and compares every complete guarded CFG target
against a separately spliced closed-block reference. Both arithmetic and
interval CFG resolvers agree, with 6,167 guarded successor checks.

Six negative controls also passed: instruction mutations in the unaffected
prefix, G, and seed bundle; changing G's binder constructor from R to Q;
restoring the deleted H; and a primitive-order-preserving nonclosed
reassociation. The last reaches and fails the full CFG comparison. The checker
reports but does not require a preselected candidate source hash.

These results discharge the source-binding boundary identified above. The
binary table, bootstrap and unbounded runtime still require their own separate
certificates. Portable checker files and exact receipts are under
portable222/verification and portable222/certificates.
