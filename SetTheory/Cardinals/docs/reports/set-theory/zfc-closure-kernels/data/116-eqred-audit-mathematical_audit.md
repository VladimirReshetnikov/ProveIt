# Independent audit: membership-defined equality and the ZFC comparison

## Verdict

The proposed replacement-equality argument is mathematically sound, with the scope below. I found no remaining logical gap in its **ordinary external consistency comparison**. This audit independently checked the uniform construction, rather than extrapolating from the supplied finite roots.

Let H_sym have K, S, positive canonical V, rho1–rho6, primitive Eq symmetry, full gated membership vacuity, exact CP/native GIC, MP and closed-theorem GEN. Let H_7 retain rho7 instead of primitive symmetry. Then, relative to the existing ordinary completeness and CP/GIC-to-ZF-to-ZFC theorems identified below,

    Con(H_sym) <-> Con(H_7) <-> Con(ZFC).

Here Con(H) means that the exact relative falsehood F=Rel(0,0), native code 1, is not derivable. The result does not say primitive Eq-vacuity is derivable. It uses a new interpretation of comparison equality.

A smaller logical variant also works: keep original rho1–rho8 and full membership vacuity/CP/GIC, and retain only

    Eq(a,b) -> All(weq(a,b), Eq(a,b))

from equality vacuity. Call this H_eq. Then Con(H_eq) <-> Con(ZFC) by the same argument. Original rho8 supplies classicality, so arbitrary-formula canonical V is unnecessary for this variant. The Eq-only canonical family must actually be supplied; this theorem does not claim it follows from deleting all Eq-vacuity.

These are external mathematical comparisons. This audit has not produced a new Lean theorem, audited the full dependency closure of the old Lean endpoints, or rebuilt them. It has not proved a changed enumerator/blank-tape theorem, certified a new optimized runtime, or obtained a machine with at most 235 states. The direct frontend costs belong to a separate lane and cannot be subtracted from the optimized 237-state machine.

## 1. Exact falsehood and proof language

Use F=Rel(0,0), N(A)=A->F, Ex_i(A)=N(All_i(N(A))), and negative conjunction C(A,B)=N(A->N(B)). Every occurrence of these abbreviations in the proof is literal.

The existing classical bridge uses only K/S, rho1, rho2, rho6 and weak vacuity A->NN(All_i A). For positive V at the actual code of A, double-negation introduction supplies this premise. Thus DNE, explosion, and all classical propositional tautologies relative to F are derivable without Eq-vacuity or rho7. Boolean TAUT leaves in the new replay are consequently abbreviations for finite derivations, rather than additional semantic assumptions.

F is not syntactically closed: its label 0 can be captured. The construction does not assume otherwise. In particular F->All_i F is available by explosion for every i, including 0. Treating F as designated bottom in the auxiliary proof language is a proof interpretation, not a raw membership-atom renaming law.

The tuple generator conflates the designated bottom with the raw atom Rel(0,0). Therefore its `qf_spec` API must not be described as an implementation of arbitrary raw-syntax substitution on every membership formula. For example its renamer fixes the tuple Rel(0,0) rather than changing it to Rel(1,1) when replacing 0 by 1. This is harmless for the E bootstrap: each original non-bottom E-body atom contains its auxiliary label z, distinct from the two endpoint labels, and hence cannot be Rel(0,0). Designated bottoms are fixed. A substituted membership atom can subsequently become Rel(0,0); the required congruence and vacuity derivations still remain valid. General raw substitution is imported only later through the full substitution-free calculus interpretation.

## 2. Uniform bootstrap and absence of alpha/UI circularity

Write L_ab(z) for the conjunction of Rel(z,a)->Rel(z,b) and its converse, and U_ab(z) for the corresponding outgoing-membership pair. Set

    E_ab^z = All_z L_ab(z) AND All_z U_ab(z),  z != a,b,
    k_ab = weq(a,b) = 4*P(a,b)+3,
    E(a,b) = E_ab^(k_ab).

The inequality k_ab>a,b holds uniformly, including a=b=0.

### A. Membership-only fresh vacuity

For a membership-only expression A, with designated bottom, and i absent from all non-bottom labels of A, derive A->All_i A by structural induction.

- A membership atom uses retained gated Rel-vacuity; designated bottom uses explosion.
- From P->All_i P, existential monotonicity and rho6 give Ex_i P->P. Contraposition gives not P->All_i not P. The classical split P->Q iff not P or Q, together with the two inductive hypotheses and quantified monotonicity, then yields implication vacuity.
- For A=All_j B, generalize B->All_i B at j, distribute with rho2, then commute j and i with rho4. The induction assumes i is absent, including bound occurrences, so no internal binder is renamed.

Every generalized formula here is a closed theorem. A GEN under an open assumption is not being used.

### B. Quantifier-free specialization only

For a quantifier-free formula built from membership atoms and a genuine designated bottom, atomic rho3/rho5 plus primitive Eq symmetry give both directions of Eq(x,y)->(A iff A[y/x]). There is no quantified-constructor case and hence no demand for primitive Eq-vacuity. This is an induction on propositional constructors; repeated atomic arguments are rewritten one position at a time.

For x!=y, shuffle the forward implication and generalize at x. Distribution gives

    All_x A -> All_x(Eq(x,y)->A[y/x]).

The object-level existential consequence of rho2 and rho1 then gives All_x A->Ex_x A[y/x]. Membership-only fresh vacuity for the substituted expression, followed by existential monotonicity and rho6, removes that last existential. This proves the needed specialization, including target y=0. The designated bottom is still fixed; it is not claimed to have no raw occurrence of 0.

### C. Auxiliary transport

For z,w distinct from a,b, with z!=w, apply B to the two quantifier-free matrices under z. This yields E_ab^z->L_ab(w) and E_ab^z->U_ab(w). The label w is absent from every non-bottom label of E_ab^z. Apply A to that entire premise, then generalize the closed implications at w and distribute. The result is E_ab^z->E_ab^w. Reverse z,w for the converse. If z=w, use identity.

This proof never applies an unproved general alpha-conversion rule. In particular it does not generalize the premise at its own internal binder.

### D. Exact E rows

For E-vacuity at i!=a,b, choose w=max(a,b,i,k_ab)+1. Transport to E_ab^w, use A at i, and quantify the reverse transport. This gives E(a,b)->All_i E(a,b), including the important collision i=k_ab and the label i=0.

For membership congruence with third label c, choose w above a,b,c,k_ab. Transport first, then specialize the two quantifier-free matrices from w to c. This gives the translated rho3 and rho5 for all coincidences, including c=k_ab and atoms collapsing to F.

For translated rho7, choose w above a,b,c and all three relevant auxiliary codes. Transport E(c,a) and E(c,b) to that common binder. Boolean transitivity of the inward and outward membership equivalences, generalized at w and distributed twice, gives E_ab^w. Transport back to k_ab. Thus

    E(c,a) -> (E(c,b) -> E(a,b)).

No generalization of the two open E hypotheses occurs: the generalized objects are closed tautologies or closed implications. Distribution combines the universal premises afterward.

Reflexivity follows by generalizing membership identity tautologies. Symmetry can be derived by the same transport and pair swapping, or from the exact translated rho7 and reflexivity. These are supplementary: the exact original logical axiom list is already covered by rho1, rho3, rho5, rho7 and gated equality vacuity below.

### E. Primitive Eq supplies the E witnesses

At the literal z=k_ab, canonical Eq-vacuity gives Eq(a,b)->All_z Eq(a,b). Primitive symmetry and rho3/rho5 supply all four required membership implications. Closed GEN plus rho2 puts them under z. Negative-conjunction introduction yields Eq(a,b)->E(a,b). Existential monotonicity and rho1 then give Ex_a E(a,b), with this same literal internal binder throughout.

For H_7 and H_eq, primitive symmetry is first derived from rho7, rho1/rho2/rho6 and canonical vacuity on Eq(x,x). The existing finite certificate has no old atomic-vacuity leaves. Its uniform argument chooses z=weq(x,x), derives Eq(z,x)->Eq(x,x), uses rho1 to obtain Ex_z Eq(x,x), canonical Eq(x,x)-vacuity to obtain Ex_z All_z Eq(x,x), and rho6 to conclude Eq(x,x). Rho7 then gives symmetry. This is independent of the new E interpretation, so there is no circularity.

All fresh-label algorithms above are maxima plus one on a finite set. Their validity does not depend on labels being small or distinct unless explicitly stated.

## 3. Complete logical proof interpretation

Use the genuine-bottom NF syntax and full original `Tarski.Thm` calculus. Define tau by preserving membership, implication and every universal binder, replacing genuine bottom by F and Eq(a,b) by E(a,b).

All logical axiom constructors translate:

- rho8: the classical bridge;
- rho1: Ex_a E(a,b) from section 2E;
- rho2, rho4, rho6: the same native schemas at translated formula parameters;
- rho3, rho5: section 2D membership congruence;
- rho7: section 2D exact ternary E law;
- vacRel: the retained gated row;
- vacEq: section 2D, including auxiliary collisions.

MP and GEN commute with tau by definition. Induction on a `Thm` derivation therefore transports any proof whose theory axioms have provable translations.

This induction has no substitution constructor. It never assumes tau commutes with free-variable substitution or with arbitrary renaming. The change of k_ab when endpoint labels change is addressed precisely where needed by section 2C. Completeness can be applied to the original `Thm` calculus after this interpretation, even though its internal completeness proof uses UI, alpha-conversion and equality-vacuity: their original axiom dependencies now all have translated derivations.

## 4. Exact equality-free theory and actual output-code coupling

Choose the following genuine-bottom comparison theory T0:

1. The bot-free named C(2,3,1), obtained from an actual gated source bundle with matrix F of code 1.
2. For every equality-free ordinary de Bruijn `Form` phi, let f=`Code254GIC.toNamed 0 phi`, p=((f->f)->f), and c=enc(p). Include exactly `namedG 1 3 c p`.
3. IR=All_0(Rel(0,0)->bottom).

Items 1 and 2 contain neither primitive Eq nor genuine bottom. They use relative negation with the raw membership atom F. Therefore tau fixes each of them literally, including every binder and the output coordinate c. The source supplies precisely those matrix/output pairs: no GIC instance at a translated or independently selected output code is used. If the actual emitter uses classically equivalent reordered negative-conjunction trees, their original forms are recovered by propositional equivalence plus closed quantified monotonicity after classicality.

The existing name assignment uses odd free names and even depth-indexed bound names. This is a definition of which source instances to request, not an application of an unproved syntactic renaming rule in the weakened calculus. Padding ensures c>3, so both gates c!=1,3 hold. The finite-tree code inequality ensures c is absent from p. The matrix remains equivalent to phi under every assignment, including the forward and reverse update orders in native GIC.

Finally tau(IR)=All_0(F->F), a generalized identity. Thus inconsistency of T0 would give an H derivation of F by the full Tarski proof interpretation. Con(H) implies consistency of T0. Ordinary completeness then gives a nonempty ordinary relational model satisfying T0 under all assignments. Nonemptiness follows from the actual countervaluation to bottom, not an empty-domain convention. IR makes F false for all assignments.

The exact semantic adapter uses C(2,3,1) for Containers and the literal GIC instances in item 2 for `ProfileModel.ModelsGIC`. It therefore yields `ProfileModel.ModelsCPGIC`.

`Code254GIC.modelsGIC_of_encBundle` is stated with a stronger all-bundles hypothesis. It is not literally a ready-made theorem for our restricted theory. Its proof uses `collection_of_matrix` only at the requested phi, and the `EqualityFree phi` condition in `ModelsGIC` is currently ignored because the original hypothesis is stronger. Restricting those calls to item 2, and using `container_at_of_namedC` directly for item 1, is a valid explicit specialization. No new representation theorem is necessary. This restricted adapter is a remaining Lean implementation task, not a missing mathematical premise.

## 5. Precise existing endpoints and their limitations

All paths below are relative to `research_sub246/source/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

- `TarskiComplete.lean`, `completeness`: full original genuine-bottom logical completeness for arbitrary theories, valid under all assignments; needs the classical theorem predicates supplied by original rho8.
- `Code254Containers.lean`, `container_at_of_namedC`: exact C(2,3,1) extraction, preserving its internal shadowing.
- `Code254GIC.lean`: `sat_toNamed`, `pad_code_gt_three`, `not_free_enc`, `collection_at_of_namedG`, and `matrix_relation` establish the selected actual-code GIC adapter.
- `ProfileModel.lean`, `ModelsGIC`: only equality-free ordinary Form matrices are required.
- `QuotientCPGIC.lean`, `quotient_fullCPGIC`: from a nonempty ordinary EF CP/GIC model, constructs full Form CP/GIC in the bisimulation quotient. It explicitly does not claim quotient irreflexivity; none is needed here.
- `WFTheory.lean`, `zf_consistent_of_model`: from that same nonempty `ModelsCPGIC` input obtains ordinary Con(ZF), including Foundation, using the internally well-founded part. Its hypothesis has no raw or quotient IR requirement.
- `ChoiceCalibration254.lean`, `zf_refutation_iff_zfc`: the external ordinary ZF/ZFC refutation comparison, using the constructible model.

Consequently Con(H)->Con(ZFC). Conversely the original ZFC/native-model interpretation validates CP/GIC and the retained rows; Eq symmetry is ordinary valid; canonical V is valid by native freshness with a separate truth-code-0 case. It follows that Con(ZFC)->Con(H). This is external classical reasoning about ordinary syntactic consistency, not a PA-internal proof-code equivalence or a newly established machine-halting theorem.

## 6. Native code zero and F audit

The native constructors are Imp=4P, Rel=4P+1, All=4P+2, Eq=4P+3. Thus F=1; Eq(0,0)=3; native Imp(0,0)=0. Decoder code 0 is the identity formula F->F, while encoding that displayed finite tree gives 16. In particular enc(dec(0)) is not 0.

For every positive n, all labels of dec(n) are below n: strong induction on n uses the two unpaired fields below n, with the recursive code-0 case containing only label 0. V(0) is separately valid because dec(0) is true. This proves canonical V sound uniformly, rather than inferring it from a finite scan.

The backward proof interpretation only needs finite encoded trees and the constructors' homomorphism laws. All such finite trees have positive encodings. It does not need an inverse enc/dec identity. The selected GIC instance is chosen using the actual enc(p), never by recoding an arbitrary decoder output. The code-zero alias therefore creates no gap in this interpretation.

## 7. Positive V placement in the measured frontends

I inspected the saved source ASTs, separately from their cost-report assertions. Their canonical V is an independent positive row, not a component trapped inside the negative CP/GIC bundle. Zero-based indexes include GEN at row0:

- `vacuity_reduction/omit_equality_deep/source.json`: row2.
- `vacuity_reduction/omit_equality_cost/source.json`: row5.
- `vacuity_reduction/symmetry_canonical_cost/source.json`: row2.
- `vacuity_reduction/symmetry_canonical_warm/source.json`: row7.

The cost scripts emit these rows separately before the bundle. In each saved AST the negative bundle has exactly three conjunction components, including the full Rel-vacuity component. Thus classicality can be derived from positive V first, and the bundle's Rel-vacuity/CP/GIC projected afterward. There is no bootstrap from only double-negated bundle components in these snapshots.

This is an AST-placement check, not a proof of the selected binary runtime's row coverage. If another source variant moves V into a negative bundle or adds gates to its supply, that new emitter must be checked again. The earlier weak-vacuity certificate may handle a double-negated component, but its precise schema coverage must be demonstrated rather than assumed. H_eq avoids this issue by retaining original rho8.

## 8. Independent tests and stopping boundary

Run from the workspace root:

    python -O research_sub236/equality_calibration_audit/check_independent.py
    python -O research_sub236/equality_calibration_audit/check_native_edges.py
    python -O research_sub236/equality_calibration_audit/check_frontend_placement.py

The independent checker uses its own leaf matching, formula/label validation, closed-GEN tracking, DAG checks, and direct Boolean assignment enumeration for TAUT leaves. It does not call the upstream replay checker.

Results:

- 93 additional E-law roots: 128,379 nodes, 117,299 formulas. Includes auxiliary binder0 in both transport directions, vacuity binder0, i=k_ab, a=b, c=k_ab, and labels as large as 999.
- Six separate numerical instantiations of the canonical Eq->E/Ex E bridge: 299 nodes each, two expected roots each.
- Four numerical instantiations of the original rho7-based reflexivity/symmetry/transitivity artifact: 547 nodes each, three expected roots each. This covers both source helper choices.
- Independently reran the supplied 51-root E replay, the Eq/E replay, the old equality replay, and the 724-node classical-bridge replay under Python `-O`.
- Native regression checks cover codes 1 through 65,535, the exact 0/1/16 alias facts, unchanged C(2,3,1), translated IR, and five equality-free named/padded GIC samples with actual output codes.
- Saved source AST hashes and positive-V row locations are recorded in `frontend_placement_results.json`.

Finite tests are supporting regressions only. The arbitrary-label construction is the structural and maximum-plus-one argument in sections 1–4. Remaining promotion work is to formalize the new native proof interpretation and restricted adapter, prove the chosen source enumerates exactly the calibrated rows, and bind all compiler/runtime/startup/folding changes to a literal full binary table and blank-halting result. Nothing in this audit licenses a state-count claim before that work.
