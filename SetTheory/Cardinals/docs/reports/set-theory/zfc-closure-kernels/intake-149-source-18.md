# Batch 149 source 01: quantifier obstruction and binding certificates

Arrival `de047657e`, archive `zfc_consistency_research.zip`. Untouched source: `/tmp/zfc-intake-149-8lt55_fi/01/zfc_consistency_research`. Execution/read copy: `/tmp/zfc-batch149-theory-review-fw5hc93s/01`. Report pin: `96836f9eea3540e96322c3d28c7127a582aae223` (2026-10-16 19:51:28 UTC). This review read the complete report and README, both Lean developments, all four core binder/test modules, independent binder audit, actual-template obstruction audit, parameter-acquisition checker, reproduction driver and the relevant current source-11 generator. No checksum manifest or line-ending work; no original/source edit or repository mutation. Root separately owns compiler/PDF reproduction. Both standalone Lean files were independently compiled on the scratch copy with the pinned Lean4.32.0 after root granted the exclusive build slot; all12 principal axiom audits report exactly [propext]. The slot was released immediately afterwards.

## Verdict

Place as a continuation of zfc-closure-kernels. No defect was found in the new ordinary mathematical arguments, local binder witness checker or strict binary format. Its two formal developments have appropriately narrow statements. The new 269/283 outputs are explicitly compiler controls, not smaller calibrated machines. A dated reconciliation must retire the source's stale open C/G-calibration question: its pin predates the subsequently accepted full finite-sort obstruction. The 12/24 destructive-parameter warning **does not invalidate the current source-11 248-state permutation**.

## New results and exact scopes

### Fixed-slot PSC counterinterpretation

`formal/PSCIdentityObstruction.lean` defines its own finite syntax and derives invariants for precisely specified axiom/inference constructors. Quantifiers evaluate as identity; R(i,j) is true exactly when i≥2 and j=0. Both primitive Bottom and R(0,0) are false. For every arbitrary matrix A and k≥2, the literal fixed-slot PSC wrapper is true: its local bound is true, activation guard false, closure/support true. No freshness of k relative to A is needed. Thus code+2 instances and either falsity convention are included.

The enlarged calculus includes original and dual rho6, distribution, commutation, same-variable specialization, explosion, IR, vacuity, modal S4/S5 and even every axiom valid in all identity-quantifier atom valuations with R00 false. MP/GEN preserve the invariant. This proves designated falsity underivable and excludes the valid ordinary UI sample (forall_2 R(2,0))→R(0,0). The interpretation intentionally distinguishes variable spellings and is not a common-domain membership model. It is not a model of the actual C/G bundle: the source-template negative control correctly finds its C factor false at a=0,b=1,c=2.

Principal declarations read: `eval_psc` (line107), `eval_psc_codePlusTwo` (113), `derivation_sound` (195), `no_designated_falsity` (218), `bottom_calculus_consistent` (225), `relative_calculus_consistent` (228), `properUISample_underivable` (235). The `IdentityValid` family is a defined property/constructor premise, not an unexplained new axiom. No `sorry`, project-specific axiom or numeric-code/runtime adapter is introduced. This is stronger than merely a false logical theorem example, because it validates every specified PSC row plus the repairs. It remains separate from ordinary one-sorted PSC equiconsistency and from literal-machine nonhalting.

### Locally nameless binding results

`formal/BinderSyntax.lean` distinguishes free names from bound indices. Opening removes the single surrounding binder: at traversal depth d it replaces bound d by a free name; the source-scoping hypothesis excludes greater indices, so no decrement branch is required. This is deliberately not a general operation on arbitrarily open contexts. Closing changes one free name to bound d; internal binders increase depth.

The stronger identity `Form.openAt_closeAt` (line218) identifies free a with **any** free b, including an already occurring b. `Form.openAt_closeAt_self` (241) is the same-name inverse. `Form.closeAt_openAt` (245) correctly retains the freshness condition in the reverse direction. `Form.closeAt_eq_self_iff` (262) makes fixed-point closing an exact freshness test. `Form.plugAt_scoped` (276) proves the two-slot insertion scope bound. The scope lemmas (174,188,202) have the needed hypotheses. These finite syntax functions match the mathematical operations used by the Python witness interface. The file does **not** define a satisfaction predicate or prove the Python DAG verifier, PSC adapter, proof calculus or binary parser sound; the report explicitly preserves that limit. All seven printed audits independently reproduce exactly [propext] under the pinned compiler; this still does not establish a semantic/Python bridge.

### Binder witness/checker audit

All of `code/binder_kernel.py` and `binder_wire.py` were read. No concrete discrepancy with the specified mathematical algorithm was found.

- Formula tables are interned/topological, Bottom is node zero, and every formula child reference points to an existing node. Reconstructed rule conclusions can be appended safely; references never create cycles.
- Witness rows verify source/output constructors, local term transformation **and source scope**, exact child pairs/depths, strictly earlier child references and the exact root at depth zero. Surplus unrelated rows do not allow a false root. The verifier does not call the witness producer.
- Open/close/plug modes reject extraneous parameters. The three fixed PSC plug maps are (2,0,width3), (1,0,width4), (0,1,width4). Under internal matrix binders they increase inserted indices, while preserving pre-existing local bound indices. The subset dummies and root/output scopes agree with the mathematical curried subset-PSC schema; support uses an unrestricted input.
- K/S/C payloads and every reconstructed conclusion are checked scoped at zero. UI opens a body scoped at one and permits identification with existing free names. UD verifies a close-to-self witness for the antecedent, exactly enforcing the side condition, and closes its consequent. GEN closes one free name of an earlier theorem. MP checks earlier references and exact antecedent identity. No arbitrary-assumption or alleged-conclusion opcode exists.
- Open parameter instances are interderivable with universal parameter closures by finite GEN/UI in the **complete** calculus. The report correctly does not transport that argument into the retired reduced numerical skeleton.
- Bottom is accepted only as the actual final reconstructed theorem. Input syntax containing Bottom is not sufficient. The binary decoder infers witness modes from rule arguments, validates every field, rejects truncation and every trailing suffix, and uses bounded unary reads. Enumerating binary(n) minus the leading one, n≥1, is the exact shortlex order of all finite bit strings. Mathematical candidate checks terminate; host memory/interruption failures are not accepted contradictions.

The ordinary soundness/completeness proof is valid: local witness induction identifies transformations; the complete K/S/C/UI/UD system provides arbitrary one-sorted variable instantiation; named finite proofs normalize/translate to locally nameless proofs and finite witnesses/DAGs; conversely every reconstructed line translates to that standard calculus. No global semantic-relation closure oracle is assumed. This is an ordinary algorithm/proof-language theorem, not a Lean verification of Python or its future binary implementation.

### Destructive rho8 parameter contract

The original implicational row uses metavariables with multiplicities a:2,b:1,c:3,u:1. The unchanged emitter destructively reads the streamed fourth parameter at every u token. Exactly 12 of 24 mathematical permutations place that read in a multiplicity-one position. The six others of each remaining kind read twice or three times. The explicit two-read counterexample emits

`((c→a)→u1)→((u2→c)→(b→c))`.

For c=false,b=true,u1=true,u2=false it is false for either a. Thus abstract schema-bijection alone is insufficient as a compiler contract. The claim is about this unchanged acquisition interface; it is not a theorem that no two-read implementation can be repaired with caching.

**Current source-11 is safe.** In `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/11-grammar-code-generate_schema_candidates.py:84`, the mapping is `{a:b,b:u,c:a,u:c}`, so streamed u occupies the original multiplicity-one b position. Line108 explicitly checks `program.count(158)==1`. Lines106–107 also check the exact symbolic stack contract. This report does not refute that retained artifact or require changing its delivered files.

### Other theory/program suggestions

The source preserves the 253-state complete-calculus reference and proposes compiling this complete checker, or a fully specified finite universal/equational/rewriting source. No attractive intended meaning is required. All payload, term processing and initialization costs are charged. The exact-state-quotient result is correctly limited and does not obstruct contextual helper/initializer sharing. The original-rho6 248 source has only four decision nodes of headroom relative to a strict improvement below253 with the fixed62 framework; this arithmetic is correct but the source search is now retired by later work.

I independently opened Friedman's primary *Impossible Counting* (2017), [PDF](https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2014/01/ImpossibleCnt090217-2a5ewhm.pdf). Section4.2's Theorem4.2.3 states the finite-theory ZFC equiconsistency argument in ACA0, and the later conversion explicitly reaches one four-place function with seven variables. This supports the report's proposed alternate input; I did not audit every conversion in that long paper, and no extracted ready-to-compile finite payload is bundled here. The later large-cardinal section is not the proposed ZFC-strength input. Relation-algebra/Diophantine routes remain suggestions, with no measured full code/payload supplied.

## Executed checks on the copy

Commands were launched by `uv run --no-project python`, which supplied Python3.13 and spawned the listed `-B` standard-library scripts. All exact commands, cwd, exit status and times are in the outside `verification.json`. All passed:

1. `code/test_binder_kernel.py --output ../01-kernel.json` (3.119s): 5 tests; 6,044 binding semantic comparisons; 2,700 PSC comparisons; 17 negative checks; depth6,000; an eight-line non-refutation example.
2. `code/test_binder_wire.py --output ../01-wire.json` (1.268s): exact392-bit/eight-line example; all392 truncations rejected; 95-bit PSC example; census131,071 strings through16bits,92 valid derivations,zero refutations; exact roundtrips.
3. `audit_artifacts/binder_independent_audit.py --output ../01-audit.json` (1.069s): 2,160 JSON field mutations,zero refutations/unexpectedexceptions; 800 arbitrary one-slot bodies and1,600 opening/UI comparisons; reverse-inverse freshness counterexample; all8 opcodes in11lines/609bits;1,001 single-bit mutations,13 valid exact-roundtrips,zero refutations; first15 shortlex strings.
4. `code/binder_wire.py examples/binding-proof.bits` (.065s): valid392-bit/eight-line derivation, `accepted_refutation:false`.
5. `code/psc_identity_obstruction_check.py --repo <scratch pin96836> --limit 100000 --output ../01-actual-obstruction.json` (1.620s): 100,000 codes each base3/base4;204 additional exact wrapper cases;14,336 logical-row cases;IR100;properUI false; actual C/G negative control false. Dependencies were recovered with `git show` at the named pin into an outside minimal tree, not fetched or run from the live checkout.
6. `compiler/check_parameter_acquisition.py --repo <scratch pin96836> --output ../01-parameter-acquisition.json` (.092s): all24 actual-emitter permutations, distribution12/6/6 and both unsafe Boolean valuations confirmed. Its source-file pin checks are intrinsic executable source-contract checks, not archive-manifest validation.

The top-level reproduce.py starts with MANIFEST validation, so that prohibited step was not invoked. These constituent checks cover our assigned mathematical/Python work; root owns the separate finite RM/table/compiler checks and PDF. No bounded absence of refutations supports a consistency claim. No Lean build was run while another agent held the build grant. After the root explicitly granted the released slot, the following two independent checks passed:

## Current-tree reconciliation and remaining obligations

- The source's statement at report.tex:669–672 that C/G calibration is unresolved on other grounds, and its further question at1239ff, are historical at its older pin. `Computability/BusyBeaver/Research/ZFC/typed_countermodel.md:1` now says “The incoming finite-sort obstruction retires the reduced raw C/G calculus”. Lines25–29 cover the retained rows and either rho6; lines38–44 retain the literal-table simulation qualification. Source17 additionally gives an ordinary PA argument. Record that update without editing delivered content.
- `.../Lean/BusyBeaver/ZFC/RawPSCModel.lean:22,44` already supplies actual equality-free Form-indexed PSC instances; lines136/141/147/153/175/188 give twins/empty/power/cover/Separation/Union, and257/265/271 give purity cut/saturation/upward purity. The source's earlier description of raw bootstrap/formula adapters as wholly future work is stale. `pure_hull_of_model` at292 retains explicit definability, PureLocalBound and PureRelationInvariant at294–295; the full uniform H-quotient interpretation and internal machine endpoint remain separate.
- `.../PSCCalibration.lean:166,171,175` proves same_models/sentence deductive equivalence/consistency for **Extensionality plus PSC** versus ZF0, not the whole raw equality-free theory calibration.
- `Computability/BusyBeaver/Research/ZFC/README.md:124–127` retains the absence of a verified proof-code translator/refutation checker/enumerator compiler/final machine endpoint. The new BinderSyntax file and tested Python checker do not silently fill those gaps. Bottom3Syntax is a different codec and carries no inherited proof-language/runtime theorem.

Practical next use: keep the obstruction as a narrow formal negative result and the binder witness checker as a complete correctness control; port its local verifier/semantic bridge before measuring a new backend. Its explicit repeated-variable and fixed-point-freshness contracts are reusable. No new theory minimization or numerical record is established by this source.

## Independent pinned Lean rebuild

Compiler: Lean4.32.0, x86_64-unknown-linux-gnu, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, Release. This matches both the package and repository toolchain. Both source files were compiled **from the scratch copy** into `/tmp/zfc-batch149-theory-review-fw5hc93s/lean-check/`, sequentially, with no project/host source edits:

- `lean -o <scratch>/PSCIdentityObstruction.olean <copy>/formal/PSCIdentityObstruction.lean`: exit0, .888672s, empty stderr. `eval_psc`, `derivation_sound`, `bottom_calculus_consistent`, `relative_calculus_consistent`, `properUISample_underivable` each report exactly `[propext]`.
- `lean -o <scratch>/BinderSyntax.olean <copy>/formal/BinderSyntax.lean`: exit0, .761837s, empty stderr. `Form.openAt_closeAt_self`, `Form.openAt_closeAt`, `Form.closeAt_scoped`, `Form.openAt_scoped`, `Form.closeAt_openAt`, `Form.closeAt_eq_self_iff`, `Form.plugAt_scoped` each report exactly `[propext]`.

There are no warnings, custom axioms or sorryAx. Exact commands, version, statuses, timings and complete unabridged audit outputs are preserved in `lean-check/verification.json` and the two `.stdout` files. No claim about Python, wire semantics, a numeric decoder, runtime simulation or the internal ZFC endpoint follows merely from these standalone syntax/derivation theorems. Exclusive build rights were explicitly released to root after both processes finished.
