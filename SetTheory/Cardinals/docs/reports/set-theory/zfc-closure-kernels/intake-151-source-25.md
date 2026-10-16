# Batch151 manuscript02 / local source25: mathematical and Lean intake review

Verdict: the complete report, theory/reference code and two standalone Lean files were read. No mathematical error, unsafe instance replacement, capture bug, or overstated formal endpoint was found at the stated scope. Recommend a complementary addition to `set-theory/zfc-closure-kernels`; retain the delivered article and proofs unchanged. Machine suites are independently owned by `/root/review_bic/mira_backend_route`; this dossier does not duplicate or certify them.

Untouched extraction: `/tmp/zfc-intake-151-gkntyfry/zfc_exact_hull_research/zfc_exact_hull_research`.
All executions used the independent copy `/tmp/zfc-review151-source25-j9qkznh3/bundle`.
Principal evidence: `theory-review.json`, `finite-hulls-actual.json`, `reference-actual.json`, `metrics-actual.json`, two `example-*.json`, `lean-verification.json` and the two `*.actual.log` / `*.actual.stderr` pairs in the review directory.
The report's inspected ProveIt pin is `de047657e193ec605e930eaf149a44a38031820b` (2026-10-16T20:33:01Z); requested earlier pins are `6d8bc7f1ba02c83e54757366f019f61b966ed0b7` and `63c83cf79986f8a92bb75460848a1d4f863b7b15`. Current head when the dossier was frozen is `6ec2e80dbbe45a99b7812fb5757977307959a51e`.

## Full read and main contributions

Read `report.tex`, all eight `sections/*.tex`, README, NOTICE, PROVENANCE, Makefile, top-level reproducer, every file under `code/`, both `formal/*.lean`, and machine README/ENGINEERING_NOTES/ATTRIBUTION. The supplement's machine algorithms/vendor reuse are the other reviewer's scope. No bulk checksum/manifest validation or line-ending work was performed. No delivery file was edited.

The new theory is EFPC in the ordinary equality-free membership language. For each matrix rho with arbitrary finite parameters, use the existing subset-fiber bound LB and the operator

`F(c;y) := exists x, (Empty(x) or x in c) and rho(x,y)`.

EFPC asserts `LB -> exists c, forall y, (y in c iff F(c;y))`. This fixes the exact incoming profile of a represented hull, without equating raw objects or quantifying over all external classes. It differs from the earlier exact-fiber theory: its new conclusion is a fixed point of the empty-seeded relational operator. A search of existing host articles/notes and current Lean sources found no earlier EFPC/exact-prefixed-hull theorem; the normal form and its local resource theorem are new relative to this tree. No historical priority is asserted for the Knaster–Tarski argument.

The useful contributions are:

1. Full EPSC and full EFPC have the same first-order consequences. The forward argument uses previously derived raw Separation, rather than trying to replace just one EPSC row.
2. A precise constructive semantic lemma needs two specified representing objects, L and J, rather than an implicit semantic powerset or arbitrary-relation closure principle.
3. Relative leastness inside a prefixed container is distinguished from global leastness. An additional represented intersection supplies the latter; a three-object model refutes the latter without that resource.
4. A different three-object structure has a raw empty object and locally subset-bounded rho, satisfies the universal parameter closure of a single EPSC instance, yet refutes its EFPC counterpart. This is stronger than an external-relation-only counterexample and correctly limits any row-level compiler substitution.
5. A narrow independently checked correction to a printed modal axiom list. Its main translation and equational presentation are not refuted.
6. A full ordinary equality-free Hilbert reference with actual capture-avoiding instantiation and an EFPC/EPSC axiom selector. This is separate from the measured equality-bearing271-state compiler control.

## Exact-hull proof audit

The monotone operator can be an unrepresented binary predicate F(A;y). In a represented prefixed C, L represents the intersection of the represented prefixed subobjects B of C, and J represents `C intersect F(L)`.

- L is included in C and every such B directly from its representing formula.
- Monotonicity into C and each B proves that F(L) is included in L.
- J is included in L and C. Monotonicity along J subset L then makes J prefixed.
- Relative leastness applies to the represented J; L subset J yields the reverse fixed-point inclusion.

No extensional equality, Foundation, Choice, Replacement or representative-selecting family is used in that lemma. The supplied C/L/J already witness domain nonemptiness. The Lean theorem is intuitionistic at this interface.

For the first-order application, rho must not contain the newly allocated hull variable c. This is explicitly stated in `sections/03-exact-hulls.tex:82–85`; the reference constructor allocates all auxiliary variables above every label in rho and performs capture-avoiding simultaneous free replacement. Thus the monotonicity premise is justified for arbitrary positive/negative/quantified rho; no accidental positivity condition on rho is needed.

Full EPSC supplies the two raw Separation instances. F(L) is prefixed relative to the chosen C, so those instances are enough for exactness. For global leastness against an arbitrary prefixed B, Separation of `B intersect C` yields a prefixed subobject of C. This additional family is explicit in `exact_hull_global_least`; it is not silently extracted from the original two objects. The finite boundary example (`C=L=J=c`, incoming profiles `{c,b}`, `{b,t}`, `{c,b,t}`) really satisfies the original resources, while b is prefixed and c is not included in b. The absent profile `{b}` is its needed intersection.

Conversely, EFPC directly gives closure plus global support for the same rho. Therefore the full schemas are deductively equivalent; deriving EFPC from EPSC can use other EPSC instances to obtain Separation. The report explicitly says this at `sections/03-exact-hulls.tex:97–101` and does not erase support from the source theory merely because the later fixed-point lemma no longer uses it.

The instance counterexample also checks out. Incoming profiles are `E0={}`, `E1={0,1}`, `E2={0,2}` and rho has rows `0->{0}`, `1->{}`, `2->{1}`. Its generated profiles are `{0}`, `{0}`, `{0,1}`. LB holds, object1 supplies EPSC support/closure, and no represented profile is fixed. The equality-free D/Empty gate has exactly two active parameter valuations, `(0,1,2)` and `(0,2,1)`, interchanged by the structure's symmetry. Every other valuation has false rho and the raw empty witness. Thus the *universally closed single* EPSC instance holds and the corresponding EFPC instance fails, while neither finite structure is claimed to model the full theory.

The ZFC-level consistency statements are ordinary mathematical consequences conditional on the inherited full raw PSC/EPSC calibration, exactly as the report labels them. The set-coded-completeness argument is uniform over formulas; it does not confuse individual external standard instances with an internal universal schema. The Foundation/Choice discussion correctly asks for internal well-founded/constructible classes of a potentially nonstandard model, rather than assuming its externally well-founded part is a model. It does not assume a ZFC model without the corresponding consistency antecedent. Equality-bearing comparison controls plus IR are calibrated by an ordinary subtheory/ZFC-model sandwich; raw EPSC/EFPC are not asserted to derive IR.

## Reference-checker audit

`reference_kernel.py` preserves source14's genuine-bottom, equality-free syntax and K/S/C/UI/QD/GEN/MP interface, then adds an explicit EFPC constructor and one kernel selector. K/S/C is the standard classical propositional basis. UI does genuine capture-avoiding free-variable substitution; QD checks its free-variable side condition. GEN operates on previous theorem records, with no open assumptions. MP checks the antecedent exactly. AX constructs universal closure from a matrix. No arbitrary conclusion, unchecked assumption, supplied theorem field or mixed-kernel record is accepted. References are backward-only; booleans are rejected as natural labels. The standard ordinary one-domain completeness argument therefore applies to the abstract checker specification.

The substitution function was inspected beyond the delivered shallow examples: it removes the current bound label from the active mapping, restricts mappings to free occurrences, freshens a binder if it occurs among active targets, and chooses the fresh label outside the body's entire label set and the mapping's domain/range. Recursive replacement of the old binder label respects inner shadowing. Both distinguished matrix slots are simultaneously mapped to fresh role labels; all other free parameters survive for universal closure. This matches the stated two-input role semantics.

This is a complete *reference interface*, not a verified Python interpreter or numeric decoder. Its physical recursion/memory limits and the ideal finite-storage enumeration claim are explicitly separated. The reference uses primitive bottom and full variable transport, so it is not refuted by the existing many-sorted reduced-engine obstruction. The reference and compiler control are explicitly different implementations (`sections/04-logic.tex:106–111`). The report does not use finite tests as a completeness proof.

## Mathematical suite reproduction

All ran with `uv run --no-project python ...` on the separate copy. All three produced JSON semantically identical to the delivered data; both example modes accept a valid non-refutation.

- `code/finite_hulls.py --output ../finite-hulls-actual.json`: PASS. Exhaustive262,404 ordered relation pairs on1/2/3 objects. Per-size local-bound counts4/242/186694; EPSC-versus-EFPC single-instance gap counts0/12/10824. Resource triples2/216/195054, total195272. The two-object gaps have no empty object; the three-object census has816 gaps with an empty object. These are finite-instance/resource diagnostics, not full-schema finite models.
- `code/check_reference.py --output ../reference-actual.json`: PASS.70 distinct matrices;2520 schema semantics comparisons;55852 substitution semantics comparisons;13 rejected malformed/unsound certificates;2 valid non-refutations;27 parameter valuations for the gated universal-instance example, with EFPC failing precisely at `[0,1,2]` and `[0,2,1]`;16 degenerate modal axiom checks.
- `code/wrapper_metrics.py`: PASS. EPSC/EFPC tree sizes39/49 in unary negation,37/45 after adjacent double-negation cancellation,51/67 in implication/bottom,39/31 with primitive biconditional. Distinct-subtree sizes35/34,33/32,36/35,35/30 respectively. Matrix occurrences3 each in expanded bases and2 for native-iff EFPC. Variable payloads, extra parameter closure, decoder and proof-engine costs are correctly excluded.
- `code/reference_kernel.py examples/valid_nonrefutation.json` and the same with `--kernel EPSC`: PASS; both valid and not refutations.

The top-level checksum routine and all machine SOURCE/ARTIFACT manifest loops were not executed. Functional recorded-result comparisons were retained. The machine reviewer separately owns the advertised machine quick/full/fusion replays.

## Standalone Lean reproduction and formal scope

Exclusive build grant was obtained and explicitly released immediately after both files passed. Explicit binary:

`/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`

Version: Lean4.32.0, release commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. No Mathlib or project import dependency.

- `ExactHull.lean`: return0,0.321seconds, six printed empty-axiom audits, stdout byte-equal to the delivered audit log.
- `ModalBasisAudit.lean`: return0,0.298seconds, seven empty-axiom audits, stdout byte-equal to the delivered audit log.
- No warnings/errors or nonempty axiom audit appeared.

The six hull audits are `exact_hull`, `exact_hull_global_least`, `seedImage_monotone`, `seed_exact_hull`, `ScopeCounterexample.relative_fixed_point`, and `ScopeCounterexample.not_global`. The semantic resource assumptions are visibly parameters, not custom axioms or hidden all-relations closure assumptions. The two whole-schema first-order formulas and their EPSC-derived Separation representations are not formalized here.

The seven modal audits are `abbreviated_schemata`, `propositional_tautologies_hold`, `modus_ponens`, `necessitation`, `T_not_valid`, `original_axiom_three_fails`, `equational_D1_fails`. They prove Boolean facts for the explicit constant modalities; `propositional_tautologies_hold` intentionally just instantiates the semantic tautology premise. There is no full formula AST, derivation-system induction, modal completeness or set-theory interpretation theorem in that file. The report states these limits.

## Primary modal-source check

Independently opened the official arXiv HTML and PDF for Andréka–Németi arXiv1111.0995v1. The actual PDF's printedpp5–6 (zero-based PDF pages4–5) were locally rendered and visually inspected; copies `andreka-p5.png`, `andreka-p6.png` and the primary PDF are in the review directory. Source: https://arxiv.org/pdf/1111.0995v1 .

The literal abbreviated modal list is B/K/5/C1/C2 with MP and necessitation. It omits reflexivity T. Constant-true box and constant-false diamond satisfy its duality, listed axioms and rules but falsify T. The earlier quantifier axiom3 and equational D1 exclude that valuation. The report's correction is therefore valid and narrow. It neither refutes the paper's main translation nor equates its ternary atomic language with binary membership. The18-equation count is3 Boolean equations +4 equations for each of3 operators +3 commutations.

This does not require a preplacement correction of an existing project claim: searches of current Research/ZFC, host README and earlier sources15/17 found no existing endorsement of that literal abbreviated list as a complete basis. Earlier genuine S5/three-modal interpretation references are compatible with this correction.

## Current-tree reconciliation and precise gap references

The report is explicit about its older pin. The following later results should be recorded beside it, without editing the delivery:

1. **Raw Separation resource already formal, full EPSC→EFPC adapter still new/open.** `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RawPSCModel.lean:22–23` defines actual formula-indexed raw PSC. At175–178 the theorem says, for arbitrary equality-free phi and env, `exists b, Exact mem (fun y => mem y a and Sat mem (scons y env) phi) b`. This is the precise reusable resource for the two hull representatives, after adding the EPSC↔PSC adapter and fresh formula builders. At292–295 `pure_hull_of_model` still requires explicit definability, interpreted bound and invariance; it does not state the full raw interpretation. No current `EFPC`/`exact_hull` theorem was found in the project library.
2. **Existing extensional first-order calibration is stronger than a semantic proposal.** `PSCCalibration.lean:96–98`: `(Bootstrap.Extensional mem and ModelsPSC mem) iff (ZFAxioms mem and PowerSets mem)`; Foundation/Choice excluded. At171–173 `psc_iff_zf0` identifies actual `BProv` sentence consequences;175–177 gives the consistency corollary. This is not raw EPSC/EFPC calibration or an arithmetic proof-code translator.
3. **Generic full named logical completeness is now proved.** `Lukasiewicz.lean:510` constructs `Tarski.classical`, and518 states `Tarski.complete`; no old hC/hC0 premise remains. `TarskiFalsity.lean:184–187` also proves `alias_complete` for the actual relative falsity, under bot-free Ax/target and irreflexive semantic models. Thus the report's general requirement to finish variable/falsity logic is partly met by later current Lean work; the changed EFPC numeric emitter and binary machine bridges remain open.
4. **Named→original numeric proof transport now exists, with a precise open calibration.** `Research/ZFC/numeric254_lean.md:51–55` records all-rule transport, while63–74 states the exact `Thm Q bot iff NumThm1` endpoint and explicitly leaves identifying Q with SIR/ZFC open. This cannot be read as an EFPC emitter certificate.
5. **Full literal public253 bootstrap, RM330 and their finite representation relation are now formal.** `BootstrapFrame253.lean:90–95` proves the full `DispatchFrame` for Core312975;106–110 combines that with actual RM330. The report's reproduced endpoint is prior work and now has these local Lean certificates. General instruction preservation/runtime, first-arrival and internal ZFC consistency are still absent; the frame theorem explicitly excludes those claims.
6. **EPSC270 is a comparison, not the global best complete retained-word control.** `Research/ZFC/layout_grammar_experiment.md:3–11` records the already reviewed complete original logic/theory layout at268, with a source bridge and no binary/ZFC endpoint. The new EFPC271 is worse than EPSC270 in its stated family, and neither improves attributed public253. The report's arithmetic17/18-state gaps relative to270/271 are local planning comparisons, not a claim that270 is the smallest existing full-control table.
7. **The new local504folds are independent later diagnostics.** The current `public253_fold_search.py` explores old5/84 direct folds omitted by source04, with55 rows frozen. Its sole known affine survivor5→64 fails the exact boot frame through2M. Source25's symbol-wise fusion family is broader and separately accounted for by the machine reviewer; neither negative search proves minimality.

No existing claim needs a preplacement retraction. The instance obstruction only refutes a newly articulated tempting replacement; the current tree did not assert it. The modal correction is likewise a new narrow source-audit result.

## Reuse and next proof obligation

The immediate reusable component is the small constructive resource theorem. To connect it to the current library, construct equality-free formula builders for `F_rho`, `Pre_rho`, the L intersection and J image cut, prove their satisfaction/renaming bridges, derive their representatives using actual `RawPSCModel.separation_of_model` after the ordinary EPSC↔PSC bridge, and apply the local theorem. Keep all hull/bound variables fresh relative to the matrix and arbitrary parameter environment. Global leastness needs a separately instantiated intersection formula.

This could close a genuine formula-level theory-equivalence component, but it is not currently a state improvement. The native-iff/shared-DAG directions are hypotheses to measure with their extra codec/logic costs. The report's complete-engine controls, exact operation certificates, finite boot replay, local Lean proofs, ordinary schema calibration and final internal-ZFC machine theorem remain separate artifacts with separate proof obligations.
