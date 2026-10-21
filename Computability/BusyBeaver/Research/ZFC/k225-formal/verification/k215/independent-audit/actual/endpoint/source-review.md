# Independent 215 endpoint/source audit

This is a source and literal-data audit, not a compiler receipt. The build lanes are compiling the complete Lean and Rocq targets separately. No proof compiler, proof generation script, or machine simulation was invoked by this auditor.

## Required endpoint

Both developments already state the required closed theorem: the exact accepted 215-working-state, two-symbol machine, begun on the blank tape in state 0, halts if and only if there is a finite classical first-order ZFC refutation. Each also proves its negation equivalence, nonhalting if and only if no such refutation exists. Neither public theorem takes a consistency assumption, simulation obligation, or source-calibration hypothesis. There is no identified missing theorem-statement layer.

Lean names are `KEndpoint215.blank_halts_iff_zfc_refutation` and `KEndpoint215.nonhalting_iff_zfc_consistency`, in namespace `SetTheory.BusyBeaver.ZFC`. The machine is `KDense215.machine215 : Machine 215`; the halting predicate expands to `∃ t, (machine215.run t).state = none`. `BProv ZFCax_s [] Form.fBot` means a natural-deduction proof from a finite list of axioms of the universally closed ZFC theory. The theory includes Foundation, arbitrary Separation and Replacement instances, and Choice. The constructive-universe consistency transfer in the generic endpoint explicitly upgrades the ZF equivalence to ZFC.

Rocq names are `K215F.CorrectDense215.tm215_halts_iff_ZFC_inconsistent` and `tm215_nonhalting_iff_ZFC_consistent`. `Dense.halts dense_tm Dense.c0` uses exactly the dense literal table, blank symbol false and starting state 0. `StandardZFC ⊢TC ⊥` is finite classical theory derivability. `StandardZFC` extends the sentence theory `Std_iface.ZFc` (including all closed Separation/Replacement instances and infinity) by Foundation and Choice. The `bnat 215` carrier includes indices 0 through 215: indices 0 through 214 are working states, and 215 has no transition and is the halt. This is 215 working states, not 216.

These are external proof-assistant theorems about finite derivability and a concrete machine. This audit does not claim an encoded derivation inside ZFC or an internal PA theorem.

## Literal bindings

The independent parser `literal_bindings.py` compares literal data without loading supplied Python helpers. Both formalizations' dense tables agree with all 430 actions of `candidate-k215/k215.tm`, SHA256 `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`. Native table SHA256 is `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`. The exact renaming is native 301→102, 302→120, halt 254→230. Lean/Rocq dense-label lists agree, apart from Rocq explicitly appending the halt label. Lean's sparse list stores labels 0 through 225; omitted larger labels and explicit disabled entries yield no transition.

Both formal source node dictionaries are identical and expand to all 4,751 accepted path/opcode/argument triples in `sites215.json`, SHA256 `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`. The dictionaries contain 179 internal decision nodes; with 23 distinct primitive leaf kinds this is the accepted 202-subtree DAG. The comparison includes the halt leaf and its null JSON argument. Old “219's source” prose in KSource215 does not alter those literal bindings.

## Bootstrap defect and repair

Opening identified an actual stale literal in the initially supplied `KBoot215.bootVs`: `[0,0,0,3,0,0,3,0,0]`. An independent read and decoding of the final literal checkpoint `cp13` instead gives physical registers `[0,0,0,0,0,0,4,0,0]`, 40 spare blocks holding 1, and a 65-zero gap. This agrees with `L2Perm.bootRegs`, whose logical register 0 is 4, and with Rocq's `boot_regs`. Opening corrected only the Lean final register literal and associated prose/generator output; the original files and diff are retained under the build's `repairs/boot-seed`. Checkpoint chunks and machine data were not changed. The current literal audit confirms the correction. Compilation still must validate every checkpoint proof and the final relation.

Rocq also had three inherited proof-case splits testing depth 40 although the concrete `check_edge` and theorem already use depth 48. Reflection corrected those three splits to 48 and preserved originals. I read the exact delta: no statement, runtime table, source program, or new assumption changes. No compiler failure is attributed to this pre-build correction.

## Static dependency/axiom boundary

The independent Lean DFS finds 171 project modules, with only `Init` explicitly outside the four project roots. Comment/string-aware scanning finds no project `axiom`, `sorry`, `admit`, `unsafe`, `native_decide`, `implemented_by`, `addDecl`, `mkAxiom`, `opaque` or `constant` token. This does not establish the actual theorem axiom set: final compiler `#print axioms` must disclose it, including ordinary Lean foundational axioms. The pre-repair closure record is retained separately.

The Rocq build's exact planned closure contains 237 modules, comprising 195 pinned reference sources and 42 K215-specific modules. Their reference hashes match the plan. The static audit finds a genuine `BusyCoq.LibTactics.inj_pair2` axiom declaration and a `skip` tactic whose body is `admit`. Neither alone establishes dependence of the endpoint. There are no `Admitted` commands in this closure. `BusyCoq.TM`'s fourteen `Parameter` declarations occur inside `Module Type Ctx` and are instantiated by concrete definitions/proofs. `RegCon.Main` uses `Axioms` only as a section name. The decisive pending checks are both sparse and dense endpoint `Print Assumptions` reports, all expected to say `Closed under the global context`, together with recursive `coqchk` without `-admit` or `-norec` exemptions. A custom axiom in a final endpoint's assumption list requires repair before the axiom-free endpoint claim.

The typed Lean caller `EndpointAudit215.lean` explicitly expands the blank halting predicate and states both final equivalences without hypotheses. The prospective Rocq CLI/scope record is `rocq-final-check-scope.json`. These are task evidence, not additional authorization requests.

## Own parser history and limits

Five failed literal-parser drafts are retained. They concerned the auditor's assumed sparse-list length (actual 226 stored labels, not 230), unparenthesized Lean halt syntax, whitespace in the Rocq edge regex, and the halt's null JSON argument. No machine or proof source was changed by these parser corrections. The final literal comparison succeeds. The source-level census and parser do not replace kernel compilation, dependency rechecking, or final axiom reports, and do not assert those pending outcomes.
