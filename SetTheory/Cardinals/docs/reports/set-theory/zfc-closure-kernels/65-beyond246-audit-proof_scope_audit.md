# Proof-scope audit for a machine below 246 states

Audited against ProveIt revision `8cdc55ff9281b0aaba49bf74b0b225d57f12b893` on 18 October 2026 UTC. This is a mathematical and source audit, not a fresh Lean/Rocq compilation. The three incoming archives were read from copies outside the repository.

## Main finding

The user's requirement is a conventional mathematical proof of

\[
\mathrm{ZFC}\vdash
\bigl(\neg\operatorname{Halt}(M,\mathrm{blank})\leftrightarrow
\operatorname{Con}(\mathrm{ZFC})\bigr).
\]

The repository's open PA internalization task is stronger than this requirement and does not prevent a ZFC proof by ordinary set-model arguments. Conversely, a closed theorem in Lean, even one reporting only the usual Lean axioms, does not automatically constitute a general translation into ZFC. The right justification is that the particular proof uses finite combinatorial inductions, set-coded first-order syntax and models, set-sized quotients and substructures, and satisfaction for set structures. Those are constructions available in ZFC.

The incoming `zfc-context246-20261018.zip` already claims this conventional ZFC proof for 246 working states. It separately and correctly says that it supplies neither a newly compiled endpoint for that table nor a serialized first-order ZFC or PA proof object. The new contribution must therefore improve this 246-state construction. Repeating its marking fold or pulse fold is not a new improvement.

## Current exact inherited endpoints

The following declarations were fetched through the GitHub plugin at the current revision. Eight relevant copied source files in the 246 archive match that current revision: `ChoiceCalibration254`, `WFTheory`, `NativeTheory254`, `WFModel`, `ConstructibleZF`, `ConstructibleOrder`, `ConstructibleAbs`, and `ZFNative`.

| Declaration | Exact mathematical content | Material premises at the endpoint |
|---|---|---|
| `NativeTheory254.c254_refutation_iff` | `Code254.C254 Code254.F` iff a finite `NativeAx` refutation exists. | None. |
| `WFTheory.c254_refutation_iff_zf` | `Code254.C254 Code254.F` iff a finite `ZFax_s` refutation exists. | None. |
| `WFTheory.native_refutation_iff_zf` | Native refutations iff ZF refutations. | None. |
| `ChoiceCalibration254.zf_refutation_iff_zfc` | ZF refutations iff `ZFCax_s` refutations. | None. |
| `ChoiceCalibration254.nonhalting_iff_zfc_consistency` | Nonhalting of the exact blank permutation252 machine iff no `ZFCax_s` refutation exists. | None. This remains an external Lean statement. |

`NativeAx` is exactly the universal closure of CP, every full finite-formula GIC instance, and raw irreflexivity. Equality is ordinary logical equality, and the scheme includes formulas with equality. It is not a scheme over arbitrary external relations. `ZFax_s` includes Power Set and Foundation. `ZFCax_s` includes the literal sealed selector-Choice axiom in addition to those ZF axioms.

Relevant current source locations:

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NativeTheory254.lean`, especially `NativeAx`, `models_NativeAx`, and `c254_refutation_iff`.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFTheory.lean`, especially `zf_consistent_of_model` and `c254_refutation_iff_zf`.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean`, especially `constructible_models_ZFC`, `constructible_nonempty`, and `zf_refutation_of_zfc`.
- `Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md`, paragraphs headed “Evidence and proof boundary.”
- `Computability/BusyBeaver/Research/ZFC/pa_internalization.md`, which treats represented syntax/proof/trace translation as a separate arithmetic task.

## Why the mathematical calibration belongs to ZFC

Fix one recursive first-order presentation, and write `Ref(T)` for the existence of a finite proof of falsity in that presentation. Finite syntax and proof trees are sets of natural-number codes. The first-order completeness theorem for a countable recursively axiomatized theory is formalizable in ZFC, and supplies a nonempty set-coded model whenever the theory is consistent. A countable model can be used throughout; no transitive model is required.

There are two relevant model constructions.

First, a native CP/GIC model has a set-sized bisimulation quotient. This quotient carries the six-field set-axiom bundle, exact Power Set, and the additional particular GIC instance needed for closure of the internal well-founded domain. The word *internal* must be retained: the formula says that every nonempty subset represented by an object of the model has a minimal member inside an appropriate transitive witness. It does not say the model's membership relation is externally well-founded.

`WFModel.lean` implements this step without ambient Foundation or object Choice. Its Separation theorem uses the actual recursively translated formula. Replacement uses both input and output WF guards, making the ambient relation globally partial-functional. Its Power Set theorem uses closure twice, so all ambient subset representatives are included. Infinity is obtained by separating the actual WF predicate from an ambient inductive set. `WFModel.quotient_models_ZF` supplies every literal closed ZF axiom, while `WellFoundedPart.quotient_domain_nonempty` supplies an actual inhabitant. These are the particular hypotheses needed; the argument must not be generalized silently to every arbitrary model of ZF without Foundation.

In the reverse direction, every ordinary ZF model supplies native rank containers and GIC through its internally derived Collection scheme. `ZFNative.native_of_zf` retains Foundation and Power as extracted resources. Soundness and completeness then yield native/ZF refutation equivalence.

Second, from a set model `A` of ZF form its internal constructible subdomain

\[
L^A=\{a\in|A|:A\models a\in L\}.
\]

This is a subset of the set `|A|` in the metatheory even though `A` regards its own constructible universe as a class. The induced structure has all literal ZF axioms. `ConstructibleZF.inL_sep` proves Separation uniformly in a finite formula by finite parameter bounds and reflection. `ConstructibleZF.inL_repl` uses a guarded actual formula, a stage bound, and Separation inside L. These are syntax-indexed arguments, not external-predicate schemata.

`ConstructibleOrder.choice_of_VL` obtains selector Choice from the internal canonical well-order. Its chosen selector is an object made by the actual Separation scheme from the union of the represented family. Metatheoretic choice is not mistaken for an internal selector set. `ConstructibleAbs.vEqL` supplies `V=L` inside this subdomain, and `ChoiceCalibration254.constructible_nonempty` exhibits a constructible empty ordinal.

Thus a hypothetical ZFC refutation would, by soundness, exclude the constructed L model. If ZF were consistent, completeness would supply the original ZF model and produce a contradiction. Therefore a ZFC refutation implies a ZF refutation. The other implication is theory inclusion. The argument proves the exact comparison

\[
\mathrm{ZFC}\vdash
\bigl(C_{254}(1)\leftrightarrow\operatorname{Ref}(\mathrm{NativeAx})
\leftrightarrow\operatorname{Ref}(\mathrm{ZF})
\leftrightarrow\operatorname{Ref}(\mathrm{ZFC})\bigr).
\]

All satisfaction relations here are for set structures. Formula induction handles every finite formula code uniformly. When the mathematical argument is formalized inside a possibly nonstandard model of ZFC, its own natural numbers and finite codes are used; no step requires restricting to externally standard syntax. This is precisely where ordinary ZFC model mathematics differs from the outstanding PA task: PA needs represented proof transformers and trace translations, together with internal correctness/totality proofs, rather than taking the set-model construction as available.

The audit reads and identifies these mathematical ingredients. It does not claim a new kernel run of their dependency closure or a compiler translating arbitrary Lean terms into first-order ZFC derivations.

## Required new-machine obligations

The inherited logical endpoint need not be altered. A smaller table must establish the exact binary-to-program side:

1. **Literal artifact.** Two symbols; one doubly infinite tape; every move L or R; all working states counted; separate halt label; blank tape and counted initial state; terminal write and move retained.
2. **Entire bootstrap.** A finite run to a recurrent frame, with the exact head and state and equality of the *whole* tape. A finite observed window is insufficient. List the complete one-cell support and establish that every other cell is zero.
3. **Recurrent resources.** Nine primary blocks `B(v)=0 1^(v+1)`, arbitrary natural register values, a nonempty arbitrary finite spare suffix, total head-to-header distance at least 40, and the actual clean/padded program counter. The lower bound is on the total distance, not only the zero gap after the counter.
4. **Universal local correctness.** Each changed box must retain its true guard, selected physical register, complete exterior tape, exit state, logical action, and all resource changes. Unary/list induction or a sound symbolic proof rule can establish this. Testing many concrete values cannot establish an unbounded contract.
5. **Complete source coverage.** Parse the complete 6,459-node/6,460-leaf literal decoder and all 8,391 guarded cases. Cover return/carry overflow and trailing zero bits. Bind that decoder to the source of `Bisim254.prog254_halts_iff`.
6. **Positive segments and halting reflection.** A logical step must correspond to a positive finite segment of the binary machine. Nonterminal segments end in active related frames and preserve the invariant. Induction on a binary halting time reflects a binary halt to a finite logical halt. This prevents silently accepting a stray or premature binary halt.
7. **Admitted root.** The actual root must satisfy `C254(T)`, `C254(H)`, and `Good(W)`. The six numerical fields `N,A,D,X,Y,L` may be arbitrary by `DirtyProgram254.six_nonformula_path_iff`. That freedom does not extend to arbitrary formula fields or stack contents.
8. **Composition.** Conclude `Halt(M,blank) ↔ C254(1)` and then apply the exact refutation comparison above. Ordinary finite combinatorial induction and a conventional ZFC proof are sufficient for the requested statement. Name accurately any absent new kernel endpoint.

The known 246 root has logical `(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`, so the dirty-root specialization is `(N,A,D,X,Y,L)=(3,0,3,0,0,0)`. Its complete prefix takes 410,735 transitions, enters old dispatcher 96 at head −5, has header 176 and marker −6, and has 167 spare blocks of value one. Formula codes 0 and stack 0 are already admissible. The source theorem for arbitrary initial candidate counter uses padded arbitrarily large encodings, so starting the enumeration at three loses no refutation.

## Guarded quotient criterion for an additional state saving

Let `f` map old recurrent control states to new states and preserve the halt label. For each actually reachable old state/read pair `(q,a)`, require equal write/move actions and target compatibility

\[
\delta'(f(q),a)=(b,D,f(r))
\quad\text{whenever}\quad\delta(q,a)=(b,D,r).
\]

Equality need only hold on a domain whose preservation is proved by the entire runtime invariant. Every omitted pair requires a proof of its exclusion; it cannot be omitted merely because finite runs failed to see it. This gives a direct step-for-step runtime simulation. An independently checked blank initializer can enter the new recurrent domain without being the image of the old bootstrap.

The 246 archive already uses this criterion twice: old 0 is entered on a forced one during marking and can reuse 20, disconnecting legacy 1 and 3; old 97 is entered on a one deposited by the preceding pulse and can reuse 255. Those two ideas and the start at old 95 are prior work for the present task.

## Novelty and claim calibration

Both `zfc-prefix247.zip` and `zfc-prefix247-research-20261017.zip` deliver the same 247 table, the same 741,241-step root, and the marking fold. The 246 archive additionally folds the pulse state and changes the blank initial state. Searches of the checked-out Research/ZFC Markdown and Python files found no claim of a 245-or-smaller working-state machine; this is a scoped repository search, not a worldwide-priority claim.

Do not claim that a graph-reachable table is minimal or that absence of ordinary exact bisimulation proves a lower bound. Do not claim unconditional nonhalting or consistency. Under `Con(ZFC)`, the constructed machine is nonhalting and ZFC cannot prove that nonhalting statement by Gödel's second incompleteness theorem. Excluding a ZFC proof of halting additionally requires a suitable soundness assumption, for example Σ1 soundness; mere consistency is not a general two-sided-independence argument.

Recommended result wording, if the new binary obligations pass: “An explicit [number]-working-state machine, with a conventional mathematical proof in ZFC and executable finite/symbolic certificates. The exact new table has not yet been compiled into a closed Lean/Rocq endpoint, and no PA-internal proof-code translation is claimed.”
