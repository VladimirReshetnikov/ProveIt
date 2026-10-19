# Boolean bundle variants and the source bridge

## Results of the bounded final exploration

The fully normalized original bundle has **1,144 fine AX terminals**, compared with 1,270 originally and 1,162 after all six direct double-negation deletions. It uses six DNE deletions plus one additional negative-to-negative contraposition inside CP. It retains all eight original logical rows, GEN, input reads, gate, cleanup, and the final outer implication tag. Its exact data are in `boolean_first_variant.json`; the fine word alone is `boolean_first_variant.txt`.

The source shortening did not produce a new sub-245-state table during this branch. The supplied full-normalization grammar seed needed 142 decision rules before further search, illustrating why primitive source length is not a state-count result. The root report records the actual finished machine candidates and must be used for their final state and audit status.

A separate small family stays near original-layout DNE mask32, which changes only redex ID5. `boolean_local_variants.json` contains the mask32 control and 31 distinct **single local Boolean edits**, for 32 targets total. The shortest has 1,234 fine AX terminals. These are exact source targets for future grammar optimization; no new transition-table count is assigned to them.

## Logical justification

The common-core theorem in `dne_calculus_transfer.md` supplies MP, K, S, Peirce and ex falso for the actual numerical implication operation and falsity code. Therefore every instance of a classical implicational tautology is a common-core theorem. The six schemas used by the additional generator are:

| Rule | Left expression | Right expression |
| --- | --- | --- |
| Double negation | `¬¬A` | `A` |
| Negative contraposition | `¬A → ¬B` | `B → A` |
| Antecedent exchange | `A → (B → C)` | `B → (A → C)` |
| Negative antecedent exchange | `¬A → B` | `¬B → A` |
| Negative consequent exchange | `A → ¬B` | `B → ¬A` |
| Unpack negative implication | `¬(A → B) → C` | `A → (¬B → C)` |

Here every negation means implication to the same numerical `F=1`. All rows are equivalences, so both directional implications are classical tautologies. The propositional completeness theorem for arbitrary implication operations applies to their numerical instances. The GEN-plus-rho2 congruence lemma then transports the equivalence through any surrounding quantifiers, including a binder of variable0. No binding position, parameter identity, source gate, or schema domain changes.

Replace the old bundle axiom by any one of the checked new bundles. The same two proof inductions give equality of the entire numerical theorem sets. The explicit enumeration soundness invariant, derivation compiler, and cofinal padding proof therefore carry over exactly as in the DNE note. The new bundle still has an outer implication and can never be the literal halt code1; this preserves the stack-selector proof's tag premise.

## What the executable checker establishes

The standalone command

```
python boolean_bundle_variants.py --check
```

reads the pinned source formula specification and reproduces the mask32 expression. It checks each of the six abstract Boolean equivalences on all eight truth assignments to its three metavariables. For each supplied local target, it then replays the stated rule at the stated formula-position address, comparing the exact before and after subtrees. It reconstructs the full emitted AX word, verifies all unchanged logical rows and input events, checks the protected stack tail and outer implication tag, and compares the exact fine word and hash. It also independently replays all seven steps in the full 1,144-terminal target.

To regenerate the 32 local targets, run

```
python boolean_bundle_variants.py --generate
```

The local target ledger records a zlib byte count only as a sorting heuristic. That field is not a grammar-state estimate, a source certificate, or a claim of machine size.

The checker uses `check_dne_variants.py`, `macro_to_fine.json`, `boolean_first_variant.json`, and the small pinned `snapshot/ZF/m254/tools/logic/spec.py` fixture. It has no external Python package dependency. Its finite truth-table calculation validates the rule schemas; the uniform numerical proof relies on the common-core implication theorem stated and proved in the mathematical note.

## Grounding the fine-token source semantics

The fine words refer to the routed baseline's optimized structured source, whose internal increment order and control association can differ from the original Wade macros. The equality of one complete original AX string is insufficient to justify arbitrary new compositions of its substrings.

The independent `audit_macro_fine_bridge.py` resolves this specific issue. For each of the 19 macros appearing in the emitted words, it compares the original structured macro with the proposed fine expansion at the level of finite control-flow graphs. Between successive decrement guards it matches all nine accumulated register increments; it checks both outcomes of each decrement and the exact return. It rechecks all graph edges with the upstream path semantics. All 19 macros pass, with 192 paired states and 346 edges. These are all-register equations, not tests at sampled small values.

Consequently each symbolic RPN constructor step in the new word has the original macro's arithmetic effect, under the original macro contract's preconditions. Induction over the emitted word gives the exact changed bundle and unchanged AX interface. This connects the Boolean/calculus argument to the actual new structured source. The root's complete binary coverage and exact blank frame then connect that source to its literal transition table. These distinct compositions are all required; neither the truth tables nor the macro bridge alone is a complete machine consistency proof.

## Attribution and status

The underlying compact calculus, set-theoretic calibration and original constructor contracts are inherited and attributed as in `dne_calculus_transfer.md`. Prior incoming work already used the same common-core DNE transport for a quantifier-row replacement. This branch contributes fixed-bundle applications, exact altered source words, local rewrite certificates, measured complete controls, and the new source-interface composition.

No new Lean theorem build, unconditional nonhalting proof, minimality result, or 244-state candidate is claimed in these supplementary files. The full machine ledger belongs to the root report.
