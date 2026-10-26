# Two new annotated-checker proof simplifications

Pinned source: `b310142330df89e48413c8fce62e7de223e1c7d5`.
All snippets are **uncompiled review candidates**. No Lean toolchain was installed, no source snapshot was edited, and no repository change was published.

## A. Reuse existing raw-table totality to remove the parent reconstruction induction

**Target:** [`AnnotatedParents.check_raw_iff`, lines 49–97](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/Computability/DiophantineConsistency/Lean/DiophantineConsistency/AnnotatedParents.lean#L49-L97).

The current proof repeats a 44-line expected-list/fuel/raw-code induction even though the preceding `check_lists` theorem already characterizes precisely the same check on an encoded list. The missing bridge is not a new mathematical theorem: existing `AnnotatedRenameScan.decodeTable_total` and `tableCode_of_decode` already imply that every natural number is `listCode (rows.map rowCode)` for some raw six-field rows.

Existing APIs:
- [`AnnotatedParents.check_lists`, lines 29–45](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/Computability/DiophantineConsistency/Lean/DiophantineConsistency/AnnotatedParents.lean#L29-L45).
- [`AnnotatedRenameScan.tableCode_of_decode` and `decodeTable_total`, lines 124–162](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/Computability/DiophantineConsistency/Lean/DiophantineConsistency/AnnotatedRenameScan.lean#L124-L162).
- Import chain already present: `AnnotatedParents → AnnotatedSchemaMaps → AnnotatedRenameScanPR → AnnotatedRenameScan`. No new import is required.

Replacement proof body:

```lean
  constructor
  · intro h
    obtain ⟨rows, hr⟩ :=
      AnnotatedRenameScan.decodeTable_total parents parents (Nat.le_refl _)
    have he : AnnotatedCodeArithmetic.listCode (rows.map AnnotatedRename.rowCode) = parents :=
      AnnotatedRenameScan.tableCode_of_decode hr
    refine ⟨rows.map AnnotatedRename.rowCode, he.symm, ?_⟩
    exact (check_lists fuel history expected _ hf).mp (by simpa only [he] using h)
  · rintro ⟨indices, rfl, h⟩
    exact (check_lists fuel history expected indices hf).mpr h
```

**Why it works.** `decodeTable_total parents parents le_rfl` returns a bounded decode at a sufficient external-natural fuel. `tableCode_of_decode` gives exact recoding, and `tableCode` unfolds to `listCode ∘ List.map rowCode`. Rewrite the raw input to that encoded list and use `check_lists` forward. Conversely, any supplied `indices` can be substituted and discharged by `check_lists` backward. No list-code injectivity lemma is needed.

**Preservation.** The statement, executable checker `check`, PR program syntax and its input behavior are unchanged. This is a `Prop` proof; the decoder is not inserted into the checker and does not affect the fixed checker fuel. Arbitrary row fields are not claimed to be valid formulas, contexts, or proof lines. The `hf : expected.length ≤ fuel` assumption is retained, not weakened. This theorem does gain a proof dependency on the existing external-natural bounded-decoder totality theorem; it does not add an axiom or an unbounded parser assumption. If avoiding this proof dependency is an intentional architectural boundary, retain the existing induction instead.

**Static size.** Whole replaced declaration: 49 → 15 nonblank lines; proof body: 44 → 10. Text bytes: 2,083 → 829 UTF-8 bytes. No kernel-term or runtime speed claim.

**Novelty boundary.** The six-packet exclusion audit found no proposal reducing `check_raw_iff` via `decodeTable_total` / `tableCode_of_decode` or list-code surjectivity. This is not the already proposed `lookup_code_maps_iff` simplification with `Option.map_injective`, removal of list lookup inductions, or a generic scanner/history-fold abstraction.

## B. Prove both decoder soundness invariants in one induction

**Target:** [`AnnotatedProofCode.Tree.decoded_depth_le` and `quote_of_decode`, lines 78–132](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/Computability/DiophantineConsistency/Lean/DiophantineConsistency/AnnotatedProofCode.lean#L78-L132).

Both proofs induct over the fuel, reject zero codes, split the tag, and inspect exactly the same two recursive option decodes. Only the terminal invariant differs: one bounds depth, the other proves exact requotation. Replace that duplicated traversal by:

```lean
theorem decode_spec {fuel code : Nat} {t : Tree}
    (h : decode fuel code = some t) : t.quote = code ∧ t.depth ≤ fuel := by
  -- One copy of the existing fuel/tag/recursive-Option case analysis.
  -- Each recursive IH supplies both quote equality and depth bound.
  ...

theorem decoded_depth_le {fuel code : Nat} {t : Tree}
    (h : decode fuel code = some t) : t.depth ≤ fuel :=
  (decode_spec h).2

theorem quote_of_decode {fuel code : Nat} {t : Tree}
    (h : decode fuel code = some t) : t.quote = code :=
  (decode_spec h).1
```

The complete 28-line combined declaration is in `AnnotatedCandidates.lean` and `proposed.patch`; the ellipsis above is explanatory only, not in either artifact. The atom case reuses `Nat.pair_unpair` for quotation and `1 ≤ fuel+1` for depth. The fork case receives four IH facts, rewrites the two child quotes for the first conjunct, and derives the maximum-depth bound for the second.

**Preservation.** No parser/code/depth definition changes. Retaining original theorem names and statements as projection wrappers preserves downstream API and existing use sites. Unlike a representation change, there are no changed numeric quotations or fuel semantics.

**Static size.** Both original declarations together: 54 → 34 nonblank lines, counting the new combined theorem and both wrappers. Proof bodies: 50 → 28 nonblank lines. Text bytes: 1,723 → 1,304. The fused statement strengthens the induction hypothesis but does not require stronger premises.

**Optional API, not counted in savings.** Combining `decode_spec` with the existing `decode_quote` gives `decode fuel code = some t ↔ t.quote = code ∧ t.depth ≤ fuel` in six declaration lines. It characterizes all raw natural codes, not merely `t.quote`. A candidate is included separately; the conservative patch does not add this optional theorem.

**Novelty boundary.** The six-packet manuscript and technical-note audit found no joint quote/depth decoder specification. Existing generic scanner-fold suggestions concern history accumulation, not a fuel-bounded recursive tree parser carrying two simultaneous invariants.

## Validation and artifacts

- `AnnotatedCandidates.lean`: complete standalone candidate declarations with `_short` names for non-conflicting future tests.
- `proposed.patch`: exact proposed changes against the pinned sources, not applied.
- `static_metrics.json`: reproducible static counts and source SHA-256s.
- `build_artifacts.py`: regenerates patch and counts from the source snapshot and candidate file.
- This file: mathematical rationale, scope and novelty notes.

Combined conservative patch: 103 → 49 nonblank declaration lines (54 removed, about 52%). The patch contains proof declarations only; it does not modify any executable definition. Actual elaboration, kernel checking, dependency axiom inspection and project CI remain to be run in the repository's existing Lean environment. In particular, test the proof-local `he` rewrite and implicit arguments in `check_lists`, and the option branch simplifications in `decode_spec`.

## Explicitly discarded prior-art candidate

`PRCode.Realizes.prec`, `ScalarPRCode.Realizes.prec` and `ScalarPROptimizer.eval_optimize` each contain a removable inner `Nat.rec` congruence induction. This looked promising, but the routed sixth packet `research/lean-proof-simplification-20261026` already supplies compiled replacements and a `RecursorCore.rec_congr` alternative (report §3.1, lines 114–130). It is **excluded**, not presented as a new idea.
