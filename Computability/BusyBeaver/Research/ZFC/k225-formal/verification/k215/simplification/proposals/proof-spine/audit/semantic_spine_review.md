# Independent review: Lean semantic-spine proposal

## Verdict

**Static source audit passes for the revised 12-file patch; Lean acceptance remains unverified.** The proposal is a useful dependency-boundary refactor, not a demonstrated reduction in theorem proof terms, mathematical hypotheses, or whole-repository source size. Its strongest immediate benefit is making the generic semantic route independent of the CP/GIC specialization wrappers.

Reviewed baseline: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.
Reviewed patch SHA-256: `0ded72b5aff3cea1a53f6637c25fcf4fd7906784ee996388b412b63d1658998f`.
No Lean compiler, repository program, downloaded generator, or installer was executed.

## Independently reproduced evidence

The independent audit uses its own exact unified-diff application, comment-aware import scan, Git-blob checks, and lexical declaration inventory. It does not import the proposal author's checker.

- All 203 fetched baseline sources match their recorded Git blob hashes and sizes; the selected convenience copies match those baseline bytes.
- The patch applies with exact line/context matching, without fuzz or offsets, to the eight changed baseline files and creates four new Core files. Its outputs equal all 12 supplied candidate files.
- The selected endpoint is `BusyBeaver.ZFC.KEndpoint215`. Counts include this root and all recursively imported repository modules, excluding the Lean toolchain/Init source.
- Endpoint source closure: 174 to 168 modules, 1,752,650 to 1,725,295 bytes, and 37,648 to 37,117 physical lines. This is minus 27,355 bytes and 531 lines.
- Maintained-source change: **plus four files, 1,152 bytes and 46 lines**. Unchanged files elsewhere cancel in this delta. The earlier 11-file draft's plus 1,114 bytes/45 lines is obsolete after the compatibility repair.
- Four generic source regions are identical after removing import lines and boundary whitespace. They retain their original namespaces. All eight specialization theorem tails are verbatim. The lexical inventory of 4,239 explicitly named declarations across the fetched set is unchanged.
- Three endpoint-client edits are limited to import routing and the two `QuotientModel` to `KQ1Model` references; the additional `WFModel` edit is one explicit compatibility import.
- There are no missing repository imports or cycles in the selected endpoint or four Core closures. No qualified references to the removed CP/GIC wrapper modules remain in that endpoint.
- A broader lexical loss-of-declaration scan across fetched modules and the new Core bodies finds no remaining candidates after the repair. This scans explicit declaration names, not generated structure fields, tactic extensions, or Lean's name-resolution state.

The 203 fetched files are **not the entire repository**: the supplied metadata contains 2,263 entries. Some non-endpoint fetched files already reference unfetched `L2Dom`/`Seed222` modules. Those are not introduced patch defects. The audit therefore does not certify a whole-repository build.

## A real compatibility issue was repaired

The initial draft left `WFModel.quotient_models_ZF` using `WellFoundedPart.quotient_wf_closure` without its defining module. Previously that declaration arrived transitively through `WFModelCore -> WFRelativization -> WellFoundedPart`; retargeting the last edge to `WellFoundedPartCore` removed it.

The revised patch adds `import BusyBeaver.ZFC.WellFoundedPart` directly to `WFModel`. This also restores the CP/GIC specialization declarations relied on through `WFModel` by `WFTheory`. The endpoint metrics do not change because `WFModel` is not in the selected endpoint closure.

This incident is why compilation of the generic endpoint alone is not sufficient evidence of compatibility. The old specialization clients must also be built.

## Mathematical interpretation and limits

1. **The generic quotient is retained.** Six `Quotient*` specialization modules leave the selected closure, but `KQ1Model`, `KQ1Separation`, `KQ1Basic`, `KQ1Replacement`, `KQ1Power`, and `KQ1Collect` remain. This does not eliminate bisimilarity, the quotient construction, or the semantic interpretation.
2. **There is no new mathematical proof in this patch.** Singleton indices, finite graph attempts, ordinary Infinity, and internally well-founded-part closure keep their existing arguments and formulas. The patch separates generic reasoning from specialization. It should not be advertised as proving a shorter Infinity argument or a stronger consistency theorem.
3. **Hypotheses are preserved, not weakened.** `SingletonInfinity.Base` still has its formula-indexed Separation field. `FiniteSets.Base` still adds Union. `InductiveAttempts.ordinary_infinity_of_container` retains its functional Replacement premise and singleton-container construction. `WellFoundedPart.wf_closure` still uses the displayed GIC witness instance. No inference of Collection from Replacement without Foundation is introduced or justified.
4. **Internal well-foundedness is not external well-foundedness.** The represented-set interpretation and its formula translation remain unchanged. No metatheoretic well-foundedness or canonical-witness choice is obtained by file extraction.
5. **The alias replacement is well motivated.** At this pin, `QuotientModel.memberForm` is an abbreviation of `KQ1Model.memberForm`, and `QuotientModel.sat_memberForm` forwards to the corresponding generic theorem. The source-level change avoids an unnecessary specialization import. Definitional equality and elaborated proof-term behavior still require Lean validation.
6. **Import size is not proof size or trust.** A smaller imported source closure does not establish smaller kernel terms, fewer axioms, faster builds, or less memory. Those need separate measurements. Preserving the text of a tactic proof does not ensure the same elaboration when imports, instances, notation, or simp declarations change.

## API and module-boundary caveats

The original four module paths remain compatibility wrappers, with their original theorem names. However, global declaration preservation is not universal source compatibility: importing `KQ1ZF`, `KLowerQHyp`, `WFRelativization`, or `WFModelCore` no longer incidentally imports every former CP/GIC declaration. For example, a downstream file importing only `WFRelativization` and then using `WellFoundedPart.quotient_wf_closure` must add an explicit `WellFoundedPart` import.

The lexical scan observes 61 fewer explicit declarations exported transitively through the selected endpoint, and 173 fewer through `WFRelativization`/`WFModelCore`. These are diagnostic inventory counts, not semantic or compiler guarantees. The proposal should promise preserved named wrappers, not preservation of every historical transitive import accident.

There are no moved private declarations, instance declarations, syntax declarations, or local attributes in the four extracted generic regions that obviously require special renaming in this patch. One original mid-file `open Form` in `InductiveAttempts` is not repeated in the wrapper, but the retained adapter tail does not use the unqualified `Form` constructors introduced by that open. This is not presently an identified failure; a compiler check is still required.

## Generation and integration

The current `k225-formal` directory inventory names 32 `generate_*.py` files and no `generate_kq1.py`. The changed source modules have no generated-source banner. This supports, but does not prove, treating these files as maintained semantic source. A directory inventory cannot prove that no producer elsewhere writes them. The separately saved and blob-verified `generate_endpoints_lean.py` writes only machine-specific `KEndpoint{n}.lean` files, none of the twelve patch targets; static inspection therefore finds no conflict with that generator.

The proposal's `build_candidate.py` is a proposal-local text transformation, not evidence that the upstream producer pipeline has been updated. Integration should identify any authoritative producer for the eight modified modules, or explicitly record that they are maintained source; if a producer exists, update it and check that regeneration preserves the new module boundary. Do not run historical proposal generators indiscriminately.

Before acceptance, using the repository's pinned toolchain and approved build procedure:

- Build each Core module and each original compatibility wrapper independently.
- Build `KLowerQHyp`, `KQ1ZF`, `WFRelativization`, `WFModelCore`, `WFModel`, `WFTheory`, and `KEndpoint215`, then the supported aggregate target.
- Compare the endpoint theorem types and `#print axioms` output, especially `blank_halts_iff_zfc_refutation` and `nonhalting_iff_zfc_consistency`, plus generic and specialization consistency interfaces.
- Check downstream transitive-import consumers, generated artifact inventories, and any explicit build/module lists.
- Regenerate only with the approved authoritative producers, then require a clean or explained diff.
- Benchmark clean and incremental builds separately if claiming timing or memory improvements.

## Reproduction

From the bundle root, run `python3 audit/semantic_spine_audit.py`. The script is newly authored data-only audit code; it prints JSON and does not modify sources. It accepts either the working review tree or the compact delivery layout. The delivery uses `review/snapshots/current/` for the 174 endpoint sources and `review/snapshots/compatibility/` for 29 additional compatibility-review sources. Their baseline Git metadata is in `audit/semantic_spine_baseline_metadata.json`. It also reads `lean/current/`, `lean/candidate/`, and `lean/generic_spine.patch`. Saved output is `audit/semantic_spine_results.json`.

The source-to-pin provenance relies on the supplied fetch metadata. Blob identity was independently recomputed, but this review did not re-fetch the Git commit/tree chain. A hash match is content provenance, not a Lean correctness certificate.

A compact-layout reproduction test copied only the delivered input structure into a fresh temporary directory and produced byte-for-byte identical audit JSON.
