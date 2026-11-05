# Diagnosis of the retained v2 duplicate-Init failure

The 61-module extension stopped before compiling its first module, `DiophantineConsistency.WangTiles942Core`. Its retained dependency stdout contains five lines: the identical lexical path `/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean` occurs twice, followed by the three distinct paths corresponding to the source's declared imports. The staged source and pinned manifest both declare those same three imports and no explicit `Init`; dependency stderr is empty. This observation does not establish why Lean emitted the duplicate.

The v2 driver rejected the second entry as `('duplicate import', 'Init')`, leaving its `records` list empty. The coordinator recorded the driver exit as 1, and the separate supervisor receipt recorded its coordinator child exit as 1 and status `FAILED`. This packet does not independently observe the supervisor's own outer session exit. The failure artifacts remain in their original `/tmp` locations; no Lean command or new build was run here.

The v2 terminal verifier would independently reject this exact stdout even if the driver accepted it: it requires the number of raw dependency lines to equal the number of unique recorded direct inputs. The later two-client runner has its own unconditional duplicate-module check, so a consistent repair should address it as well.

A narrowly scoped repair can allow at most two copies of `Init` only when their original path strings are identical, authenticate that one producer and its companions, retain and hash the **unmodified raw stdout**, and require every other module to occur once. Conflicting paths for the same module, even aliases resolving to the same object, a third `Init`, non-`Init` duplicates, missing declared imports and extra dependencies should still fail. This policy is a recommendation, not an accepted or checked v3 implementation.

The older fresh-base builder already accepts repeated dependency lines for a module if the lexical provider path is the same; v2's unconditional duplicate rejection is stricter. The retained artifacts are point-in-time evidence and do not establish the outcome of any successor build. A successor must use new pinned code and fresh output paths rather than overwrite these failure artifacts.

The read-only [checker](check.py) authenticates the relevant state, source, manifest, dependency logs and supervisor/coordinator evidence and verifies the counts and declared-import relationship. It does not execute Lean.

```
python3 -I -S -B path/to/current14-extension-v2-duplicate-init-diagnosis/check.py
```

The deterministic output is frozen in `result.json`.
