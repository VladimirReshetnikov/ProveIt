# Sixth K215 proof-simplification checkpoint

This checkpoint keeps the exact 215-state machine and the statement that it halts iff a finite ZFC refutation exists. It adopts the normalized certificate from Source 168, the transition-lookup adapter from Source 175, and the semantic seed-model cleanup from Source 176. The reports and remaining proposals are reconciled in Sources 168–178.

The accepted run checks **187 project modules: 35 fresh and 152 reused** from the immutable 184-module phase-five checkpoint. Both unchanged typed endpoint clients pass, with ten reports using only `propext`, `Classical.choice` and `Quot.sound`. The selected project logs have 22 linter warnings and both audits have none. The individual kernel records, sources, dependency hashes, logs, toolchain and both audit objects were rechecked after the audits. This is an incremental checkpoint; it is not a claim that all 187 modules were freshly compiled.

| Change | Before | After |
|---|---:|---:|
| Source-certificate entries | 2,240 | 1,426 |
| Source partition files, total bytes | 438,399 in 18 files | 375,335 in 19 files |
| Additional generic normalized checker | — | 6,365 bytes |
| Seed-model source | 269 lines / 11,711 bytes | 240 lines / 10,710 bytes |
| Primary import closure | 184 modules | 187 modules |

Across the 21 adopted source and producer files, the total drops by 49,266 bytes. The three additional modules separate the normalized relation, stable program data and transition-lookup transport. All 16 certificate chunks and all nine site batches were freshly checked. Their 105 block statements still cover the same 4,751 leaves; the coverage facade retains its 104 joins.

The normalized relation identifies finite pointer lists with the same implicit trailing zeros. Its transport lemma preserves the complete instruction observation and consumed path. Increment and break operations still act on that consumed path. K215 explicitly uses 512 decoding steps, preserving paths up to 176 bits; the inherited 128-step interface is unchanged.

`KSource215Program` contains exactly the four moved program/tree declarations, with their qualified names and bodies preserved. Site modules import that stable data rather than the correspondence certificate. Future certificate-only changes can therefore reuse their validated providers. The site adapter rewrites through the existing all-state equality between the balanced transition lookup and the literal table. It introduces no new machine or tape semantics.

The seed proof obtains a derivable named bundle and uses the existing semantic encode/decode theorem. A direct bound on its double-negation code replaces formula-code positivity. Three unnecessary formula inductions disappear, with the same semantic definitions and seed endpoint statements. An unused helper hypothesis and eight simp arguments are removed too.

## Evidence and reproduction

- `lean/` preserves the completed primary run and its independent post-audit review, with an exact reference to the published phase-five evidence. No compiled objects are shipped.
- `proof-sources/` preserves the source changes, regeneration and structural controls, independent peers, and all isolated attempts, including the failed cleanup attempt. Its saved reader deliberately does not establish the full endpoint.
- [lean/review/root-actual-review.json](lean/review/root-actual-review.json) records a separate byte review of the complete current and predecessor provider sets.

To compile every current project module afresh, use a new output directory from the repository root:

```sh
python3 Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py \
  --repo . --out /tmp/k215-phase6-fresh
```

The maintained driver uses one compiler worker, a shared lock, a 12 GiB memory limit, and bounded module/audit processes. The historical incremental driver additionally requires the preserved phase-five cache. Saved-evidence readers need no compiler; their READMEs give the exact commands and predecessor reference.

The native table, dense table and source hashes remain the accepted K215 hashes. No new Rocq compilation, smaller TM, minimum-state bound, unconditional nonhalting result or internal-PA endpoint is claimed. Affine contraction, decoder factoring, alternative-machine transports and concrete zero-credit integration retain the gaps stated in their intake notes.
