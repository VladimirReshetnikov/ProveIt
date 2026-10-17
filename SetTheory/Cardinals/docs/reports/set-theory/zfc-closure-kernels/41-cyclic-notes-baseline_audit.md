ARCHIVE NOTE: This is a development or independent audit record. The final
article.tex/article.pdf and README.md are authoritative for the delivered
status and runnable archive commands. Some original workspace paths and
earlier-stage comments are retained as provenance. The final U14 source
and its 10,182-node wrapper are included under data/.

# Independent baseline audit and compiler artifacts

## Exact public baseline

The inspected main branch of `jeff87654/busy-beaver` is pinned to
`297ab8df7e5de329605c3875b4934643b371a5e3`. It includes Mira-Cult's 254-state
machine and Jeff's published end-to-end Coq verification. Public pull request
20 remains a distinct, unmerged 253-state submission at inspected head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, by mira-emmy. The 253-state result
is prior work, not a result of this report.

Both literal machines have one bi-infinite tape, two symbols, blank 0,
start state 0, L/R moves only, and a separate terminal state omitted from the
working-state count. Every working state has both transition rows.

| Machine | Working states | Rows | Literal checked boot | Absolute final head | One-cells | Spare blocks |
|---|---:|---:|---:|---:|---:|---:|
| Mira-Cult / Jeff | 254 | 508 | 264,982 steps | -8 | 149 | 136 |
| mira-emmy PR20 | 253 | 506 | 312,975 steps | -17 | 178 | 158 |

The new independent `audit_public_baselines.py` reads only table data. It
checks the pinned SHA256, all rows, target closure, graph reachability,
ordinary exact-step partition refinement, and the complete finite support
of the final infinite tape. The final head is independently fixed in both
specifications. No upstream simulator or generator is imported.

For 254 the final state is 96, the header is 62 cells right of the head, and
the primary physical register values are `[0,0,0,0,0,0,2,0,0]`. For 253 the
final state is compact 33, the PC prefix is `000`, the header is 40 cells
right of the head, and physical values are `[0,2,0,0,0,0,5,0,0]`. The 158
spares have value 1 at zero-based indices 2 and 8 and value 0 elsewhere.

The exact-step partition is discrete for both tables. These are restrictions
on same-step state quotients of the fixed tables, not lower bounds on machines
with the same blank-tape halting predicate. The boot checks are finite
computations, not replacements for unbounded runtime proofs.

The upstream PR20 `--source-only` check also passed independently: exact
253-state / 506-row identity, Coq literal-table maps, a dependency closure of
160 source files, and 194 assumption probes. No Coq compiler was available
locally, and no new kernel rebuild is claimed. Upstream's published proof
endpoint concerns finite refutations of its explicit SIR, closed ZF, and
ZF+AC presentations. Export to a fixed internal ordinary-ZFC proof predicate
remains a separate statement and is not obtained merely by importing Coq.

The origin URL `https://github.com/Mira-Cult/turing-machines` returned 404
through both the GitHub connector and the web lookup during this audit. This
does not prevent auditing the frozen literal tables and committed proof
sources. It does limit access to the original author's unavailable
`source.py` and `paths.json`; verification of the committed tables does not
require those files.

## Exact table identities

254 SHA256:
`d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`

253 SHA256:
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`

Local inspected files:

- `baseline_work/busy-beaver/ZF/m254/machine/zfc_254.tm`
- `baseline_work/public253/ZF/m253/machine/zfc_253.tm`

No repository-wide license or package-specific license for `ZF/m253` or
`ZF/m254` was found in the pinned upstream trees. ProveIt's existing
`lib/jeff-busy-beaver-zfc254/README.proveit.md` explicitly excludes its
upstream snapshot from ProveIt's blanket MIT-0 grant. Any copied tables should
retain the existing authorship and this license boundary. Their inclusion
must not be described as a new license grant or as relicensing under MIT-0.
No vendored Coq library is needed to run the independent finite table audit.

## Primary source links

- [Upstream ZF README](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/README.md)
- [254 machine README](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/README.md)
- [254 literal table](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/machine/zfc_254.tm)
- [254 endpoint theorem](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/e2e/E2E254.v)
- [PR20](https://github.com/jeff87654/busy-beaver/pull/20)
- [Pinned 253 README](https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/README.md)
- [Pinned 253 literal table](https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm)
- [Pinned four-row generator delta](https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/tools/generate_candidate.py)
- [ProveIt attribution/license boundary](https://github.com/VladimirReshetnikov/ProveIt/blob/8cf840b8a26d002041e7a26dc9688ce7ce5fd751/lib/jeff-busy-beaver-zfc254/README.proveit.md)

## Reproduction in the present workspace

```sh
python3 baseline_work/audit_public_baselines.py \
  --machine254 baseline_work/busy-beaver/ZF/m254/machine/zfc_254.tm \
  --machine253 baseline_work/public253/ZF/m253/machine/zfc_253.tm \
  --output baseline_work/public_baseline_audit.json

python3 baseline_work/test_phase_optimizer.py \
  --reference logic_work/rotation9.py \
  --output baseline_work/phase_optimizer_results.json

python3 baseline_work/test_phase_optimizer8.py \
  --output baseline_work/phase_optimizer8_results.json
```

For a compact archive, place the four compiler/test Python modules together,
and preserve `rotation9.py` separately or pass its archive location through
`--reference`. The reference option is optional: omitting it still runs the
independent normal-form optimality oracle and finite algebra checks. The
machine-audit arguments accept any paths to the two exact pinned tables.

Recommended new artifacts to include are the audit script and JSON, the two
phase optimizers, the two test scripts, their two result JSONs, and
`PHASE_COMPILER_NOTES.md`. The large exploratory `runtime252_trace.json`,
`trace_runtime252.py`, local Git checkouts, and build products are not
deliverables. No new 252-state consistency machine was found.
