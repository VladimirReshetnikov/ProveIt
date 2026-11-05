# Independent P64 replay on captured providers

On 2026-11-04 an independent run forcibly rebuilt the eight P64 modules,
in order, against an isolated overlay of the previously captured P65
providers. The observed outer tool session **91344 exited 0**; each of the
eight recorded Lean invocations exited 0, with no warnings, errors or
`sorryAx`. The endpoint reports `positiveBridge`, `native_equivalence`,
`standard_equivalence` and `reference_equivalence` with
`[propext, Classical.choice, Quot.sound]`. These are Lean metatheory axioms,
not additions to the object theory.

The endpoint's exact statement is the Lean expression's positive-model
halting bridge and the native, standard and equality-only iPRA derivability
statements using the selected mapped Foundation refutation negation. It is
not a decision of ZFC consistency.

| Fresh module | Exit | Seconds |
| --- | ---: | ---: |
| P64Graph | 0 | 3.930 |
| P64Root | 0 | 38.411 |
| P64Norm | 0 | 17.575 |
| P64Early | 0 | 4.430 |
| P64Facts | 0 | 22.058 |
| P64ConvZero | 0 | 2.726 |
| P64Converse | 0 | 32.279 |
| IPRAPositive64 | 0 | 44.833 |

[`results.json`](results.json) retains every source, rewritten source, direct
import, command, exit, log and object hash; [`logs/`](logs/) retains each
complete Lean log. [`result.json`](result.json) records the nine distinct
external direct-object guards, the Lean search path and the preceding P65
captured-provider audit. [`terminal-observation.json`](terminal-observation.json)
records the observed outer exit, runner and result hashes and the successful
read-only [`audit.py`](audit.py) result. The audit rechecks the retained logs,
source/shim and output objects, direct imports and endpoint reports while the
recorded `/tmp` objects remain available.

## Exact import boundary

[`run.py`](run.py) pins the eight canonical source hashes and Lean binary,
refuses an existing output directory, checks the earlier P65 provider audit,
and creates a new symlink overlay with no pre-existing P64 output objects.
It copies each exact canonical source into the temporary source tree except
for one import-only substitution in `P64Graph`: its first line
`import DiophantineConsistency.Compact44.FreeJSumSquares` is replaced by
`import P65GraphShim`. That shim's imported object is separately hash pinned;
the P64 graph body and its other import are unchanged. All eight objects are
fresh outputs rather than cached selected objects. The runner hashes the
resolved direct imports, guards them and source files after each stage, and
checks all previously rebuilt selected objects after each stage.

To repeat only in the same captured environment after choosing a fresh output
directory in a copy of the runner, execute it from the repository root; it
intentionally refuses to overwrite `/tmp/p64-independent-captured-replay`.
The paths and temporary objects are machine-specific. The audit command is:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/fourteen-p64-independent-replay/audit.py
```

This is a single independent captured-provider replay, not a two-builder
paired replay or a clean current-source rebuild of the whole dependency
closure. It does not authenticate the full project, package or dynamic
ancestry of inherited objects, and after-the-fact guards cannot exclude
transient changes between observations. The P65 audit it reruns has its own
recorded captured-provider limits.

## Literal and payload scope

The P64 source gate block has a separate external 83-gate comparison with
`positive14/polynomial.json`; its exact degree is a package claim, not a Lean
degree theorem. The Lean endpoint uses the symbolic compact44 tuple. Exact
identity with retained coefficient payloads or a rendered page is an
external binding, not a theorem interpreting JSON, gzip or PDF bytes. At the
time of this replay the JSON's referenced
`positive14/native/COEFFICIENT_BINDING.json` was absent at that path; the
missing package files have since been restored in the separately recorded
[payload provenance packet](../fourteen-p64-payload-provenance/README.md).
`positive14/SOURCE_PINS.json` records its historical
Git blob `c54f7f1ce0698a5aad3bf56722c3dde343db6dff`, which is available in
the local object database; matching the restored bytes does not establish
a Lean equality to the payloads.
