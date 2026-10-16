# Pinned 254-state ZFC consistency benchmark

Imported on 16 October 2026 from
[`jeff87654/busy-beaver`](https://github.com/jeff87654/busy-beaver), commit
[`297ab8df7e5de329605c3875b4934643b371a5e3`](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3).
The imported files are unchanged. Their upstream relative paths are retained
so the upstream checker can resolve its sibling packages.

**Mira-Cult designed and built the machine.** Jeff (`jeff87654`) supplies the
Coq verification imported here. The upstream
[`ZF/m254/README.md`](ZF/m254/README.md) credits
[`Mira-Cult/turing-machines`](https://github.com/Mira-Cult/turing-machines)
and describes the distinction between the machine and its subsequent formal
verification. This snapshot is a historical benchmark for ProveIt's
minimization work; it is not a ProveIt-authored machine or a new state-count
result. At the user's direction, subsequent formal verification work uses
**Lean**. The imported Coq sources remain unchanged reference material; no
Lean port is claimed.

## Machine and verification endpoint

[`ZF/m254/machine/zfc_254.tm`](ZF/m254/machine/zfc_254.tm) has **254
nonhalting states**, numbered 0–253, and two tape symbols, 0 and 1. It starts
in state 0 on a blank tape; state 254 is the halt state. The semantics use a
single, two-way infinite tape and L/R moves. Its exact SHA-256 is:

```text
d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb
```

The unchanged checker compares all 508 transitions against the Coq literal
table, builds the dependency closure of
[`E2E254.v`](ZF/m254/coq/e2e/E2E254.v), and requires three closed
`Print Assumptions` results. The upstream theorems connect blank-tape halting
with inconsistency of its explicit `ZFc`, `ZFc + AC`, and `SIR` presentations.
Their exact axioms and metatheory must be audited when connecting this
benchmark to a separately fixed ordinary ZFC proof predicate. Importing a
Coq theorem does not itself export a PA or ZFC derivation of that connection.

## Included source and provenance

The snapshot contains all **81** files under upstream `ZF/m254/`, including
its machine, Coq proofs, design notes, tools, and README; the exact **157-file
Coq dependency closure** computed by that directory's unchanged `check.py`;
the relevant upstream READMEs and vendor licenses; and five public
`ZF/generator/` files for the reproducible compiler experiments. There are **207
unchanged upstream files** in total. Dependencies shared with other upstream
machines retain their original `ZF/stdzf/` and `ZF/stdzf_r3/` paths.

[`upstream-manifest.json`](upstream-manifest.json) lists every imported
upstream path, Git blob ID, byte size, executable mode, role, and the checker
dependency order. The upstream root README is retained as provenance; links
to other machines or unselected sibling files may point outside this subset.

The author's `source.py` and `paths.json` are **absent from the pinned
upstream repository**. Some preserved generators refer to those original
bundle files. This import includes the complete published verification
package and its build dependencies, but cannot reproduce unavailable source
bundle artifacts or the original machine compilation from those files.
The end-to-end checker does not require them.

## Reproduce

From the ProveIt root, verify the snapshot and literal machine without Coq:

```sh
uv run --no-project python lib/jeff-busy-beaver-zfc254/verify_snapshot.py
```

To check manifest entries against a separate upstream Git clone, append
`--upstream /absolute/path/to/busy-beaver`. The helper performs no network
access, writes no build artifacts, and does not run the Coq compiler.

The upstream checker recommends **Coq 8.20.x**. Build on a scratch copy so
compiler artifacts stay outside the vendored snapshot:

```sh
task_build=$(mktemp -d)
cp -R lib/jeff-busy-beaver-zfc254 "$task_build/snapshot"
cd "$task_build/snapshot/ZF/m254"
COQC=/absolute/path/to/coqc-8.20 uv run --no-project python check.py
```

The local scratch attempt with installed Rocq **9.0.1** passed the literal
machine/hash check and compiled 19 dependencies, then failed at
`ZF/stdzf_r3/vendor/busycoq/Helper.v:5` because
`Lists.Streams` could not be resolved under `Stdlib`. An isolated Coq 8.20.1
installation attempt failed at the `ocaml-system.4.14.2` availability check,
before compilation. Coq work was then stopped at the user's request to use
Lean. **No local end-to-end Coq pass or Coq 8.20 build is claimed.**
[`build-status.json`](build-status.json) records these results. The upstream
reported successful build is not substituted for a local result.

## Public compiler backend

`ZF/generator/TMBuilder.py`, `tm.py` and `tmdb.py` are Andrew James Wade’s
public backend, distributed under the retained `LICENSE.wade` (MIT-0). The
upstream generator README records their source. They enable offline
reconstruction of the published 219-node DAG as a 281-state machine; they
are separate from Mira-Cult’s optimized interpreter. See
`Computability/BusyBeaver/Research/ZFC/compiler_route.md` for the exact
reconstruction and its verification limits. No original `source.py` is
recreated by adding this backend.

## License boundary

No upstream-wide license file is declared in the pinned `busy-beaver` tree.
**The imported snapshot is excluded from ProveIt's blanket MIT-0 grant.**
This import preserves authorship and does not relicense upstream work.
The nested dependencies retain their applicable notices:

- [`busycoq/LICENSE`](ZF/stdzf_r3/vendor/busycoq/LICENSE): MIT, Maja Kądziołka.
- [`busycoq/LICENSE-LibTactics`](ZF/stdzf_r3/vendor/busycoq/LICENSE-LibTactics):
  MIT X11, Arthur Charguéraud.
- [`undecidability/LICENSE`](ZF/stdzf_r3/vendor/undecidability/LICENSE):
  Mozilla Public License 2.0.

The vendor READMEs preserve their own source pins:
busycoq `bd2e36f6aa204eb011742d2ca6c8741102b2e59e` and the Coq Library of
Undecidability Proofs `70dfc56f33a6e4835281044e68aa68279989047e`.
`README.proveit.md`, `upstream-manifest.json`, `build-status.json`, and
`verify_snapshot.py` are ProveIt-authored import metadata, separate from the
unchanged upstream files.
