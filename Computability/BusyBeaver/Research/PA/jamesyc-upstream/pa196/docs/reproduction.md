# Reproducing PA196

Run the source and machine-table checks from the repository root with Python
3.10 or later.

```sh
bash scripts/check.sh
```

The checker verifies the exact table bytes and checks that the literal machine,
58,154-step startup, and standalone Challenge match their source inputs.
The default build uses Lean 4.35.0 and the committed Lake manifest. Install
[elan](https://github.com/leanprover/elan) and put its executables on `PATH`.

```sh
elan toolchain install leanprover/lean4:v4.35.0
lake exe cache get
bash scripts/check.sh --full
```

The Mathlib cache is optional. Lake builds the bundled Foundation modules and
the PA196 proof from source. A fresh build can take substantial time and
memory. See [Foundation's source and license](../vendor/Foundation/README.md).

The root [audit](../Audit.lean) checks the exact machine and both Palomar
declarations. Guarded audits also check the compiler and scheduler. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted in the compared
proofs. The two deliberate theorem holes are confined to the standalone
[Challenge](../Challenge.lean).

For the sandboxed statement comparison and independent replay, use Linux
with [Bubblewrap](https://github.com/containers/bubblewrap) and user
namespaces enabled. The script uses NanoDa and con-ron from the pinned Lean
toolchain.

```sh
bash scripts/verify-comparator.sh
```

Build the paper with `tectonic --outdir paper paper/pa196.tex`, or run
`pdflatex -output-directory=paper paper/pa196.tex` twice.

The [public PA209 snapshot](https://github.com/jamesyc/BusyBeaver/tree/69d98241a721ead20b4f0b17df9062950b40fbfe)
documents the predecessor machine and the shared arithmetic proof architecture.
The [K230 Rocq development](https://github.com/elliotglazer/k230-rocq/tree/3142e4d)
and the [PA238 Rocq development](https://github.com/jeff87654/busy-beaver/tree/84049b5/PA/m238)
supply background for the tape engine and proof calculus.
