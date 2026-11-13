# Reproducing PA209

From the repository root, run the source and machine-table checks with
Python 3.10 or later.

```sh
bash scripts/check.sh
```

Install [elan](https://github.com/leanprover/elan) and place its executables
on `PATH`. Build with the pinned Lean 4.35.0 toolchain and committed Lake
manifest.

```sh
elan toolchain install leanprover/lean4:v4.35.0
lake exe cache get
bash scripts/check.sh --full
```

Mathlib's cache is optional. Lake builds PA209 and the bundled Foundation
modules from source. A fresh build can take substantial time and memory.
See [Foundation's source and license](../vendor/Foundation/README.md).

On Linux with [Bubblewrap](https://github.com/containers/bubblewrap) and
user namespaces available, run Comparator with its independent NanoDa check.

```sh
lake comparator --config comparator.json
```

The root [audit](../Audit.lean) checks the literal proof endpoints and both
compared theorems for dependencies beyond `propext`, `Classical.choice`,
and `Quot.sound`. The two declarations in
[Challenge.lean](../Challenge.lean) use intentional statement holes.
The verified declarations come from [Solution.lean](../Solution.lean).

Build the paper with `tectonic --outdir paper paper/pa209.tex` or run
`pdflatex -output-directory=paper paper/pa209.tex` twice.

The [K230 Rocq development](https://github.com/elliotglazer/k230-rocq/tree/3142e4d)
and the [PA238 Rocq development](https://github.com/jeff87654/busy-beaver/tree/84049b5/PA/m238)
supply background for the tape engine and the proof calculus. The
restricted implicational proof adapted from
[ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/6809609)
retains its [MIT-0 notice](../vendor/ProveIt/LICENSE).
