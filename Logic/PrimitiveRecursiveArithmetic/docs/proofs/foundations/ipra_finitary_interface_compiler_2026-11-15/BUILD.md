# Build notes

Requirements:

- Python 3.11 or newer (standard library only)
- a TeX installation with `pdflatex`; `latexmk` is preferred

Run:

```sh
bash build.sh
```

Expected outputs:

- `verification/python_tests.txt`
- `verification/example_generation.txt`
- `verification/latex_build.txt`
- `paper/ipra_finitary_interface_compiler.pdf`

The Lean sources require the root ProveIt Lake workspace at the pinned commit.
They are intentionally excluded from the local build because Lean was not
installed in the artifact runtime.
