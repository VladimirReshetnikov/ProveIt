# Build and validation

Requirements:

- Python 3.11 or later (standard library only for the reference checks)
- a LaTeX installation with `latexmk`, `pdflatex`, `amsmath`, `mathtools`,
  `booktabs`, `longtable`, `listings`, `hyperref`, and `cleveref`

Run:

```sh
bash build.sh
```

The script deliberately does not claim to build the Lean blueprints.  No
Lean/Lake executable was available in the artifact environment.  Complete
formalization requires placing `lean/` in the pinned ProveIt workspace,
replacing every visible placeholder, running `lake build`, and auditing public
theorems with `#print axioms`.
