# Sparse Dirichlet mixtures as error-correcting codes

Research note, 27 November 2026. See `paper.pdf` for the theorem statements, proofs, source analysis, limitations, and bibliography. `paper.tex` is its complete LaTeX source. No repository modification was made.

## Reproduce

- `pdflatex paper.tex` three times (standard AMS/LM packages and hyperref).
- `python3 verify.py > verification.json` (Python 3.10+; standard library only). The checks enumerate Walsh-group rank-deficiency witnesses, both for uniform and nonuniform samples; check explicit inequalities for 9,999 values of the sparsity; and construct a balanced 24-prime example for the quadratic quotient of modulus 105. They are illustrations, not a substitute for the proofs.
- `SOURCE_AUDIT.md` records the inspected GitHub source, hashes, theorem interface, and comparison with the existing article.
- Optional: copy `InputAudit.lean` into the pinned readable `grh/` project and run `lake env lean InputAudit.lean` after its build. This is an input-interface check only, and was not executed here. The new result is not machine-formalized.

The analytic conclusions use the imported Dirichlet GRH and classical analytic estimates; the local-bias rigidity theorem itself is unconditional. All claims of novelty are provisional. The universal sample is proved to exist with effective-in-principle constants, not explicitly constructed for arbitrary Q. The finite example is not a numerical instance of the universal asymptotic cutoff.
