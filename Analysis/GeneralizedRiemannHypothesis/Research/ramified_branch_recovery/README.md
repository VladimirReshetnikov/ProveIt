# Exact error correction for ramified branch measurements

Research note, 26 November 2026. Full mathematical proofs, source analysis,
exact computational certificates, and reproducible figures.

## Main result

Let `H(X,Y)` be an arbitrary formal power series over the two-element field,
and let `u_b(X)=(1+X)^b-1` for `b=0,...,15`. Observe the first `n`
coefficients of each of the sixteen series `H(X,u_b(X))`.

All 21 coefficients of `H` of total degree at most five are uniquely
recoverable despite any three entire branch records being replaced by
arbitrary records **if and only if `n >= 15`**. The higher coefficients of
`H` are unrestricted. The paper gives an explicit ambiguity at `n=14`.

The general theorem computes the exact relative block distance from the
contact tree of any finite set of distinct formal branches over a field.
A scalar dynamic program optimizes over every surviving branch set. It
also yields sharp corruption/erasure tradeoffs and a closed formula for
the precision at which the maximal distance is attained.

## Files

| File or directory | Contents |
| --- | --- |
| `paper.pdf` | Complete typeset research paper with proofs and references |
| `paper.tex` | Editable LaTeX source |
| `code/branch_recovery.py` | Contact trees, capacity recursion, exact binary arithmetic, reference decoder |
| `code/verify.py` | Main exhaustive checks and sharpness/decoding certificates |
| `code/independent_jet_check.py` | Independent direct substitution checks over F2, F3, F5 |
| `code/independent_tree_check.py` | Independent capacity implementation checked against subset enumeration |
| `code/independent_nonpacking_check.py` | Independent enumeration of all 8,008 ten-branch survivor sets |
| `code/make_figures.py` | Regenerates both figures using matplotlib |
| `results/` | Exact JSON certificates and the precision/distance CSV table |
| `figures/` | Vector PDF and PNG figures |
| `provenance/source_audit.md` | Source analysis, reading scope, and novelty assessment |
| `provenance/source_manifest.json` | Pinned repository commits and primary source URLs |
| `provenance/formalization_plan.md` | Precise proposed Lean decomposition; no formalization is claimed |
| `provenance/verification_summary.md` | Validation methods, counts, and limitations |
| `SHA256SUMS` | Checksums of the included files, excluding this checksum file |

## Reproduce the exact certificates

Run from this directory with Python 3.10 or later:

```bash
python3 code/verify.py
```

This requires only the Python standard library. It checks all 256 subsets
of an eight-branch grid, 240 capacity states against exhaustive search,
all 8,008 ten-element subsets of the sixteen-branch grid, direct
substitution matrices, an explicit failure at precision 14, and a
three-corruption decoding example at precision 15. It overwrites
`results/verification.json` and `results/phase_diagram.csv` deterministically.

Optional independent checks print their results to standard output:

```bash
python3 code/independent_jet_check.py
python3 code/independent_tree_check.py
python3 code/independent_nonpacking_check.py
```

The independent scripts use separate implementations, not imports of the
main theorem implementation. Their recorded outputs are included in
`results/independent_*.json`. They are internal verification, not external
peer review or proof-assistant certificates.

## Rebuild the figures and paper

The existing figures are sufficient to compile the paper. A normal
TeX Live installation with the packages listed in the LaTeX preamble is
required. No shell escape, bibliography processor, or network access is
needed for compilation.

```bash
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

To regenerate figures, install matplotlib and run:

```bash
python3 code/make_figures.py
```

The `Makefile` provides `verify`, `independent`, `figures`, and `pdf`
targets. `requirements-figures.txt` records the optional plotting dependency.

## Scope, attribution, and novelty

The analysis uses the specified `lsernau/grh-lean` development, the scoped
ProveIt research corpus, and the current Wikipedia discussion, with primary
verification records consulted for the RH/Dirichlet-GRH claim. Exact source
versions and reading coverage appear in `provenance/` and the paper.

The result is unconditional. It transfers local formal-series and valuation
ideas; it does not invoke RH as an assumption. The inspected GRH statement
covers Dirichlet characters, including imprimitive characters.

The mathematical ingredients include Bhargava's valuation orderings,
Amini's fixed-tree factorial merge, Berger–Sprang's qualitative branch
recovery, and the ProveIt packets' sharp clean-data bounds. The proposed
new contribution is adversarial leaf-retention optimization and its exact
total-jet block-error consequences, including the sharp nonpacking example.
A targeted search found no exact prior statement; global publication
priority is not certified.

No upstream Lean build or proof replay was run here, and no Lean proof of
the new theorem is supplied. The new theorem is proved in the paper.
The reference decoder is exact but enumerates candidate error sets; the
efficient capacity algorithm is not itself a fast error-location decoder.
The Lubin–Tate specialization is over the residue field, not over higher
powers of a uniformizer.

No upstream repository source files are redistributed in this archive.
