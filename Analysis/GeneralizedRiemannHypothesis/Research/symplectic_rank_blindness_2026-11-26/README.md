# Rank tests miss a persistent symplectic obstruction

Research note prepared for Vladimir Reshetnikov, 26 November 2026.

## Main result

Take a random symplectic transformation of a nondegenerate half-dimensional
input space, then project onto a fixed Lagrangian coordinate space. The resulting
square matrix has a rank distribution exponentially close to that of a matrix
with independent uniform entries. Its full matrix distribution stays a positive
distance away: 0.06880500650669452057... over the binary field.

The exact distinguishing test is whether the kernel is isotropic for the input
alternating form. It is impossible for the symplectic projection to have a
non-isotropic kernel. The paper proves the entire likelihood, exact finite total
variation distances, their asymptotics, and an extension to arbitrary input-form
rank. The broader theorem gives rank-distance at most kappa_q q^(-2s), where 2s
is the input-form rank, while the full distance tends to the same positive
constant whenever s grows.

The source of the research direction is the finite-field compression estimate
in `grh-lean` and an explicit open question in the supplied ProveIt symplectic
block report. The resulting theorem is a finite-field theorem and requires
neither RH nor GRH as a hypothesis.

## Read and reproduce

- `paper.pdf`: the complete proof and source analysis.
- `paper.tex`: its LaTeX source.
- `code/verify_formulas.py`: exact rational probability laws and certified limits.
- `code/exhaustive_check.py`: independent enumeration of actual frames.
- `code/make_figures.py`: figures from the exact formulas, without simulation.
- `results/`: all check outputs, tables, and numerical enclosures.
- `figures/`: PDF and PNG figures.
- `formalization/plan.md`: a concrete Lean development plan; no compiled proof
  of the new theorem is claimed.
- `provenance/`: pinned source audit, catalogue of previous work, relevant
  upstream source excerpts, and original license/notice material.
- `MANIFEST.sha256`: hashes of all deliverable files except the manifest itself.

From this directory:

```bash
python3 code/verify_formulas.py
python3 code/exhaustive_check.py
python3 code/make_figures.py
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

The first two scripts need only the Python standard library. Plotting needs
Matplotlib. The PDF was compiled locally with pdfTeX/LaTeX and visually inspected.
The normal LaTeX command above assumes an initialized local TeX installation.

## Verification status

The paper contains proofs for all mathematical claims in arbitrary dimensions
and every finite-field characteristic. Exact formula checks passed in 288
parameter cases. Independent exhaustive enumeration passed 4,371 individual
projection/Gram comparisons over 268,961 pairs of matrices. Numerical constants
have explicit rational enclosures. These finite checks support implementation
correctness; they are not the proof of the infinite families.

The new theorem is not yet a compiled Lean theorem. The large upstream GRH
development was inspected at its public declarations and relevant proof files,
not independently rebuilt in this investigation.

## Novelty and scope

The likelihood and the sharp separation between rank statistics and full matrix
statistics are absent from the inspected ProveIt predecessors. Targeted searches
did not locate the precise theorem in the primary literature consulted. Classical
symplectic counts and the independent-entry nullity law are credited as prior
tools. Global publication priority has not been certified.

This resolves the Lagrangian-output portion of the prior arbitrary-subspace
question. Both compressed spaces arbitrary remains outside this result.

## Pinned repositories

- `lsernau/grh-lean`: `72fead102f663d5c7a407964a13dc0cf9d977207`
- `VladimirReshetnikov/ProveIt`: `9ce7302df13ca8ea547135be83c794141da8d79c`

The artifact does not modify either remote repository.

## Third-party source material

`provenance/upstream_sources/` contains selected original `grh/` files from
the pinned upstream snapshot, with `LICENSE`, `NOTICE`, and `ATTRIBUTION.md`.
These are a source-reading snapshot, not a complete standalone Lean project.
Original paths and Git blob checks are recorded in the provenance manifest.
The new research code and prose are kept outside that directory.
