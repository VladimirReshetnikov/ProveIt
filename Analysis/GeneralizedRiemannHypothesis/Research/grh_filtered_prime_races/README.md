# Filtered prime races after GRH

Research package, 26 November 2026.

## Contents
- `paper.tex`: complete LaTeX source of the research note.
- `paper.pdf`: compiled, 9-page paper, including complete proofs, source analysis, references and research questions.
- `source_map.md`: inspected upstream source files, commit, theorem names, and verification scope.
- `experiment.py`: reproducible prime-power-only filter computation and numerical consistency checks. Requires Python 3 and NumPy.
- `example_q1.csv`, `example_q4.csv`, `example_q5.csv`, `example_q8.csv`: finite samples at 281 equally spaced logarithmic times from 5 to 12, with h=1.
- `experiment_output.txt`: actual output of running the script.
- `SHA256SUMS`: hashes of the deliverable files (excluding this manifest).

## Reproduction

    pdflatex -interaction=nonstopmode -halt-on-error paper.tex
    pdflatex -interaction=nonstopmode -halt-on-error paper.tex
    python experiment.py
    sha256sum -c SHA256SUMS

Run the hash check on the supplied files before rebuilding: PDF metadata and regenerated floating-point text may vary by environment. The numerical experiment was run successfully with NumPy. The PDF was compiled twice and visually inspected after correcting line overflow.

## Logical status

The zero-divisor tail rigidity theorem and ramp explicit formula are unconditional classical results proved in the note. The main uniform oscillation theorem uses Dirichlet GRH (including RH), as stated by the inspected Lean development. No zero simplicity, disjointness, or rational independence is used. The paper gives human-readable proofs; it is not itself Lean checked. The upstream Lean code was inspected selectively at the pinned commit and was not rebuilt here. Novelty of the exact formulation is a candidate claim based on a targeted, non-exhaustive search, not an established priority assertion. The sample eigenvalues are not certified bounds for the true second-moment matrix.
