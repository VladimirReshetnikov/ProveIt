# Weighted Rank Five and Covers with a Two Vertex Shore

This package proves that every weighted bipartite matching-support polynomial with a minimum vertex cover meeting one shore in at most two vertices is ultra-log-concave after normalization by its matching rank. In particular all positive two-shore weighted instances through matching rank five satisfy the inequality, and the first weighted failure rank is exactly six.

The main proof is an explicit transversal matroid lift with q+2 slots for every displayed 2+q cover. It proves the stronger Lorentzian property of the full homogenized left marginal when right activities are fixed. The report also includes:

- An exact positive-integer rank-six obstruction and a family at every rank at least six
- The precise augmented-edge-polytope and stable-set-complement Ehrhart corollaries at unit activities
- A generic-line model for forcing both vertices of the two-vertex cover shore
- The optimal all-core constant 2q/(q-1), including an independent rank-five coefficient and sum-of-squares certificate
- Independent star-core Lorentzian transfer proofs
- Exact first-gap equality and quantitative eventual strictness under two activity scalings

## Read

`article.pdf` is the final report. `article.tex` includes the named section files in this directory. The main theorem and proof are in Sections 1–4; the exact negative examples are in Section 5. Supporting refinements and certificates are in the appendices.

These are ordinary mathematical proofs, with exact checks, not Lean-certified or peer-reviewed results. Global priority is not claimed. The theorem does not assert real-rootedness or stability of the original support polynomial.

## Verify

Use Python 3.10 or newer and SymPy:

    python -m pip install -r requirements.txt
    python checks/run_all.py

The scripts regenerate their exact JSON outputs in `data/`. They use fixed seeds for finite weighted examples; all arithmetic comparisons are exact. The universal proof is the six-case matroid basis identity, not an inference from these finite examples.

## Build

With a standard TeX installation:

    pdflatex article.tex
    pdflatex article.tex

The included `build_local.sh` additionally handles the TeX format/font configuration used for this PDF. It requires the usual amsmath, amsthm, mathtools, geometry, Latin Modern, microtype, booktabs, hyperref and xurl packages.

`SHA256SUMS` records the delivered files. `PROOF_STATUS.md` distinguishes proofs from finite regression checks. `qa_report.json` records the final artifact checks.
