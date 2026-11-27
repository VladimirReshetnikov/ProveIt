# Distinguishing Dirichlet characters from low zeros

The nine-page paper proves a conductor-uniform finite identification theorem and a stability estimate. Its arithmetic input is the Dirichlet GRH theorem in the linked Lean project. The PDF and its self-contained LaTeX source are at the top level.

## Reading the paper

Theorem 1 gives the low-height result, including positive-only lists and the precise conjugacy ambiguity for folded data. Theorem 2 measures discrepancies after insertions, deletions and displacement in translated windows. Lemma 4 is the averaged prime-power interference estimate. Corollary 6 bounds the number of common prime probes from above and below. Corollary 7 identifies the factors of products from their pooled zero lists, with a fixed bound on the number of factors. The paper gives existence bounds with absolute constants for a single character. It does not evaluate a numerical universal threshold.

The references link to the upstream theorem declarations, the ProveIt reconstruction corollary and its open question at pinned commits. The new proof is written in LaTeX. The upstream Lean build was not rerun for this archive.

## Reproducing the checks

Run these commands from the top-level directory with Python 3. Assertions must be enabled.

    python checks/prime_dictionary.py
    python checks/quartic_certificate.py
    python checks/quartic_spectrum.py

Each script has a corresponding text file containing the output of the recorded run.

- The prime dictionary uses integer arithmetic and only the Python standard library. It checks every prime power in the specified enlarged windows and all 99 possible nonzero differences of character exponents modulo 101.
- The quartic zero certificate uses mpmath interval arithmetic, Euler–Maclaurin remainders, Cauchy bounds and Rouché's theorem. It proves the local zero count in the disk in the paper, independently of GRH.
- The quartic spectrum experiment uses floating-point zero searches. Agreement of the two meshes supplies a numerical consistency check. The disk certificate above supplies the rigorous assertion about one zero.

The recorded environment used mpmath 1.3.0, NumPy 2.3.5 and SciPy 1.17.0. The latter two packages are used only in the floating-point experiment. Its last displayed digits can vary with the platform.

## Rebuilding the PDF

Use a standard TeX Live distribution with the LaTeX packages listed in the source preamble. Run twice to resolve references.

    pdflatex -interaction=nonstopmode -halt-on-error character_zeros.tex
    pdflatex -interaction=nonstopmode -halt-on-error character_zeros.tex
