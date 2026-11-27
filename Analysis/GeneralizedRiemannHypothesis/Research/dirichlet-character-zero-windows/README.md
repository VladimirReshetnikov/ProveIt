# Identifying a primitive Dirichlet character from a short window of zeros

Read character_windows.pdf for the theorem, proof, scope, comparisons with prior work and references. character_windows.tex is the complete source. The Dirichlet GRH input is the upstream Lean theorem identified in the paper. The downstream results are mathematical proofs in the manuscript. The computations below illustrate two steps.

## Rebuild the paper

In a standard TeX Live environment with the packages named in the preamble, run the following command twice from this directory.

    pdflatex -halt-on-error character_windows.tex

The bibliography is embedded in the source.

## Reproduce the numerical examples

From this directory run the following commands.

    python3 experiments/probe_example.py
    python3 experiments/signed_zeros_mod5.py

The first uses the Python standard library. Its expected output is experiments/example_output.txt.
It computes a compactly supported prime-side kernel for the conjugate quartic pair modulo 101.
It uses a fixed smooth taper and reports actual off-diagonal weights.

The second requires mpmath (tested with 1.3.0). Its expected output is experiments/signed_zeros_mod5.json.
It computes sign-changing zeros of the two Hardy functions on [-10,10] at 45-digit working precision,
compares them with LMFDB and checks conjugate reflection. This local check uses floating-point
arithmetic. The conclusions of the paper are independent of these examples.

## Source snapshots

- grh-lean, 72fead102f663d5c7a407964a13dc0cf9d977207. See grh/src/Statements.lean, grh/src/Main.lean and grh/README.md.
- ProveIt, f6b9918d87befd09f8786df70e668452171abb89. See Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex, especially the labels rec:cor:quadsep, rec:thm:quaddisplace and rec:sec:open. Relevant comparisons also appear under dir:lem:bias in dir.tex and zer:thm:short in zer.tex.
- Salem Eid, revised July 2026 manuscript, DOI 10.5281/zenodo.21326653, Theorems 1.1 and 1.3. This is the closest comparison we found outside the two supplied repositories.
