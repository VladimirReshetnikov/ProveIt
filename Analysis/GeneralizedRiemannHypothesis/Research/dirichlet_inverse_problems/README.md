# Three inverse problems for Dirichlet L-functions

Research notes, 26 November 2026. Each folder contains a self-contained paper, its LaTeX source, a reproducible calculation, and the recorded output.

## Suggested reading order

1. **Factorial samples of prime-power sums** (factorial/factorial.pdf, five pages). Given a primitive character, form a triangularly weighted sum of its prime powers at each factorial. Under the critical-line theorem, the running lag-one autocorrelation fails to converge, and its oscillations determine every zero multiplicity and hence the character. The paper gives both inversions, a mean-square distance formula, and the precise ambiguity for imprimitive characters. The identification uses infinitely many exact samples.
2. **Counting critical-line zeros from a fixed strip inside the Euler product** (phase_counts/phase_counts.pdf, five pages). Theorem 1 counts zeros from phases and logarithmic derivatives on finitely many lines with real part greater than one. Under Dirichlet GRH, refinement eventually succeeds at any two endpoints away from zero ordinates. Theorem 4 gives a finite test requiring only the classical critical strip. Its interval calculation encloses exactly one simple zeta zero at heights between 10 and 18 without using RH. The method and its computable error bound are the subject of the example. This zero has long been known. The final corollary extracts the maximal horizontal displacement from local Taylor radii.
3. **Detecting Dirichlet zeros with a sparse weighted count of prime powers** (residue_classes/residue_classes.pdf, four pages). For fixed modulus, choose one generator of each nontrivial cyclic subgroup. The normalized trace of the resulting residue is the total multiplicity divided by the group order. The note proves a two-way analytic criterion and gives a sharp classification of rational weights and their supports in the abstract multiplicity model.

## Source review

The readable project at commit 72fead102f663d5c7a407964a13dc0cf9d977207 exports Mathlib's RiemannHypothesis and results for all Dirichlet characters, including the theorem that zeros in the open critical strip lie on the critical line. Its one-sided reduction controls a smoothed sum supported on a progression and twisted by a quadratic character. The public statements, entry point and reduction can be read at these pinned locations.

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean

The supplied RH overview describes how the explicit formula encodes zeros as oscillations in prime counts. The first note samples those oscillations at factorials. The third asks when a weighted prime count can see a zero shared by several characters. The second uses the zero-location input in the opposite direction, turning phase information on the Euler-product side into local counts.

- https://en.wikipedia.org/wiki/Riemann_hypothesis
- https://math.mit.edu/~drew/shortgrh/

Andrew Sutherland's independent record reports successful builds, axiom checks and paranoid comparator checks for the shorter proof. We inspected the source and verification record. The three new notes contain mathematical proofs and companion calculations. They have not been formalized in Lean. Each note identifies nearby published work and the particular statement proposed as new. Historical priority has not been established.

## Reproduce the checks

Run from the directory containing this file. Python 3.10 or later suffices. The phase calculation also needs mpmath 1.3.0. Its interval operations use 40 decimal digits internally, with explicit truncation bounds for prime powers and the gamma terms.

    python factorial/check_factorial.py
    python phase_counts/phase_check.py
    python residue_classes/check_residue_classes.py

The factorial script compares actual prime sums for a character and its lift and checks a separate two-frequency model. The phase script encloses the integer count directly. The residue-class script checks the trace and support identities with exact arithmetic in four finite groups. The output beside each script records a successful run. For each paper run pdflatex twice on the corresponding .tex file in its folder with a standard TeX Live installation.

## Further research

- Give effective factorial sample lengths that distinguish primitive characters up to a specified conductor, allowing for closely spaced ordinates.
- Choose observation lines and split them between the phase estimate and the endpoint error bound to minimize total working precision at a prescribed height and interval width.
- Determine which of the abstract multiplicity patterns used in the support lower bound can be excluded by additional arithmetic information about shared zeros.

SHA256SUMS records the SHA-256 digest of every other file in this archive.
