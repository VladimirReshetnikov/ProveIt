# Gaussian prime races

Open **Gaussian_prime_races.pdf** for the paper. The main LaTeX source is **prime_races.tex**. It loads the companion TeX files in this directory.

## Results

For the prime race between 3 and 1 modulo 4, the critical Gaussian smoothing time satisfies

    0.04007656562 < h_* < 0.04007656609.

Each class leads with positive logarithmic density below the threshold. Class 3 leads with logarithmic density one at the threshold and by a uniform positive normalized margin eventually above it. For every modulus the limiting mean classifies the thresholds for all pairs, and distinct inverse classes have equal winning densities at all widths. The paper also proves uniform one-dimensional occupation estimates, a full-dimensional limiting density for sums along d deterministic scales, and an explicit broad-window exponent.

## Reproduce the checks

Run these commands in the extracted directory, using Python 3.9 or newer. The first two checks need only the standard library.

    python3 certify_threshold.py
    python3 bound.py
    python3 verify.py

- **certify_threshold.py** checks both strict endpoints with rational interval bounds, allows uncertainty in every input ordinate, bounds the entire high-zero tail, and checks the harmonic derivative bounds near the threshold. Compare its output with **enclosure_output.txt**.
- **bound.py** checks an independent bound, h_* < 1/22, by enclosing a second moment of the zeros. Its output is in **bound_output.txt**. It requires no numerical zero data.
- **verify.py** uses mpmath 1.3.0. It sieves prime powers up to 24,154,953 and independently finds sign-changing beta zeros for the five illustrative comparisons in **checks.txt**. The floating-point example is separate from the exact endpoint proof.
- **plot_threshold.py** and **plot_model.py** reproduce the two included figure PDFs. They use NumPy and Matplotlib. The threshold plot also imports the rational certificate. The other plot uses 12,000 deterministic samples of a periodic model.

To rebuild the paper with a standard TeX Live installation, run the following command twice.

    pdflatex -halt-on-error prime_races.tex

The build produces prime_races.pdf. The distributed copy is named Gaussian_prime_races.pdf. The supplied figure PDFs allow compilation without running Python.

## Sources and verification scope

- The Dirichlet GRH input is the theorem in lsernau/grh-lean at commit **72fead102f663d5c7a407964a13dc0cf9d977207**. Relevant files are grh/src/Statements.lean, grh/src/Main.lean, grh/GUIDE.md, and the readable edition's New/Reduction/MainInequality.lean and OneSidedBound.lean under grh/src. Andrew Sutherland's independent verification records cover the short editions. The original Alpöge project has separate Lean FRO and Mathlib verification records. This work inspected the source and used those records for kernel verification.
- The ProveIt comparison used **041d8032541746f2ac2e686fbe437f8092771670**. The main directory is Analysis/GeneralizedRiemannHypothesis. Its merged 499-page article covers 61 packets. See Article/sections/zer.tex for the labelled multiplicity-rank, fixed-interval balancing and fixed-window modulo-four race theorems. The directory also has 48 later ZIPs under docs/incoming at this revision. The closest comparisons include grh_filtered_prime_races.zip, grh_multiscale_covariance.zip, grh_multiscale_prime_fluctuations.zip, and grh_prime_error_balancing.zip. This comparison is a reading of related results, not an independent formal verification of those packets.
- The Wikipedia article supplied the contemporary account of the proof, the zero-location formulation, and the link to prime-number errors through the explicit formula.
- The specific zero enclosures in the certificate use David Platt's data for the LMFDB primitive Dirichlet L-function of label 1-2e2-4.3-r1-0-0. Its Reliability page states the precision and completeness guarantee. This work reran the downstream rational calculations. The certificate takes those database inputs as given.
- The new proofs are mathematical arguments in the PDF. They have not been formalized in Lean. The bibliography identifies the fixed-width Knapowski–Turán result, Neroli's different Mellin family, and earlier results on prime distributions and analytic pushforwards. Priority for the exact formulations has not been established.

[Lean source](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207)
· [ProveIt source](https://github.com/VladimirReshetnikov/ProveIt/tree/041d8032541746f2ac2e686fbe437f8092771670/Analysis/GeneralizedRiemannHypothesis)
· [Original formal verification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
· [Short-edition verification](https://math.mit.edu/~drew/shortgrh/)
· [Beta zeros](https://www.lmfdb.org/L/1/2e2/4.3/r1/0/0)
· [Zero-data reliability](https://www.lmfdb.org/L/1/2e2/4.3/r1/0/0/Reliability)
