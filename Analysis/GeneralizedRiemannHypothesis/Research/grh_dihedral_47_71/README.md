# Beyond Dirichlet GRH at conductors 47 and 71

Open **report.pdf** for the complete manuscript. **report.tex** is the entry point for the LaTeX sources. All paths are relative to this folder. Rebuild using a current TeX Live installation with `latexmk -pdf report.tex`. The precomputed illustration `ratios.pdf` is included.

## Proofs and inputs

Sections 1–5 cover the Lean reduction, a classification of the real zeros of the conductor-47 pencil, one-sided prime criteria, and interpolation and positivity at conductor 71. The appendices develop the general finite-group and dihedral character tests, Gaussian perturbation tests, and the classification for pairs of eta factors.

The main results proved here are mathematical arguments. The upstream Lean project proves zeta and Dirichlet GRH. The paper uses that theorem in the prime criteria and gives references to the independent verification. The critical-line conjectures for the nonabelian factors and the necessary all-scales prime bounds remain open. The additional arguments in this archive have not been formalized in Lean. Primary citations and pinned links to the earlier ProveIt reports appear in the paper. The JSON source manifest identifies nine upstream blobs.

## Reproduce the calculations

Use Python 3.10 or later. The certificate and sample scripts below use only the standard library. Run the scripts without Python's -O option so that all assertions execute.

| Command | What it checks or prints |
| --- | --- |
| `python check_threshold.py` | Exact rational enclosure of the two central values and their ratio at conductor 47. Printed endpoints are also in threshold.json. |
| `python check_level71.py` | Rational bounds proving positivity of all three conductor-71 theta kernels on a Fricke half-ray. |
| `python check_rotation.py` | Integer multiplicities invisible to incomplete rotation-class selections in five generalized dihedral examples. |
| `python check_detector.py` | Finite-group weight examples for the symmetric groups on three and four letters. |
| `python check_finite.py` | Rational interval signs of two cubic Jensen discriminants. |
| `python check_eta_pairs.py` | Fourier-coefficient obstructions among the twelve normalized eta pairs; the seven eigenforms themselves are identified by a cited theorem. |
| `python sample_primes.py` | Exhausts the three discriminant -47 forms up to one million, checks the sets against quadratic splitting, and rewrites prime_sample.csv. Prime counts are exact. The logarithmic sums are floating-point illustrations. |
| `python example71.py` | Numerical coordinates of the combination with a fourth-order central zero. The determinant formula in the paper specifies the coefficients exactly. |
| `python plot_ratios.py` | Recreates the illustrative figure using NumPy and Matplotlib. No plotting libraries are needed for any proof certificate. |
