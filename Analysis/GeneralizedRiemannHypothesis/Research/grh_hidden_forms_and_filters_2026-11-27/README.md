# Two research extensions of the ProveIt GRH program

**27 November 2026 · complete proofs, reproducible computations, and source record**

This package contains two new results relative to the inspected ProveIt revision. Both mathematical theorems are unconditional. The positive-filter paper also explains the application to prime-error modes under the repository's Dirichlet GRH input.

## Read the papers

1. **`papers/hidden_symplectic_forms.pdf` — Recovering a Hidden Symplectic Form.** A sharp additive threshold for statistical detection and exact recovery from random isotropic two-planes, valid over every fixed finite field, including characteristic two. Its source is `papers/hidden_symplectic_forms.tex`, which inputs `papers/sections/hidden_form_body.tex`.
2. **`papers/spectral_skewness.pdf` — The sixth-order cost of spectral asymmetry in shortest positive filters.** The explicit first nonzero term in the optimal width of a positive filter for a tight frequency cluster, with an exact local lower bound and equality criterion for three or four target occurrences. Its source is the standalone `papers/spectral_skewness.tex`.

The proofs reproduce their local geometric and analytic inputs. They can be read without building the upstream Lean project.

## Result 1: hidden-form recovery

Fix a prime power q and even n. Put D = n(n−1)/2 and d = D−1. Choose a projective nondegenerate alternating form H uniformly once, then sample t independent H-isotropic two-planes. Compare this planted experiment with t independent uniform two-planes.

One planted observation has exactly the same law as one uniform plane. Jointly, however:

- At t ≤ d−w(n), where w(n) tends to infinity, the two experiments have total variation tending to zero, and every estimator's exact recovery probability tends to zero.
- At t ≥ d+w(n), their total variation tends to one, and Gaussian elimination recovers H up to scalar with probability tending to one, uniformly in H.
- For each fixed integer a, the chi-square divergence at t=d+a converges to q^a/c_q, where c_q is the product of (1−q^(−(2j−1))) over j≥2.

The paper also proves explicit finite-dimensional bounds. At q=2 and n=200, d=19,899. At 19,889 observations, total variation is below 0.0171 and optimal exact recovery probability below 0.001165. At 19,909 observations, Gaussian recovery failure is below 0.000977 and its null false-positive probability is below 0.00082. The rounded inequalities are certified by exact rational comparisons.

The connection to ProveIt is exact for wide symplectic blocks with two-dimensional kernels **conditioned on full row rank**. The theorem does not silently extend this statement to unconditioned blocks. The below-threshold statement uses the specified uniform hidden-form prior; the above-threshold recovery guarantee holds for every fixed hidden form.

## Result 2: the sixth-order spectral penalty

For N≥3 nearby positive target frequencies, counting repeated entries as repeated Fourier-zero requirements, let kappa be the mean and delta_j=(lambda_j−kappa)/kappa. Set epsilon=max|delta_j| and p_3=sum(delta_j^3).

Among **all** probability measures whose Fourier transform vanishes to the prescribed orders, the minimum support diameter is

    B = N*pi/kappa
        + N*pi^5*p_3^2 / (180*(N−1)*(N−2)*kappa)
        + O_N(epsilon^8/kappa).

The minimizing measure is unique up to translation and has N+1 positive atoms. All terms of degrees one through five, and of degree seven, vanish after the mean is fixed. The sixth-order coefficient is positive and exact.

For N=3 or N=4, sufficiently close clusters satisfy the exact inequality B≥N*pi/kappa, with equality if and only if the centered multiset is invariant under negation. For example, a double zero at 1−epsilon and a simple zero at 1+2epsilon require width

    3*pi + (3*pi^5/10)*epsilon^6 + O(epsilon^8).

This is a fixed-N local theorem. It does not provide an explicit certified neighborhood or a general sign theorem along every higher-dimensional direction with p_3=0. Repeated Fourier-zero requirements are deliberate robustness constraints; they are not automatically required just because an arithmetic zero has multiplicity.

## Source and novelty

The repository was pinned at commit `00cadb961bbe77c74e5d082c4948f8884d58a970`:

<https://github.com/VladimirReshetnikov/ProveIt/tree/00cadb961bbe77c74e5d082c4948f8884d58a970/Analysis/GeneralizedRiemannHypothesis>

The main direct predecessors are the source labels `spn:q:symplectic`, `spn:thm:wide`, `spn:thm:wide-sample`, `fil:thm:split`, `fil:thm:differential`, and `fil:sec:open`. The source comparison includes the current, not-yet-merged Research packets. See `provenance/SOURCE_ANALYSIS.md` for the precise advances and remaining scope, and `provenance/source_manifest.json` for immutable paths and verified Git blob hashes.

The supplied repository itself takes the external Dirichlet GRH theorem as input and describes its article as a merge rather than a review. This work does not independently certify the entire upstream RH/GRH development. It proves the two extensions directly. A targeted search of related primary literature did not locate the exact new statements; this supports novelty relative to the checked sources, not an exhaustive global priority claim.

## Reproduce the checks

The exact finite-field programs require only Python's standard library. The symbolic/numerical filter checks and the figure additionally use the versions recorded in `requirements.txt`.

```bash
python3 -m pip install -r requirements.txt
python3 code/run_verification.py
```

The runner executes the four verifiers, writes their logs to `provenance/`, and updates the JSON data and figure. The numerical checks use 100-digit arithmetic but are not interval certificates. The proofs themselves are symbolic arguments in the papers, not inferences from the numerical experiments.

Individual commands, run from this package's root:

```bash
python3 code/independent_hidden_forms.py
python3 code/recovery_demo.py
python3 code/make_hidden_figure.py
python3 code/check_spectral_skewness.py --numeric
```

The first program independently constructs every two-plane and projective class of alternating forms in dimension four over F_2 and F_3. Its binary span process has 2,356 states and gives exact probability laws through 24 samples. The filter checker verifies identities for arbitrary symbolic N, 855 exact first-variation identities, 779 exact beta-coefficient identities, and 27 independent high-precision moment systems.

## Rebuild the PDFs

Use a standard TeX Live installation with pdfLaTeX and the packages listed in each preamble. The figure PDF is included, so Python is not needed merely to rebuild the papers.

```bash
make pdf
```

Set `PDFLATEX=/path/to/pdflatex` to choose an alternative executable. `make clean` removes only LaTeX auxiliary files. No network access is needed to run the mathematics or compile the papers once the dependencies are installed.

## Package map

| Location | Contents |
|---|---|
| `papers/` | Two complete papers in PDF and LaTeX |
| `code/` | Exact finite-field enumeration, recovery demonstration, rational finite bounds, figure generation, symbolic and numerical filter checks, check runner |
| `data/` | Reproducible JSON results, including the recorded sampled planes and recovered coefficients |
| `figures/` | The exact finite experiment and proved finite-bound comparison, in PDF and PNG |
| `provenance/` | Source analysis, hashes, proof review, detailed spectral derivation, successful verification/build logs |
| `FORMALIZATION.md` | A concrete module plan for future Lean formalization of the recovery theorem |
| `CHECKSUMS.sha256` | SHA-256 checksums of the delivered files, excluding this manifest itself |

No Lean formalization of the new theorems is claimed. No repository changes were pushed.
