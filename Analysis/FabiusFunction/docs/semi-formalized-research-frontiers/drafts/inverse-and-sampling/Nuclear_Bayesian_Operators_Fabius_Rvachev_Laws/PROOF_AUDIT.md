# Proof and provenance audit

## Scope of this document

This is a dependency audit, not an independent referee report or a formal verification certificate. It distinguishes the analytic arguments in the article from the finite checks in `verify.py`.

## Main analytic dependencies

| Result | Main dependencies | Important boundary condition |
|---|---|---|
| Smoothness, positivity, prefix-weight comparison | Finite convolutions of uniforms; elementary simplex density | All q in (0,1); m fixed and positive |
| Weighted derivatives of the likelihood kernel | Triple-uniform Fisher bounds; convolution Cauchy–Schwarz | The division by f is canceled using f=b*p; it is not ignored |
| All Schatten classes and logarithmic-square singular bound | Weighted derivative estimates; Jacobi derivative identities; rank approximation | q,m fixed; coefficient 1/(6 log(1/q)) is an upper-bound coefficient, not asserted optimal |
| Fourier kernel modes | Characteristic function product; differentiation in frequency | Listed modes span only a proved subspace; kernel completeness remains open here |
| Dense range and simple constant mode | Adjoint convolution; compactly supported Fourier uniqueness; overlap of positive conditional supports | Left singular family complete; right family requires the kernel complement |
| Factorial polynomial instability | Taylor approximation to one exact exponential null mode | Polynomial restriction norms use the probability weights, not coefficient Euclidean norms |
| Gaussian rigidity | Characteristic-function scaling; finite-variance expansion at zero; ODE continuation | No exponential moments or nonvanishing characteristic function away from zero assumed |
| All finite Rényi orders | Arbitrary root-Lipschitz density estimates and prefix small-ball lower bound | Finite m; constants may depend on alpha,q,m |
| Critical order two | Uniform convergence b_m to f; conditional posterior formula; dominated convergence/Fatou | Finiteness at each depth is distinct from finiteness of a depth limit |
| Prefix correction obstruction | Conditional orthogonality; strictly non-Gaussian Gaussian-noise test channel | Extra randomness must be independent of X conditional on S |

## Finite exact checks executed

The script uses `fractions.Fraction` for the core arithmetic and SymPy for Bernoulli numbers and symbolic identities. It checked:

- Appell intertwining through degree 8 for (q,m)=(1/3,1),(1/2,2),(2/3,3).
- Jordan ranks through degree 8 at a dyadic parameter.
- The degree-2 determinant ratio symbolically as a rational function of q and t=r^2.
- Jacobi derivative-norm multipliers in 45 parameter/degree/order combinations.
- Exact triangularity, parity, diagonal inner products, determinant ratio, and cubic mixing for 5 parameter pairs through degree 18.

Finite matrix eigenvalues were then computed at 100 decimal digits. These values were checked for expected positivity and the constant singular value, but were not enclosed using interval arithmetic. The exact trace fractions are retained; their printed logarithms are rounded numerical values.

These calculations test formulas and implementation. They do not prove compactness, the all-order singular-value bound, or the Rényi asymptotics. Those claims depend on the article's proofs.

## Source question provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected recursive-tree snapshot:

    8490a6e1c259a3b0c7ce32170816740b8ad7b40d

Editorial amendment (ProveIt, 2026-09-29): this string identifies a commit,
not a tree object. The Library source described below is byte-identical to
the report as first archived in the repository (30 August 2026); the three
problems it continues changed since only by renamings of notation macros.

Navigation path:

    Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/
    drafts/inverse-and-sampling/README.md

Relevant report package:

    fabius_information_frontier/

Question labels read from the user's Library source:

    prob:Bayesian-spectrum
    prob:TM-Renyi
    prob:exact-RD

The Library source is dated 30 August 2026, has 77,282 bytes, and has SHA-256:

    b756c86255c24f421029ded2f60f574f0677fbad4bb0fa62416950a742ebda45

Current repository metadata described a source of 78,310 bytes. No claim of byte-identical correspondence is made. The definitions and question labels are reproduced in the article so its claims can be evaluated independently of later editorial changes.

The navigation also identified newer entropy-Edgeworth and uniform-factor-recovery reports. This article does not re-present the already developed entropy expansion or those factor-recovery exponents. It does not claim to settle the separate global entropy-monotonicity conjecture.

## Remaining limitations

The strongest claims are the exact theorems as stated, not global novelty, optimal constants, a closed-form entire spectrum, or full rate-distortion asymptotics. The spectral bound concerns positive singular values; growing polynomial matrices may also approximate exact null directions. Ordinary Appell or Legendre coefficient diagonals are not substituted for the weighted singular values.
