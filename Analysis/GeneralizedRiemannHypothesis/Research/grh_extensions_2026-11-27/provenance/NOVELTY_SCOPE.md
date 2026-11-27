# Novelty and primary-source comparison

Date of comparison: 27 November 2026.

## Precise claim

This package proves two extensions that were not stated in the supplied Article at ProveIt commit `3d8689ceae76501a5c50f67da37e85369aac4fb6`. It does not certify that no equivalent theorem exists elsewhere. The scope is supported by indexing all 21 section sources, examining the relevant results and open questions, and targeted searches of the mathematical literature.

### Unsmoothed prime counts

Existing article inputs:

- `zer:lem:bins`: local second-moment control by frequency bins.
- `zer:thm:coercive`: prime-probe coercivity of multiscale zero-multiplicity vectors.
- `zer:cor:multiscale`: strict covariance and occupation for absolutely convergent smoothed prime-error series.
- `zer:sec:open`, item 10: asks whether multiscale or jet covariance remains strictly positive for unsmoothed prime counts.

Extension: the ordinary pi counting functions, with their prime-square and central-zero corrections, satisfy arbitrary finite multiscale strict covariance and uniform directional occupation even after finite spectral deletion. The technical addition is local fourth-moment convergence and a controlled theta-to-pi integral remainder. The paper re-proves the prime-probe step and does not treat every unsmoothed jet derivative or all prime-race orderings.

Existing literature inspected:

- Kaczorowski and Ramaré, *Almost periodicity of some error terms in prime number theory*, Acta Arithmetica 106 (2003), 277–297, DOI 10.4064/aa106-3-6. Theorem 1(e) already provides Stepanov S^2 almost periodicity. This is explicitly credited as classical. Primary text: https://ramare-olivier.github.io/Maths/kaczo.pdf
- Banks, *Comparing zeros of distinct Dirichlet L-functions*, Publicationes Mathematicae Debrecen 106 (2025), 327–335. Theorem 1.2 in arXiv:2302.07073v2 supplies fixed-argument Landau sums with O(log T) error; this is an input, not a novelty claim. https://arxiv.org/pdf/2302.07073
- Akbary, Ng, and Shahabi, *Limiting distributions of the classical error terms of prime number theory*, arXiv:1306.1657. General limiting distributions and almost-periodic methods are established background. https://arxiv.org/abs/1306.1657
- Martin and Ng, *Inclusive prime number races*, arXiv:1710.00088v2. Their all-ordering and support conclusions are stronger in a different direction and use additional independence hypotheses. Our theorem makes no corresponding claim. https://arxiv.org/abs/1710.00088

### Symplectic projections

Existing article inputs:

- `spn:thm:complete-law`: exact arbitrary-frame symplectic compression law.
- `spn:thm:lagrangian`: closed square Lagrangian projection likelihood.
- `spn:thm:rank-blind`: asymptotically identical square rank laws with a persistent complete-matrix discrepancy.
- `spn:q:symplectic`: asks for growing-dimensional compression limits.

Extension: grow the excess of columns c in n by (n+c) blocks with a nondegenerate source form. The full-matrix total variation tends to one, with a sharp overlap coefficient valid through c=n, while rank total variation is asymptotic to q^(-n)/(q-1). The rank chi-square asymptotic q^(-2n+c)/(q-1) yields the sharp scale q^(2n-c) for independent rank observations. The exact finite likelihood is a specialization of the existing general law and is not advertised as a separate globally new counting theorem.

Existing literature inspected:

- Fulman and Goldstein, *Stein's method and the rank distribution of random matrices over finite fields*, Annals of Probability 43 (2015), 1274–1314. Standard rectangular uniform-matrix rank laws and their limiting approximations are background. https://arxiv.org/abs/1211.0504
- Ishizuka, *Uniform Sampling of Linear Codes with Prescribed Hull Dimension*, arXiv:2611.03578v2. The paper treats prescribed-form orbits and uniform sampling over all characteristics; these are background to our model, not evidence that our observation-testing asymptotics are novel. Primary text: https://arxiv.org/html/2611.03578v2

## Targeted search record

Searches included the following combinations, supplemented by the bibliography and exact result labels in the supplied article:

- random symplectic matrices rectangular blocks total variation Lagrangian rank distribution;
- symplectic random matrices finite fields blocks;
- Lagrangian total variation rank matrices;
- symplectic rank sample complexity;
- prime Stepanov almost periodic;
- prime multiscale covariance unsmoothed;
- Banks comparing zeros distinct Dirichlet L-functions Landau formula;
- the exact titles of the primary works above.

The inspected results did not exhibit the complete new formulations in this package. These searches are not a comprehensive priority review. No claim is made to have settled a named open conjecture beyond the explicitly identified extension questions in the supplied research article.

## Attribution and status

The input Article is attributed in its own main file to “ProveIt Contributors.” The vendored README attributes its underlying proof to Levent Alpöge with Claude and its text to Claude. This package takes the precisely stated Dirichlet GRH export as the arithmetic input and makes its static-audit limitation explicit. The symplectic result is unconditional and can be checked without any statement about zeros of L-functions.
