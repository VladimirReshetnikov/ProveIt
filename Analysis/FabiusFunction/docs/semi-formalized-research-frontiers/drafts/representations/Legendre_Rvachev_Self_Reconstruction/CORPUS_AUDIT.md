# Corpus audit and novelty boundary

## Snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Branch: `main`
- Commit: `faa3a9b94ac0e71abdc53c36fdf428222e4d2a8c`
- Audited scope: `Analysis/FabiusFunction/docs/**/*.tex`
- Audit date: 2026-08-29

The subtree contains multiple historical versions, source copies inside
archives, generated consolidations, and several independent reports answering
closely related prompts.  Treating each byte-distinct copy as independent
mathematical evidence would distort the audit.  The workflow was therefore:

1. recursively inventory the TeX tree;
2. identify canonical or newest representatives of each mathematical strand;
3. close-read the task-bearing sources and compare their neighboring sibling
   reports;
4. search the current repository for formulas and terminology defining the
   additional results in this package.

## Principal task-bearing repository sources

- `Analysis/FabiusFunction/docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`
  supplies the normalization, Fourier product, moments, dyadic values, and the
  exact rational Fourier--Legendre expansion.

- `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Up_Polynomial_Synthesis/Up_Polynomial_Synthesis.tex`
  consolidates exact polynomial reproduction by shifted or dilated up-atoms,
  dyadic zero multiplicities, Bell--Bernoulli deconvolution, local nullspaces,
  and endpoint compression.

- `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/lagrange_rvachev_loop_report_v3/lagrange_rvachev_loop.tex`
  is the directly preceding Legendre-aware loop report.  It already contains
  deconvolved Legendre polynomials, Christoffel--Darboux synthesis, finite
  Legendre atomization, fixed-scale partial loops, factorial growth of
  `Q_{2n}(0)`, and a rigorous non-flattening theorem.

- The other four Lagrange--Rvachev loop siblings, including
  `Rvachev_Lagrange_Loop_Report_v5/`, were used as independent consistency
  checks for finite synthesis, right inverses, projectors, and conditioning.

- The Fourier-decay, inverse-Fabius, Lambert-W, q-analog, Thue--Morse,
  Bell/Bernoulli, and asymptotic reports supplied context and cross-checks.

## Imported baseline

The package does **not** claim as new:

- the sinc-product Fourier transform and its dyadic zero multiplicities;
- the probability/MGF model, rational moments, and exact dyadic values;
- exact polynomial synthesis by finite shifted up-functions;
- the Fourier--Legendre expansion and exact rational coefficients `u_n`;
- the basic Legendre-to-up block loop and fixed-scale partial-loop formulas;
- the reciprocal-MGF pole asymptotic of `Q_{2n}(0)`;
- the original theorem ruling out absolute or unconditional atomwise
  flattening;
- the general deconvolved Christoffel--Darboux projector loop.

## Additional results developed in this package

Subject to the corpus-relative qualification below, the report adds:

- exact orthogonality of the finite self-translate blocks and their atom-Gram
  identities;
- exact Pythagorean tails and the Sturm--Liouville/Sobolev energy hierarchy;
- a positive rational Legendre series and infinite-sinc integral for
  `A_2 = integral_0^1 F(x)^2 dx`;
- the nested dyadic-Fabius square series for `A_2`;
- general interlevel null trains, a refinement cocycle, and a quarter-grid
  lifting decomposition into a null gauge plus one orthogonal detail;
- endpoint-jet and central-binomial dyadic sum rules;
- trace and Hilbert--Schmidt identities for the even-projector translate
  factorization;
- the sharp central-coefficient law
  `limsup |c_n^(0)|^(1/n) / n^2 = 1/(pi^2 e^2)`.

## Targeted current-snapshot searches

GitHub code searches at the pinned snapshot/current branch found no matching
occurrence for the following defining phrases or values:

- `quarter-grid`
- `u_n^2`
- `orthogonal block`
- `positive rational energy`
- `interlevel polynomial null`
- `root-limsup`
- `Hilbert--Schmidt identities`
- `0.40443676798398526`

These searches supplement, but do not replace, mathematical comparison with
the canonical sources.  Absence from this repository is **not** a claim of
worldwide priority.  Every conjecture in the report is explicitly labeled.
