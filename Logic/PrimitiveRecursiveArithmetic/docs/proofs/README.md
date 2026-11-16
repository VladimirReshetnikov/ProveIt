# Delivered iPRA proof packets

This directory holds the research packets that were delivered as archives on 14 and
15 November 2026: 33 to `docs/drafts`, and 34 to
`Logic/PrimitiveRecursiveArithmetic/docs/incoming`. Each packet gives a human-readable proof of a classical theorem
of analysis, number theory or geometry. Each proof is in a finitary, quantitative form meant
for intuitionistic primitive recursive arithmetic (iPRA). Most packets also include
exact-arithmetic reference code and a Lean formalization plan or scaffold aimed at the iPRA
development in [`ConciseIPRA`](../../ConciseIPRA/README.md).

The packets are filed as delivered. Nothing in them was rerun, checked, compiled or edited
for this placement. The Lean files have not been built, and the summaries in the table below
only repeat what each packet says about itself. Several packets say that their Lean files are
uncompiled specifications or outlines, or that part of what was asked for is not proved.

## Layout

- The packets are grouped by mathematical area, one subdirectory per area (see
  [Packets](#packets)). Within its area, each archive has one directory, named after the
  archive without `.zip`. The grouping is by the main theorem of each packet; several
  packets touch more than one area.
- Almost every archive wraps its files in a single top directory. That directory is removed,
  so the archive member `<wrapper>/<path>` is the file `<area>/<directory>/<path>` here. The
  tables below give each wrapper, or `none` for an archive without one.
- Text files are stored under the repository's `.gitattributes`, which normalizes line
  endings to LF. Other bytes are as delivered.

## What is not placed

[`OMITTED.tsv`](OMITTED.tsv) lists every archive member that has no file here, with the
reason. Its directory column gives `<area>/<directory>`.

| Reason | Members | Where the bytes are |
|---|---:|---|
| `ignored` | 77 | The member matches the repository's `.gitignore`: 43 `SHA256SUMS` / `SHA256SUMS.txt` checksum manifests, 33 `.log` files from LaTeX and Lean builds, and 1 file under a `build/` directory. It is available only from the delivered archive, so it is lost for the archives that were not committed. |
| `sibling-packet` | 21 | `puiseux_ipra` bundles `dependencies/FTA_iPRA/`, a byte-identical copy of the packet filed in [`algebra/FTA_iPRA`](algebra/FTA_iPRA/) (13 members). `ipra_finite_demand` bundles four of its files under the same path (4 members). `ipra_resources_and_elimination_2026-11-15` bundles `lean/BackwardDemand.lean` of [`foundations/ipra_finite_demand`](foundations/ipra_finite_demand/) (1 member). `ipra_stable_observables` bundles three `lean/ConciseIPRA/` files byte-identical to the `lean/upstream/` copies in [`foundations/ipra_coherent_methods_2026-11-15`](foundations/ipra_coherent_methods_2026-11-15/) (3 members). The reference column gives the placed file, except for the copy of `SHA256SUMS`, which is ignored in both. |
| `sibling-archive` | 1 | `zeta_zeros_ipra_2026-11-15` bundles `dependencies/zeta_functional_equation_ipra.zip`, a byte-identical copy of the delivered archive filed in [`analytic-number-theory/zeta_functional_equation_ipra`](analytic-number-theory/zeta_functional_equation_ipra/). |
| `repository-copy` | 25 | `zeta_zeros_ipra_2026-11-15` bundles `sources/Deduction.lean`, `sources/NativeBiInterpretation.lean` and `sources/PR.lean`; `ipra_presentations_to_witnesses` and `four_metrics_ipra_2026-11-15` bundle those three and `Syntax.lean`, under `lean/upstream/` and `lean/upstream_inspected/`; all byte-identical to the files of the same names in [`ConciseIPRA/Lean/ConciseIPRA`](../../ConciseIPRA/Lean/ConciseIPRA/). `isoperimetric_ipra_constructive_2026-11-15` bundles, under `reused/`, the earlier packet [`geometry/isoperimetric_ipra`](geometry/isoperimetric_ipra/) as filed here at `22afac4c9d`; 14 of its files are byte-identical to that packet. The reference column gives that file, relative to the repository root. |

Other checksum manifests (`MANIFEST.sha256`, `manifest.sha256`, `MANIFEST.txt`) are not
matched by `.gitignore` and are placed. None of them was verified. The README,
`SOURCE_MANIFEST.md` and article of `puiseux_ipra` still refer to its `dependencies/`
directory. Its files are in [`algebra/FTA_iPRA`](algebra/FTA_iPRA/). Likewise, `sections/status.tex` and
`sources/source_manifest.json` of `zeta_zeros_ipra_2026-11-15` still name its omitted
`dependencies/` archive and `sources/` copies.

To recover an omitted member, restore the archive from the commit that added it
(the Arrival column). For `apery_ipra`, `faltings_ipra`, `gamma_ipra`,
`ipra_polynomial_formulas_abel_ruffini` and `mollweide_circle_ipra`, replace `docs/drafts` with
`Logic/PrimitiveRecursiveArithmetic/docs/incoming`:

```bash
git show <arrival>:docs/drafts/<archive>.zip > <scratch>/<archive>.zip
```

An archive whose Arrival is *not committed* was not committed, on Vladimir's instruction, and
was deleted after placement, so it cannot be restored from the history. Of those,
`isoperimetric_ipra_constructive_2026-11-15` omits only its `reused/` copies, which are the
files of `geometry/isoperimetric_ipra`. The others omit at most their ignored checksum
manifests, build logs and `build/` files.

## Packets

The 67 archives hold 1,793 members: 1,669 placed here, 77 ignored, 21 in bundled copies of
a sibling packet, 1 nested copy of a sibling archive and 25 copies of repository files.
In each area's table, P is the number of placed files and O the number of omitted members
of each packet. Arrival is the commit that added the archive to its drop directory, or *not committed*.

### Algebra

[`algebra/`](algebra/): Roots of polynomials, their expansions, and field-theoretic impossibility.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`FTA_iPRA`](algebra/FTA_iPRA/) | `ea3f6066cf` 2026-11-14 | `FTA_iPRA` | An arithmetized constructive fundamental theorem of algebra, with a Lean formalization blueprint and exact rational reference programs. | 12 | 1 |
| [`cayley_hamilton_ipra`](algebra/cayley_hamilton_ipra/) | *not committed* 2026-11-15 | `cayley_hamilton_ipra` | The Cayley–Hamilton theorem as the uniform primitive recursive identity for the generic n×n matrix, specialized to any commutative ring, with trace identities, minimal polynomials, integrality and quaternionic extensions. Its Lean files are uncompiled specifications and an outline. | 24 | 0 |
| [`ipra_polynomial_formulas_abel_ruffini`](algebra/ipra_polynomial_formulas_abel_ruffini/) | `6800f2d21a` 2026-11-15 | `ipra_polynomial_formulas_abel_ruffini` | Radical formulae for polynomials through degree four, and the Abel–Ruffini theorem for the generic quintic, with an iPRA arithmetization plan. Its Lean file is a blueprint whose `opaque` declarations are not yet defined. | 27 | 1 |
| [`ipra_stable_observables`](algebra/ipra_stable_observables/) | *not committed* 2026-11-15 | `ipra_stable_observables` | Stable observables from finite witnesses, applied to rational spectral theory uniform in dimension: Jacobi rotations with explicit fuel, stable ordered eigenvalue names through collisions, principal square roots and gap-dependent spectral projectors. It states that five Lean combinators return the `Prf PRAAx` type. Its `lean/lakefile.toml` needs `lean/ConciseIPRA/`, omitted here as copies from `ipra_coherent_methods_2026-11-15`. | 43 | 4 |
| [`lagrange_inversion_ipra`](algebra/lagrange_inversion_ipra/) | *not committed* 2026-11-15 | `lagrange_inversion_ipra` | Lagrange inversion coefficientwise in truncated power series: the Lagrange–Bürmann formulas, Bell-polynomial and Good's multivariate forms, Puiseux-type inversion, explicit inverse radii, Lambert W and Catalan expansions. Its Lean file is a blueprint, not a kernel-checked proof. | 18 | 0 |
| [`puiseux_ipra`](algebra/puiseux_ipra/) | `8c135f6f2a` 2026-11-15 | `puiseux_ipra` | Puiseux expansions for exactly presented algebraic coefficients, with explicit convergence radii and tail bounds. It bundles the FTA packet as a dependency. | 17 | 14 |
| [`three_impossibilities_ipra`](algebra/three_impossibilities_ipra/) | `a28886c88e` 2026-11-15 | `three_impossibilities_ipra` | The impossibility of doubling the cube, trisecting 60° and squaring the circle by straightedge and compass. It is stated as a proof architecture. | 12 | 1 |

### Real and complex analysis

[`analysis/`](analysis/): Calculus, special functions, series and contour integration.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`basel_ipra`](analysis/basel_ipra/) | `ea3f6066cf` 2026-11-14 | `basel_ipra` | The Basel identity, ∑ 1/j² = π²/6, as a universally quantified PRA inequality. Its Lean files are uncompiled specifications and an outline. | 17 | 1 |
| [`bohr_mollerup_ipra_2026-11-15`](analysis/bohr_mollerup_ipra_2026-11-15/) | `b2d7526ffc` 2026-11-15 | `bohr_mollerup_ipra` | A finitary constructive Bohr–Mollerup theorem, with a structured Lean scaffold and roadmap. | 13 | 0 |
| [`calculus_ipra`](analysis/calculus_ipra/) | `6ad3d9f371` 2026-11-14 | `calculus_ipra` | Effective versions of both parts of the fundamental theorem of calculus and the finite-order Euler–Maclaurin formula. | 12 | 1 |
| [`cauchy_residue_ipra`](analysis/cauchy_residue_ipra/) | `4ea4d4a14a` 2026-11-15 | `cauchy_residue_ipra` | Quantitative constructive versions of Cauchy's integral theorem and the residue theorem, stated as schemas. | 13 | 1 |
| [`gamma_ipra`](analysis/gamma_ipra/) | `7e8e6aad97` 2026-11-15 | `gamma_ipra` | The Gamma function built from finite Euler products, with explicit error bounds: the Euler integral, functional, reflection, multiplication and beta identities, Bohr–Mollerup, Stirling and Binet formulas. It says its Lean file compiles but leaves the analytic contracts uninstantiated. | 24 | 1 |
| [`stirling_ipra`](analysis/stirling_ipra/) | `38cafaa5be` 2026-11-14 | `stirling_ipra` | Stirling's formula, with finite rational estimates and an induction audit. | 10 | 1 |
| [`taylor_cauchy_ipra`](analysis/taylor_cauchy_ipra/) | `daade03000` 2026-11-15 | `taylor_cauchy_ipra` | Taylor's theorem with integral and Peano remainders, and Cauchy's integral formula. | 13 | 1 |
| [`trigonometric_identities_ipra_2026-11-15`](analysis/trigonometric_identities_ipra_2026-11-15/) | *not committed* 2026-11-15 | `trigonometric_identities_ipra_2026-11-15` | An atlas of trigonometric identities, with principal inverse-function identities, the derivatives of sine and cosine and the dyadic infinite cosine product. Its checker states 227 identities in 27 families verified exactly. Its Lean files are uncompiled, and two of them contain deliberate `axiom` declarations. | 16 | 1 |

### Analytic number theory

[`analytic-number-theory/`](analytic-number-theory/): Primes, prime sums and the Riemann zeta function.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`brun_ipra_2026-11-15`](analytic-number-theory/brun_ipra_2026-11-15/) | `fb79243454` 2026-11-15 | `brun_ipra` | Brun's theorem on twin-prime reciprocals, with a primitive-recursive Cauchy modulus. | 20 | 1 |
| [`goldbach_euler_ipra`](analytic-number-theory/goldbach_euler_ipra/) | `d72c8b2463` 2026-11-15 | `goldbach_euler_ipra` | The Goldbach–Euler theorem, ∑ 1/(p−1) = 1 over perfect powers p, with an explicit convergence modulus. Its Lean outline has explicit `sorry` obligations. | 13 | 1 |
| [`pnt_ipra_constructive_2026-11-14`](analytic-number-theory/pnt_ipra_constructive_2026-11-14/) | `ea3f6066cf` 2026-11-14 | `pnt_ipra` | An explicit arithmetic prime number theorem with quantifier-free induction, and the passage to the logarithmic statement. | 14 | 0 |
| [`pnt_li_ipra_2026-11-15`](analytic-number-theory/pnt_li_ipra_2026-11-15/) | `d72c8b2463` 2026-11-15 | `pnt_li_ipra` | Logarithmic-integral strengthenings of the prime number theorem: an explicit stretched-exponential bound on π(n) − Li₂(n), and the full asymptotic expansion with explicit remainders. | 23 | 0 |
| [`prime_distribution_ipra`](analytic-number-theory/prime_distribution_ipra/) | *not committed* 2026-11-15 | `ipra_prime_distribution_2026-11-15` | Prime distribution, which it calls a partial resolution: Dirichlet's theorem with an explicit bound and sharp Brun–Titchmarsh are proved, while Chebotarev, Siegel–Walfisz and Bombieri–Vinogradov get targets and reductions only. Its Lean files are an uncompiled outline. | 33 | 1 |
| [`prime_reciprocal_ipra_2026-11-15`](analytic-number-theory/prime_reciprocal_ipra_2026-11-15/) | `52eb7d907b` 2026-11-15 | `prime_reciprocal_ipra_2026-11-15` | Divergence of the reciprocal-prime sum in the explicit form ∑_{p ≤ 2^(2·4^k)} 1/p > k. | 11 | 0 |
| [`von_mangoldt_totient_ipra_2026-11-15`](analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15/) | *not committed* 2026-11-15 | `von_mangoldt_totient_ipra_2026-11-15` | Identities for the von Mangoldt function and Euler's totient, uniformly for a primitive recursive prime weight: divisor, Möbius, lcm, Chebyshev and Dirichlet-series identities, Menon's identity and Euler orders. Its Lean files are uncompiled scaffolds. Its README cites `build/BUILD_REPORT.md`, which is ignored here. | 16 | 1 |
| [`zeta_functional_equation_ipra`](analytic-number-theory/zeta_functional_equation_ipra/) | `db4b793b19` 2026-11-14 | `zeta_ipra` | Riemann's functional equation for ζ in quantitative form, with a formalization plan for its finite arithmetic content. | 31 | 0 |
| [`zeta_ipra_proof_package`](analytic-number-theory/zeta_ipra_proof_package/) | *not committed* 2026-11-15 | `zeta_ipra` | Constructive zeta theory in 33 result families: Dirichlet convergence, Euler products, the entire regular part and Stieltjes constants, special values, both functional equations and ξ, the Euler–Hasse series, and an explicit lower bound on the modulus of ζ(1+it). Its Lean files are uncompiled candidates. | 26 | 1 |
| [`zeta_zeros_ipra_2026-11-15`](analytic-number-theory/zeta_zeros_ipra_2026-11-15/) | `d72c8b2463` 2026-11-15 | `zeta_zeros_ipra` | Quantitative zero distribution of ζ: nonvanishing regions, trivial zeros, the Riemann–von Mangoldt estimate and local counts. It also certifies one critical-line zero near 1/2 + 14.1347i. | 25 | 5 |

### Combinatorics

[`combinatorics/`](combinatorics/): Combinatorial sequences, their identities, congruences and asymptotics.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`bell_numbers_ipra`](combinatorics/bell_numbers_ipra/) | *not committed* 2026-11-15 | `bell_ipra` | Bell numbers: finite identities, the Dobiński and Comtet formulas, generating functions, Hankel determinants, Touchard congruences, an all-n bound, and the de Bruijn and Moser–Wyman asymptotics with explicit remainders. It states that its finite Lean core compiles; the analytic results remain Lean targets. | 32 | 0 |

### Diophantine number theory

[`diophantine-number-theory/`](diophantine-number-theory/): Diophantine equations, Diophantine approximation, geometry of numbers and transcendence.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`apery_ipra`](diophantine-number-theory/apery_ipra/) | `12ab5b00c1` 2026-11-15 | `apery_ipra` | Apéry's theorem: ζ(3) is irrational, with an explicit primitive-recursive separation from every rational p/q. Its Lean files are uncompiled. | 15 | 1 |
| [`diophantine_geometry_ipra`](diophantine-number-theory/diophantine_geometry_ipra/) | `d72c8b2463` 2026-11-15 | `diophantine_geometry_ipra` | Selected rational Diophantine geometry: bounded-height enumeration, height inequalities for maps of P¹, rational preperiodic points, conic parametrization, and Fermat's square-area theorem by finite descent. It states that its Lean arithmetic core is compiled. | 38 | 1 |
| [`diophantine_ipra_2026-11-15`](diophantine-number-theory/diophantine_ipra_2026-11-15/) | `b5a3ad0377` 2026-11-15 | `diophantine_ipra` | Størmer's theorem, a constructive Davenport–Schmidt theorem, and Roth cutoffs for quadratic irrationals. It says the general effective Roth cutoff is not proved and its Lean files are not compiled. | 23 | 1 |
| [`dirichlet_kronecker_ipra`](diophantine-number-theory/dirichlet_kronecker_ipra/) | `db4b793b19` 2026-11-14 | `dirichlet_kronecker_ipra` | Logical obstructions to the unrestricted statements, with constructive scalar and simultaneous Dirichlet approximation and quantitative Kronecker theorems. | 23 | 1 |
| [`faltings_ipra`](diophantine-number-theory/faltings_ipra/) | `12ab5b00c1` 2026-11-15 | `faltings_ipra` | Faltings' theorem: it says it does not prove the general theorem in iPRA. It analyses the missing height bound and proves special cases, among them the rational points of the Fermat quartic. It states that its three Lean modules compile. | 20 | 8 |
| [`flt_ipra`](diophantine-number-theory/flt_ipra/) | *not committed* 2026-11-15 | `flt_ipra` | Fermat's Last Theorem for every exponent divisible by 3, 4, 5 or 7, by descents for the base exponents and uniform lifting. It says it does not prove FLT in general; the first exponent it leaves out is 11. Its Lean files are an uncompiled outline. | 26 | 1 |
| [`hurwitz_khinchin_ipra`](diophantine-number-theory/hurwitz_khinchin_ipra/) | `b5a3ad0377` 2026-11-15 | `hurwitz_khinchin_ipra` | Sharp constructive Hurwitz approximation and quantitative constructive Khinchin approximation. | 18 | 1 |
| [`minkowski_ipra`](diophantine-number-theory/minkowski_ipra/) | `057b790401` 2026-11-14 | `minkowski_ipra` | Minkowski's convex-body theorem. | 37 | 1 |
| [`mordell_weil_ipra`](diophantine-number-theory/mordell_weil_ipra/) | *not committed* 2026-11-15 | `mordell_weil_ipra` | Constructive Mordell–Weil descent: a general primitive-recursive finite-descent theorem, generators for an elliptic curve relative to a supplied covering list, and an unconditional computation of E(Q) for y² = x³ − u⁴x and products of these. It says it does not give a uniform generator algorithm for arbitrary elliptic curves. | 33 | 1 |
| [`pell_ipra_2026-11-15`](diophantine-number-theory/pell_ipra_2026-11-15/) | `b5a3ad0377` 2026-11-15 | `pell_ipra` | Pell equations for every nonsquare D ≥ 2, with an audit of their algorithms and induction invariants in iPRA. | 18 | 1 |
| [`siegel_ipra`](diophantine-number-theory/siegel_ipra/) | *not committed* 2026-11-15 | `siegel_ipra` | Siegel's theorem on integral points: it says it does not prove the general theorem in iPRA. It proves a complete constructive Runge case with explicit height bounds and enumeration, the integral points of y² = x²ᵐ + x + 1 and of y² = x⁴ + ax² + b, and the logical link between a uniform iPRA proof and a height bound. It states that its native Lean results compile. | 32 | 1 |
| [`transcendence_ipra`](diophantine-number-theory/transcendence_ipra/) | `c5093c20b5` 2026-11-14 | `transcendence_ipra` | Transcendence of e and π as explicit apartness bounds for nonzero integer polynomials. | 18 | 1 |

### Foundations

[`foundations/`](foundations/): Methods shared across areas: search, certificates and quantitative names in iPRA.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`ipra_coherent_methods_2026-11-15`](foundations/ipra_coherent_methods_2026-11-15/) | *not committed* 2026-11-15 | `ipra_coherent_methods` | Coherent finite methods: coherent finite presentations with restriction maps, filtered lifting with a frozen inverse, ranked descent and weighted norms, with applications to Hurwitz-type targets. It credits the earlier frameworks here. Its `lean/upstream/` holds `Deduction.lean`, `PR.lean` and `Syntax.lean` as in ConciseIPRA at `052fbaebfc`, each with one extra blank line at the end, so they are placed. | 55 | 0 |
| [`ipra_embedding_framework`](foundations/ipra_embedding_framework/) | *not committed* 2026-11-15 | `ipra_embedding_framework` | Mathematics in iPRA through finite observations: bounded-formula compilation, simple analytic branches with Cauchy coefficients, simultaneous finite-window stability, a hyperelliptic zero count for the Siegel strategy, and finite algebra certificates. It calls itself a targeted audit of the collection, not a verification of the packets. | 28 | 1 |
| [`ipra_embedding_framework_2026-11-15`](foundations/ipra_embedding_framework_2026-11-15/) | *not committed* 2026-11-15 | `ipra_embedding_framework_2026-11-15` | Certified Finitary Presentations, a different packet from `ipra_embedding_framework`: fixed codes and evaluator schemas, finite observations with precision transformers, guarded operations, bounded traces and finite nets, ending in a `PRAAx` derivation. It also proves barriers, such as that no total universal PR evaluator exists. Its Lean files are a semantic core and a blueprint. | 45 | 0 |
| [`ipra_evidence_framework`](foundations/ipra_evidence_framework/) | *not committed* 2026-11-15 | none | Evidence-indexed finite mathematics: a finite relational-output and compatibility interface for cases where only approximate witness families are justified, with a backward finite dynamic program for witness amalgamation. It credits the earlier frameworks here. Its Lean blueprint is not compiled. | 6 | 0 |
| [`ipra_finite_demand`](foundations/ipra_finite_demand/) | *not committed* 2026-11-15 | `ipra_finite_demand` | Finite demands, root supports and norm certificates: backward demands with changing parameters, aggregate witnesses, root supports through collisions for monic polynomials, and norm zero-counts for y^m = f(x). It states that its five Lean modules compile with Std only. Its bundled FTA files are omitted as copies of `algebra/FTA_iPRA`. | 36 | 4 |
| [`ipra_finite_observation`](foundations/ipra_finite_observation/) | *not committed* 2026-11-15 | `ipra_finite_observation` | Finite observations and uniform constructions: a finite observation compiler, degree-uniform complete polynomial factorization, a derived continuity modulus for the Bohr–Mollerup candidate, and finite-net infimum names and coherent minimizers. It states that its finite-table Lean proofs are checked and its further targets type-check. | 35 | 1 |
| [`ipra_finite_use_framework_2026-11-15`](foundations/ipra_finite_use_framework_2026-11-15/) | *not committed* 2026-11-15 | `ipra_finite_use_framework` | Demand-driven relational certificates: a finite-use relational composition theorem, in which a producer returns a finite relation of valid answers and a bounded consumer is compiled with it by backward viability, with exact or diameter-stable erasure of internal choices. Its Lean files are uncompiled blueprints. | 37 | 0 |
| [`ipra_framework`](foundations/ipra_framework/) | *not committed* 2026-11-15 | `ipra_framework` | Finite contracts for mathematics in iPRA, a different packet from `ipra_framework_2026-11-15`: bounded-formula Booleanization and guarded induction, then stable finite windows, coherent approximate witnesses, local analytic branches, and integral power-gap certificates for y^m = f(x). It says it gives no final convergence moduli. | 64 | 1 |
| [`ipra_framework_2026-11-15`](foundations/ipra_framework_2026-11-15/) | *not committed* 2026-11-15 | `ipra_framework` | A cross-domain certificate-and-modulus framework for the packets here: bounded primitive recursive search and descent, certificate composition, arithmetic of quantitative real names and apartness-conditioned inverses. It says it is not a verified solution of the other packets. Its Lean files have not been typechecked. | 6 | 0 |
| [`ipra_local_global`](foundations/ipra_local_global/) | *not committed* 2026-11-15 | `ipra_local_global` | Local-to-global constructions: a `Prf PRAAx` rule for variable-length PR recursion, classical-to-intuitionistic transfer, uniform local solutions of rational polynomial ODEs, and integral points on split polynomial branches. It states that its Lean modules compile and that two of them construct embedded `Prf PRAAx` derivations. | 37 | 1 |
| [`ipra_presentations_to_witnesses`](foundations/ipra_presentations_to_witnesses/) | *not committed* 2026-11-15 | `ipra_presentations_to_witnesses` | From finite presentations to explicit witnesses: proof-preserving finite simulation, complete rational enumeration from finite action data, certificate constructors, and complete section lists from nonzero norms. It says it proves no general Siegel, Faltings or Mordell–Weil result. Its `lean/upstream/` copies are omitted; they are the ConciseIPRA sources. | 54 | 5 |
| [`ipra_resources_and_elimination_2026-11-15`](foundations/ipra_resources_and_elimination_2026-11-15/) | *not committed* 2026-11-15 | `ipra_resources_and_elimination_2026-11-15` | Finite mathematical interfaces: changing-parameter recursion compiled to PR syntax, primitive recursive fuel for lexicographic descent, complete affine plane-intersection lists, and finite auxiliary envelopes. It states that four Lean declarations conclude `Prf PRAAx` derivability. Its `lean/build.sh` needs `BackwardDemand.lean`, omitted here as a copy from `ipra_finite_demand`. | 48 | 12 |
| [`ipra_uniform_certificates`](foundations/ipra_uniform_certificates/) | *not committed* 2026-11-15 | `ipra_uniform_certificates` | Uniform certificates complementing the finite-contract frameworks here: finite-net lifting with an explicit modulus and rational error budgets, uniform root names from sign brackets and algebraic separation, and composition of precision contracts. Its Lean blueprint is not compiled. | 6 | 0 |

### Geometry

[`geometry/`](geometry/): Euclidean and projective incidence theorems, triangle and solid geometry, rotations, the isoperimetric inequality, and Zariski descent on schemes.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`desargues_pascal_ipra`](geometry/desargues_pascal_ipra/) | `4ea4d4a14a` 2026-11-15 | `desargues_pascal_ipra` | Desargues' and Pascal's theorems, with a formalization roadmap and a repository-source audit. | 28 | 0 |
| [`eight_geometry_theorems_ipra`](geometry/eight_geometry_theorems_ipra/) | `390098877e` 2026-11-15 | `eight_geometry_theorems_ipra` | Constructive coordinate proofs of eight theorems: Pappus's harmonic theorem, Ceva, Menelaus, Carnot's conic and polygon theorems, Hoehn, Pappus's hexagon theorem and Brianchon. | 31 | 0 |
| [`euler_rodrigues_ipra`](geometry/euler_rodrigues_ipra/) | `db4b793b19` 2026-11-14 | `euler_rodrigues_ipra` | Euler's rotation theorem and Rodrigues' formula. It says the unrestricted exact-axis form is not constructively provable (LLPO reduction) and proves constructive replacements. | 21 | 2 |
| [`four_metrics_ipra_2026-11-15`](geometry/four_metrics_ipra_2026-11-15/) | *not committed* 2026-11-15 | `four_metrics_ipra` | Exact local forms of the Schwarzschild, Reissner–Nordström, Kerr and Kerr–Newman metrics: under valid rational coding, the inverse, determinant, Einstein–Maxwell, source-free Maxwell and Bianchi identities hold. Its Lean files define the arithmetic and name the `Prf PRAAx` target as an obligation. | 35 | 13 |
| [`ipra_algebraic_geometry_framework_2026-11-15`](geometry/ipra_algebraic_geometry_framework_2026-11-15/) | *not committed* 2026-11-15 | `ipra_algebraic_geometry_framework_2026-11-15` | Certified Zariski descent: certified setoids with quotient equality by ideal-combination witnesses, localization equality by killing exponents (valid with zero divisors), a primitive recursive power-cover constructor, finite principal-open gluing of modules, finite affine atlases and Čech complexes, and the Čech computation of O(d) on P^1 and on P^n. Its Lean files are uncompiled blueprints, and it claims none of its main theorems as a constructed `Prf PRAAx` value. | 46 | 0 |
| [`isoperimetric_ipra`](geometry/isoperimetric_ipra/) | `0bf379a842` 2026-11-14 | `isoperimetric_ipra` | The sharp planar isoperimetric inequality L² ≥ 4πA, with its equality characterization, for effective presentations. | 16 | 0 |
| [`isoperimetric_ipra_constructive_2026-11-15`](geometry/isoperimetric_ipra_constructive_2026-11-15/) | *not committed* 2026-11-15 | `isoperimetric_ipra` | Constructive isoperimetry, broadening [`isoperimetric_ipra`](geometry/isoperimetric_ipra/) (which it carries under `reused/` and as an appendix): planar and Dido problems, triangle inequalities, a rational Brunn–Minkowski theorem for box unions, the sharp n-dimensional inequality from outer-volume data, finite Sobolev/BV, spherical caps, and the hypercube edge and Harper vertex theorems. Its Lean files are uncompiled outlines. | 30 | 14 |
| [`mollweide_circle_ipra`](geometry/mollweide_circle_ipra/) | `349481d51f` 2026-11-15 | `mollweide_circle_ipra` | Mollweide's formulas, the laws of tangents and cotangents with the inradius formula, and the power-of-a-point, tangent-secant, intersecting-chords and intersecting-secants theorems. Its Lean files are not compiled. | 25 | 1 |
| [`morley_ipra_constructive`](geometry/morley_ipra_constructive/) | `58087eb241` 2026-11-15 | `morley_ipra_constructive` | Morley's trisector theorem, stated over finite exact certificates. | 13 | 1 |
| [`pappus_centroid_ipra_2026-11-15`](geometry/pappus_centroid_ipra_2026-11-15/) | `7b3c755844` 2026-11-15 | `pappus_centroid_ipra` | Pappus's surface and volume centroid theorems, with τ = 2π presented by nested regular polygons. | 16 | 1 |
| [`platonic_solids_ipra`](geometry/platonic_solids_ipra/) | `58087eb241` 2026-11-15 | `platonic_solids_ipra` | Exactly five similarity classes of Platonic solids, for constructible-coordinate codes. | 25 | 2 |
| [`spherical_trigonometry_ipra_2026-11-15`](geometry/spherical_trigonometry_ipra_2026-11-15/) | *not committed* 2026-11-15 | `spherical_trigonometry_ipra_2026-11-15` | Spherical trigonometry: the cosine, sine and tangent laws, polar duality, half-angle and Delambre–Napier formulas, right-triangle rules, Girard's theorem and L'Huilier's formula, triangle-solving procedures, and the tetrahedral face-area cosine law. Its checker states 68 identities in 14 families verified exactly. | 37 | 2 |
| [`triangle_formulas_ipra`](geometry/triangle_formulas_ipra/) | `c1bda76f7f` 2026-11-14 | `triangle_ipra` | Heron's formula and the laws of sines and cosines, in explicit finite arithmetic versions. | 21 | 3 |

### Probability

[`probability/`](probability/): Limit theorems for sums of random variables.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`central_limit_ipra_2026-11-15`](probability/central_limit_ipra_2026-11-15/) | *not committed* 2026-11-15 | `central_limit_ipra_2026-11-15` | Central limit theorems with explicit Berry–Esseen-type bounds for finite rational laws, and effective iid, Lindeberg, Lyapunov, de Moivre–Laplace, local, multivariate and martingale versions. Its Lean files are uncompiled blueprints. | 17 | 1 |

### Topology

[`topology/`](topology/): Combinatorial and quantitative topology of the plane and of cubes.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`dimension_invariance_ipra`](topology/dimension_invariance_ipra/) | `f616f72b66` 2026-11-15 | `dimension_invariance_ipra` | Quantitative dimension invariance for finite rational tables, via cubical Sperner parity on staggered grids. | 13 | 1 |
| [`jordan_ipra_constructive_2026-11-15`](topology/jordan_ipra_constructive_2026-11-15/) | `4ea4d4a14a` 2026-11-15 | `jordan_ipra` | A quantitative Jordan curve theorem for primitive-recursively presented circle embeddings. | 22 | 1 |
