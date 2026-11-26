# Audit of the 31 incoming GRH reports

## Provenance and scope

The snapshot is `VladimirReshetnikov/ProveIt` commit `274841c1cb137aafbb60ab5f519c51fd42eee98e`. Its `docs/incoming` contains 31 ZIP archives and the intake README. The README does not catalog these GRH arrivals. All 31 ZIPs were safely extracted to `working/prior_reports/`, allowing only text/source extensions and rejecting absolute/traversal member paths. There are 890 extracted files. `extraction_manifest.json` records archive SHA-256, sizes, and extracted members. `prior_work_matrix.json` and `.csv` record each manuscript's claimed established results, outstanding bridge, and member pointers.

This was a manuscript audit: introductions, abstracts, and the relevant theorem/proof sections were read. It is not a fresh verification of every proof, external theorem, large finite enumeration, or claimed classification. In particular, statements such as the exponent-six census and CM five-term classification should be attributed to their reports unless their proof/certificate is independently replayed.

## What is already exhausted

1. **General nonabelian analytic criteria.** There are explicit S3, S4, A5, A6, Sn, reflection-group, Sylow, cyclic-generator, PSL2 and Kummer criteria, tower/compositum compression, optimized character support and coefficients, sparse scales, positive-part and moving-average variants. A new group character calculation alone would be incremental. Every report leaves the same principal gap: a global arithmetic covolume/divisibility estimate for its actual nonabelian/Frobenius weights.
2. **Unrestricted torsion selection.** The papers already contain: series/Fitting extensions, arbitrary families under total budget, sharp nonvanishing depths, polynomial fixed-cardinality positive-tolerance bounds, exact aggregate zero-loss, exact minimax shell blocking cost, sharp exponential inverse-tolerance phase transition, and cyclotomic coefficient-field exact costs. A generic claim of a new exact torsion selector risks repeating existing work.
3. **Selmer limitations.** The papers already prove compulsory ramification cost, failure of normalized-length rounding, lack of fixed-module comparison under varying twist, conjugate self-duality obstruction invariant under anticyclotomic twists, symmetric mirror-image refinement, and scalar-inertia obstruction for rank-two symmetric powers. Finite-length/corank-zero consequences are already implicit or explicit.
4. **CM sparsity.** The latest manuscript closes all five-term cases: `s(Delta)<=5 iff h(Delta)<=4`, independently of RH. The earlier five residual discriminants and width-65536 limits are superseded. A later manuscript improves the Gaussian prime-conductor full-support lower relative density from 61.33% to 99.9818260107372245%.
5. **External-consequence applications.** Exponent-six census, CM coefficient fields, heavenly varieties/isogeny bounds, Euler products, prime-generating constants, prime-cube additive thresholds and geometric intervals are already explored. Most primarily use the exported Dirichlet GRH plus external arithmetic, and thus are less well aligned with the user's request for reuse of the internal method.

## Best identified unfilled torsion gap

Read `working/prior_reports/grh-torsion-and-prime-sampling/sections/field.tex`, with its inputs `ramification_intro.tex` and `cyclotomic.tex`.

Let K/Q_p be finite of ramification index e. Let F_i in O_K[T_1,...,T_s] be nonzero and

`A_i = min_a (v(coeff_a F_i) + rho |a|)`, with `sum_i A_i <= B`.

Choose h0 so `1/phi(p^h0) <= rho`. The report proves the existence of one tuple `(zeta_j-1)` satisfying **every separate exact bound**

`v(F_i(zeta_1-1,...,zeta_s-1)) <= A_i`.

It obtains exponents `h_j <= M_j` where

`M_1 = h0 + floor(e B)` and `M_{j+1} = h0 + floor(e phi(p^{M_j}) B)`.

The last paragraph explicitly asks whether this iterated growth is necessary or whether the common Galois action on coordinates allows a smaller bound. It also explicitly asks for the exact optimum at fixed packet cardinality and over general noncyclotomic finite coefficient fields.

**Essential distinction:** `grh_exact_torsion_transfer.../sections/exact_torsion.tex` already gives a dimension-independent order cutoff for **aggregate** exact valuation, by multiplying the polynomials. Its counterexample only rules out cardinality-free exact individual bounds with unrestricted growing coefficient fields; it does not settle fixed-field multivariate or fixed-cardinality questions.

## Exact one-variable baseline that must not be rediscovered

For unrestricted integral algebraic coefficients, rho=1, e_h=phi(p^h), set

`U_h(m) = (1/e_h) sum_{j=1}^{h-1} e_j floor(m/e_j)` for m<e_h, infinity otherwise.

Let m_h be the least integer with `U_h(m_h)>epsilon`. Then the exact minimum total witness budget needed to block every torsion shell through H with total positive excess greater than epsilon is

`C_p(epsilon,H) = sum_{h=1}^H m_h/e_h`.

This is in `grh-torsion-and-zero-data/grh-torsion-and-zero-data/minimax.tex`. Its `phase.tex` proves the threshold `B*=p/(p-1)` and

`lim_{epsilon -> 0} epsilon log N_p(B,epsilon) = B-B*` for B>B*.

For K_s=Q_p(zeta_{p^s}), the exact shell costs above level s are the level-s costs: see `grh-torsion-and-prime-sampling/sections/cyclotomic.tex`. The exact cost for shells h0..H is the sum of `a_min(h,s)(delta)`.

## Selmer corank finding

No literal "corank" or "co-rank" occurs in the manuscript TEX corpus. Nevertheless the mathematical content is already present:

- `grh_beyond_dirichlet_grh_2026-11-25/grh_beyond_transfer/sections/odd_sha.tex` proves that a direct limit of the exact odd-cocycle modules is a specified natural-conjugation eigenspace of the locally trivial H1 with divisible coefficients. Its uniform-bound corollary explicitly says the group is finite, killed by X, and zero when ell does not divide X. A further corollary proves integral odd cocycles vanish.
- `grh_method_transfers_2026-11-25/grh_method_transfers_2026-11-25/report/ramification_budget.tex` explicitly extracts infinitely many distinct twisting characters with bounded support cardinality and simultaneous finite Selmer-length bounds.

Thus stating finite normalized length implies corank zero is a useful clarification, but not a substantive new theorem relative to the supplied corpus. The comparison in odd_sha is only for its stated positive Tate exponent and odd coefficient prime; it is not a general BSD Selmer comparison.

## Further worthwhile directions if the torsion gap resists

- Formalize the symmetric mirror-image injection and demonstrate one actual arithmetic representation with the opposite sign and all remaining hypotheses; structural_transfers only specifies the candidate refactor.
- Build the first actual determinant object retaining the conductor-23 ideal-class/Frobenius information. Analytic optimizations will not substitute for this missing construction.
- Complete an exact strict-Selmer-to-Hecke comparison at one candidate K-theory degree before treating finite Hecke computations as K-group vanishing.
- Prove a new local CM determinant criterion that survives tied coefficient valuations, especially the first missed Gaussian prime conductor 42337. This directly addresses an explicit remaining question, but is a downstream arithmetic project rather than reuse of the central theta-lift mechanism.
