# Prior-report synthesis and new graph extremum

## Scope of comparison

Reference repository: `VladimirReshetnikov/ProveIt` at `d80526e4212e80f52046395005562b12d900dc37`.
Root verified all 52 incoming ZIPs against GitHub blob identities and extracted them into `research/prior_extracted`. This note inspects relevant report statements and arguments; it does not certify every theorem in every archive. Exact archive identities are in `research/incoming_manifest.json`.

## Existing results that must not be repackaged as new

| Family | Actual current frontier in inspected reports | Status in this review |
|---|---|---|
| Nonabelian zero detectors | S3 discriminants −23 and229, S4, A5/A6, PSL2, cyclic-generator, Sylow and relative-race detectors; one-sided prime-sum criteria, no arithmetic square-root bound | Scope inspected, no additional nonabelian RH proved |
| Higher K/Selmer | Concrete finite matrix/Hecke certificates, sharp torsion selection, sign-sensitive self-duality obstructions and trace-depth formulas | Global arithmetic comparison and uniform estimates remain missing |
| Exponent-six census | Exactly432 imaginary quadratic fields and1236 orders, relying on published enumeration plus new exclusion | Inherited report claim, not replayed here |
| Exponent-seven census | `exponent_seven_and_grh_transfers.zip` now claims complete33-field/40-order census;31 groups C7, remaining two C7² at −63499,−118843 | Current text inspected; memory describing it as still-open is stale |
| CM sparse equations | Four/five-term classifications; maximal-support families; >99.9818260107372245% certified lower relative density for Gaussian prime conductors | Inherited; general six-term and density-one assertions remain open |
| Natural vs upper density | McNew Q7.1/Q7.3: supplied gaps >0.002836 and >0.069218 | Inherited; separately revalidated in other recent reports |
| Rational vs integer-ratio density | Newest `mcnew_density_and_grh_transfers.zip` claims β−α>0.0001306, resolving McNew Q7.4 | Inherited newest claim; root handling proof review |
| Signed square cycles | Exact n=8m optimum; all even8≤n≤30; latest advances also n=34,36,38,42,44,46,50 | Do not redo n50 as new |
| Graph-tower valuations | Five DuBose–Vallières examples, nine Kataoka Table7 rows; finite moment formula p>2m | Moment formula and open question read in full |
| Finite coefficient rings | Positive limiting density for growing products of fields iff Σq_i^-2<∞; square-zero local-ring contrasts | Inherited; exact finite-product extrema and general local-ring families still open |
| Local torsion/interpolation | Sharp shell bounds, fixed coefficient fields, Lubin–Tate branch precisions, first-depth criterion and unbounded excess depth | Generic torsion-selection result would repeat prior work |

## Corrections retained

1. The source exports Dirichlet GRH. “GRH” must not be silently expanded to all Artin, Hecke or automorphic L-functions.
2. Earlier finite-precision objection to the entire Selmer route was too broad. `grh_ideal_densities_and_transfer_conditions_2026-11-26` explicitly corrects it: the readable source already has a bound for the full divisible Selmer module under its own hypotheses. Remaining issues are arithmetic identification, local conditions, odd-cocycle sizes, determinant nonvanishing, special-value denominators and uniformity.
3. Neither a Frobenius detector nor a correct Mellin/Landau criterion proves the required arithmetic estimate. No new nonabelian RH follows from the detector alone.
4. Nilpotent coefficient-ring behavior can differ sharply from products of fields of the same cardinality; degree arguments cannot be transferred without checking multiplication by zero divisors.
5. Known finite graph searches and prior incoming completion claims should be attributed rather than advertised as discoveries of this session.

## A completed new deduction relative to the incoming corpus

`moment_extremum.tex` proves a sharp global maximum for the coefficient A in the rank-two moment formula. For m nonzero steps spanning F_p², p>2m, and k=floor(m/2):

A ≤2k(p+1+2m−2k).

For even m and p≡1 mod2m this is attained and becomes

max A=m(p+1+m).

For m≥4 the maximizer has identically zero quadratic moment, resolving an explicitly open case in `grh_method_transfers_graph_towers_and_finite_rings/.../endmatter.tex`, lines9–13. Its consequence for every graph layer is

max v_p(κ_n)=m(p+1+m)(p^n−1)/(p−1)−2n.

The new ingredient is a first-nonzero-moment lemma: the first nonzero binary even-moment polynomial occurs by index floor(m/2). The proof groups parallel step forms and applies two Vandermonde arguments. Together with the projective root count it yields the upper bound. Two scalar root-of-unity orbits on independent coordinate axes attain it.

This is an extremal theorem about graph Iwasawa valuations, not a claim to resolve a longstanding named number-theory conjecture. It is independent of RH. Historical priority has not been established. The theorem was independently reviewed by `source_audit`, which found no mathematical errors.

## Computational evidence

`verify_moment_extremum.py` uses only the Python standard library. It passes:

- all240 spanning multisets at(m,p)=(2,5), maximumA16;
- all19152 spanning multisets at(m,p)=(3,7), maximumA24;
-2200 deterministic random spanning lists for m2 through12;
- ten equality constructions for even m2 through14;
- independent exact cyclotomic norm determinants for(m,p)=(2,5),(4,17),(6,13),(8,17);
- actual Laplacian cofactors for25 and169 vertices, with valuations14 and118 respectively.

The169-vertex case uses m6,p13 and steps(1,0),(4,0),(3,0),(0,1),(0,4),(0,3). The exact spanning-tree count has177 decimal digits; its13-adic valuation is118. The all-level formula is10(13^n−1)−2n, giving118,1676,21954 at levels1,2,3. These computational tests support the proof; the infinite theorem follows from the written argument.

## Primary literature for context

- Sage DuBose and Daniel Vallières, *On Z_l^d-towers of graphs*, Algebraic Combinatorics6(2023),1331–1346. https://alco.centre-mersenne.org/articles/10.5802/alco.304/ ; https://arxiv.org/abs/2207.01711 . General eventual polynomial theorem, not this extremum.
- Cédric Dion, Antonio Lei, Anwesh Ray and Daniel Vallières, *On the distribution of Iwasawa invariants associated to multigraphs*, Nagoya Math.J.253(2024),48–90. https://www.cambridge.org/core/journals/nagoya-mathematical-journal/article/on-the-distribution-of-iwasawa-invariants-associated-to-multigraphs/E908B7CA865EC0BD7F397FE6E18E5EFC ; https://arxiv.org/abs/2207.07213 . Discusses finite-field quadratic forms, moment coefficient methods, and distributions; no historical novelty inference from limited review.

Root should reopen any primary web source it cites in final response. Search-service IDs in this agent: `turn845454104search0` and `turn845454104search1`.
