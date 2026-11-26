# ProveIt incoming GRH report review

## Scope and pin

Repository: `VladimirReshetnikov/ProveIt`.
Commit inspected: `28ad287a8d13c0f864ebb51c7c053ad06aa6e585`.
Commit timestamp returned by GitHub: `2026-11-26T05:39:50Z`.
Directory: `docs/incoming/`.

The directory contains 32 GRH-themed ZIP archives and its pre-existing intake README. The README is not a current index of the GRH archive contents. `inventory.json` preserves the authoritative GitHub directory metadata, including exact blob SHA and byte size of every archive.

The latest commit adds `grh_transfer_synthesis_2026-11-25.zip` (Git blob `266406881cea5e9ab39e9e4fb41214b537fcab21`, 1,188,050 bytes). This latest synthesis was read directly. It summarizes 26 predecessors, leaving five other current reports outside its corpus. Those five were all downloaded and their principal mathematical sections read directly:

- `grh-torsion-and-prime-sampling.zip`
- `grh-torsion-and-zero-data.zip`
- `grh_exact_torsion_transfer_2026-11-25.zip`
- `grh_structural_transfers_2026-11-25.zip`
- `grh_transfers_singular_moduli_and_symmetric_powers.zip`

Three additional important predecessors were downloaded directly: `grh-exponent-six-and-transfers.zip`, `grh_sparse_singular_moduli.zip`, and `grh_quantitative_twists_2026-11-25.zip`. These notes distinguish mathematical statements written in earlier reports from independently verified results. No full upstream Lean rebuild or exhaustive arithmetic census was run by this review.

## Most useful earlier synthesis

Local path: `synthesis/grh_transfer_synthesis/`.

The files `sections/assessment.tex`, `sections/prior_matrix.tex`, and `sections/program.tex` provide a concise baseline for the entire earlier programme. The synthesis makes three new contributions relative to its 26-report baseline:

1. An explicit trace frame for the totally real S3 splitting field of `T^3-4T+1`, discriminant 229, with bound `M_F=48*229^2=2517168`. It tensors with a cyclotomic resolution while correctly accounting for the intersection `Q(sqrt(229))`.
2. A joint positive-average Mellin criterion. Positive filters individually can cancel nonreal poles; a family detects all poles exactly when its multipliers have no common zero. The example `P=5+6z`, `Q=25+30z+36z^2` uses `Q-6zP=25`.
3. Sharp positive-ramp Lp-to-pointwise bounds, with bounded positive coefficients supported at integer indices, explaining why direct averaged Landau arguments retain more information than first recovering a pointwise estimate.

The explicit S3 frame is not an admissible global source frame. It proves an embedding identity and integrality at the relevant inert primes. It does not prove membership in a compatible Weil lattice, availability of principal level frames, two coprime frame bounds, or a unit linear form at every prime. The synthesis clearly states this limitation.

The same report identifies three missing nonabelian arithmetic packages:

- `New.exists_length_shaOdd_le` in `Lib/Cyclotomic/OddSha.lean` needs the whole CM field contained in a cyclotomic field; that hypothesis excludes any CM field containing an S3 extension. A replacement must control growth in both tower level and weight, not merely prove each obstruction group finite.
- Compatible different/Weil-lattice data, level primes, and coprime frames are missing. Congruences `p=1 mod N` do not force splitting in a nonabelian field.
- Cyclotomic local defect and sparse-place arguments must be rebuilt; an abstract finite-group second moment alone does not supply the desired arithmetic moment estimate.

### Arithmetic completions reported in the synthesis

The synthesis endorses the earlier exponent-six result: exactly 432 imaginary quadratic fields and 1,236 imaginary quadratic orders have class group of exact exponent six. It says it reran an explicit-formula interval test and two exact divisor searches closing the residual discriminant interval. The initial published enumeration through `3.1e20` remains an input. This review read the proof structure; it did not independently rerun those certificates. This classification must be credited to the earlier report, not relabelled as new work now.

The corresponding exponent-seven question remains open in that synthesis. The previous report proves an upper bound `4*4600^7 = 174327062886400000000000000` for any omitted discriminant, beyond the 33 known fields in the initial range. The exponent-six pigeonhole collision does not survive unchanged: the forced split-prime count no longer exceeds the admissible norm-equation coefficient count.

The sparse-CM reports claim a global classification `s<=5 iff h<=4`, with support-growth consequences, after closing earlier exceptional five-term cases. The synthesis rechecked selected disk, reduced-form, and determinant inputs but not the entire global computation. Treat as a prior claim with that validation boundary unless its full certificates are replayed.

## Five reports outside the synthesis corpus

### Structural transfers

Path: `extracted/grh_structural_transfers_2026-11-25/grh_structural_transfers/`.

The source global congruence term is not a Selmer rank. For a lattice T and conjugate Tate dual D(T), the report proves the exact finite-level Smith formula

`C_n(T) = h*n + sum_j min(n,a_j)`,

where h is the dimension of the rational equivariant Hom space and a_j are the nonzero Smith valuations of one finite relation matrix. A finite set of equations suffices modulo all powers because the module of all relation rows is Noetherian. Thus the global congruence term is finite iff the rational Hom space vanishes.

Anticyclotomic twisting preserves the entire intertwining equation, so it cannot repair rational conjugate Tate self-duality. A polarized abelian variety descended from a totally real field gives a symmetric conjugate Weil pairing, hence an unbounded contribution. This defeats a direct BSD instantiation.

The report sharpens the source mirror map: its image consists of symmetric conjugate-dual maps, by the source `mirrorForm_eq_zero` identity and spanning. If the only rational invariant pairing is alternating, this smaller target is bounded. Under the source integral Burnside hypothesis, its exact length is `min(n,v_pi(2))`; for symmetric sign it is n. The report explicitly leaves a full generalized Selmer theorem/refactor unbuilt.

An exact weight-24 modular-form projector example has denominator ideal `(24*sqrt(144169))`; the smallest rational integer clearing all entries is 3,460,056. Keeping the full two-form Galois orbit avoids the projector but not the missing arithmetic comparison.

Files read closely: `sections/duality.tex`, `sections/symmetry.tex`, `sections/programme.tex`, plus report findings.

### Torsion and prime sampling

Path: `extracted/grh-torsion-and-prime-sampling/`.

This report already proves exact one-variable shell obstruction budgets; fixed coefficient-field zero-loss bounds; an exact cyclotomic coefficient-field descent formula; and a multivariable iterative bound. It explicitly raises arbitrary finite ramified coefficient fields and sharper multivariable bounds as further questions.

It also gives a sparse zero-simplicity criterion. With `x_n=2^n*3^(n^2)`, Weyl equidistribution and an absolutely convergent explicit formula show the mean of `x_n*R_Q(x_n)^2` is `sum_t m(t)^2/(1/4+t^2)^2`. Simplicity is equivalent to equality with `4 H_Q(1)-2 H_Q'(1)`, explicitly `6+2gamma-2log(4pi)+4gamma_1+2gamma^2-pi^2/4`. This remains a criterion: the matching upper bound on the prime side is open. It is not a newly proved simplicity theorem.

### Torsion and zero data

Path: `extracted/grh-torsion-and-zero-data/grh-torsion-and-zero-data/`.

This report proves a sharp unrestricted-coefficient minimax shell budget, with a transition at `p/(p-1)` and exponential worst-case order exponent in inverse tolerance above it. The concrete example `p=2`, budget 3, tolerance 1/8 has worst first successful exponent 372, versus 4 over Q_2.

It also recovers source arithmetic parameters from a finite signed zero list with certified precision, and gives an optimized symmetric-power detector for a non-CM elliptic curve. The arithmetic estimate realizing that detector is still open.

### Exact torsion specialization

Path: `extracted/grh_exact_torsion_transfer_2026-11-25/grh_exact_torsion_transfer/`.

This report already uses the discrete number of roots in each shell to derive exact specialization for one polynomial, hence for the aggregate valuation of a finite packet, with a uniform order bound independent of degree and coefficient field. The bound is `h0+ceil(p^h0 * B * (h0+B+2))`. It does not give cardinality-free simultaneous exact bounds for every individual member of an arbitrary packet. It includes a positive-tolerance improvement, multivariable/bounded-analytic versions, and explicit impossibility results for cardinality-free exact individual bounds and for a moving Gauss target. Its application to a new fixed Selmer or K-group still needs an arithmetic comparison and ramification control.

### Singular moduli and symmetric powers

Path: `extracted/grh_transfers_singular_moduli_and_symmetric_powers/`.

The report already contains a Gaussian prime-conductor full-support lower relative density greater than `0.999818260107372245`, independent of RH and GRH. It combines multiplicative disks at 2, 3, and 7 and exact factorial-comparison density sieves. It also proves exact optimized nonnegative symmetric-power test polynomials using quasi-Gaussian quadrature. Its positive arithmetic bound for symmetric powers of Delta remains an unmet hypothesis. Quadrature/positive-polynomial optimization is therefore not an untouched new direction.

## Recommendations for the present work

1. Do not add another character-table criterion and call it a resolved open conjecture. Prior reports cover S3, Sn, A5, A6, Sylow, cyclic generators, reflection groups, PSL2, Kummer windows, relative prime races, deficits, symmetric powers, sparse sampling, moment bounds, and joint filters.
2. A useful advance would be a substantive local or global arithmetic lemma that removes one identified obstruction. A codifferent-based clarification of the S3 frame issue is well targeted: plain integral tight frames at ramified primes have unavoidable divisibility in their bounds, while the source frames use a fractional Weil lattice. The transfer must modify the lattice/duality data, not simply seek better integral weights.
3. The Selmer symmetric-image refinement is already proved in the structural report; formalizing it would be new implementation work but not new mathematical discovery. A rank-sensitive mirror-preimage bound could be substantive, but is presently missing.
4. The exponent-seven finite interval is a concrete arithmetic research target, but simply adapting the exponent-six script does not work.
5. State the inspection boundary. This review directly read nine archives (latest synthesis, five absent reports, three selected predecessors), while the remaining 23 reports are represented by the latest synthesis's claim matrix rather than a fresh independent proof audit.

## Exact archive identities for cited baselines

| Archive | Git blob SHA |
|---|---|
| grh_transfer_synthesis_2026-11-25.zip | 266406881cea5e9ab39e9e4fb41214b537fcab21 |
| grh_structural_transfers_2026-11-25.zip | ba5f8d5d0122f9af246eac54d6eced90dc089c96 |
| grh-torsion-and-prime-sampling.zip | d3829f100d4c9e27d2168ca5c851ff6307ed0877 |
| grh-torsion-and-zero-data.zip | 8a2ade56c8e54552458da576dcfd9bcebe0be170 |
| grh_exact_torsion_transfer_2026-11-25.zip | fb41113c0dc2d8929100d1e005a8d4275a54d7a2 |
| grh_transfers_singular_moduli_and_symmetric_powers.zip | bb21bc82aa992fcb7bb8fc58c06292ab89763538 |
| grh-exponent-six-and-transfers.zip | 27e55259ff1bb021be0c3f4077014690dd5629d7 |
| grh_sparse_singular_moduli.zip | 0d5a83ba283e3d100168c9569cb981c010bafe7c |
| grh_quantitative_twists_2026-11-25.zip | 3468e65ff562dd2f77b9322d2ca484925b3e721d |

Pinned citation prefix: `https://github.com/VladimirReshetnikov/ProveIt/blob/28ad287a8d13c0f864ebb51c7c053ad06aa6e585/docs/incoming/`.
