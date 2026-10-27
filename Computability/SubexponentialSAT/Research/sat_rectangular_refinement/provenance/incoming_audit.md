# Review of the five newest 3-SAT packets

## Snapshot and coverage

The primary analysis snapshot is
[`8e76d515063c4b9fbd8743a846b457e3a01bc039`](https://github.com/VladimirReshetnikov/ProveIt/tree/8e76d515063c4b9fbd8743a846b457e3a01bc039/Computability/SubexponentialSAT).
Its project index lists **29** research packets in four rounds, with counts
7, 8, 5, and 9. The five newer archives arrived in
[`26bd83d4b37d3c5a3ccb45bab2e6385fae3977f1`](https://github.com/VladimirReshetnikov/ProveIt/commit/26bd83d4b37d3c5a3ccb45bab2e6385fae3977f1)
and were then still under `docs/incoming`. Thus the reviewed inventory contains
**34** packets. [packets.json](packets.json) distinguishes index review of the
29 placed packets from deeper source audit of these five arrivals, and records
exact paths, hashes, available artifacts, and scope. The 29 records' primary
SHA256 hashes identify named LaTeX sources; the five arrivals' primary hashes
identify ZIP bytes. They must not be confused.

For the five arrivals, the review read main LaTeX and relevant included
mathematical sections, including certificates, schedules, and stated barriers.
The original `sat_pairwise_certificates` cached and streamed checkers were
replayed successfully. This is a source audit and finite-certificate replay,
not an independent reconstruction of the entire imported SAT framework or a
new Lean build. [recent_commits.json](recent_commits.json) records the recent
requested-path history from local Git objects.

## The incoming comparison frontier

Each generic cached coefficient below multiplies
`s/sqrt(ceil(log2(s)))` in a base-two exponent. Here `s` is the normalized wire
budget, **not** the number of SAT variables. The common premises include the
previous normalization, Cauchy/Hermite reduction, balanced packing, canonical
creation-precision entry semantics, paid recursive entries, theoretical fast
matrix backend, and initial degree at most `ceil(s^0.9)`.

| Packet | Cached time | Cached space | Main mechanism |
|---|---:|---:|---|
| `sat_pairwise_certificates` | **29.81160894538347** | 29.81160894538347 | Weighted coupled-pair support certificate; rectangular products; 10 → 13 → 7 schedule |
| `sat_affine_contraction` | 30.25703561149638 | **25.98906771869022** | One joint time/boundary selector; affine 9-point and 12-point certificates |
| `sat_affine_geometry` | 30.26987291044112 | 29.48753728692122 | Affine and punctured menus; 9 → 12 → 8 → 7 → 4 |
| `sat_affine_cauchy` | 30.41334872634844 | 29.46603025659479 | Affine menu and 13 cyclic plans; 9 → 13 → 9 → 6 |
| `sat_affine_plane` | 30.69133782428595 | 29.46603025659479 | Affine 9-point and four-plan 13-point certificates; 9 → 13 → 7 |

Only the first two rows are Pareto points among these five generic cached
pairs. The generic polynomial-space comparison remains 46.184845586731… from
`sat_adaptive_bounds`. A distinct, stronger-degree premise in the pairwise
packet gives polynomial-space coefficient 16.81223380188329 at initial degree
at most `ceil(s^(1/12))`. These regimes must remain separate.

None of the five improves the unrestricted 3-SAT exponent order
`n log log n / sqrt(log n)` or the bounded-density order `n/sqrt(log n)`.
They supply finite certificates and local algorithms, not an end-to-end SAT
implementation or a practical runtime guarantee.

## Exact opportunity exploited in this report

The strongest incoming cached-time packet uses a weighted pair certificate.
For plans with support families `V_i`, weights `w_i`, sum `W`, and `q` plans,

    A_ij = max [w_i^2 ||v_i||^2 + w_j^2 ||v_j||^2
                + 2(q-1) w_i w_j <v_i,v_j>],
    U_2 = sum_{i<j} A_ij / ((q-1) W^2),
    beta^2 = 2 U_2 / (L^2 r^2).

Its root uses `r=10`, nine plans, support scale `L=1400000`, and weights
`137,124,135,120,108,119,106,87,64`. The exact root certificate is

    beta_10^2 = 15952347164548384057 / 49000000000000000000.

The old fixed schedule pays the root, depth-one, and infinite-cache branches
at approximately 29.8116089454, 29.3352039993, and 29.0657485246, respectively.
The root certificate is therefore the bottleneck. The present report's
subset-coupled extension replaces the sum of separate pair maxima by maxima
over triples, retaining correlations that the pair estimate discards. With
this same old backend and schedule, it proves 29.7768189451… instead of
29.8116089454…. Its updated matrix backend and independently paid new schedule
then give the separate 28.4337393784… time and 28.3057800303… space bounds.
Precise statements and all imported hypotheses are in the report; reproducible
finite checks are in [verify_certificates.py](../code/verify_certificates.py)
and [certificate_normal.json](../results/certificate_normal.json).

The new cached point does not dominate the incoming 30.2570356115 /
25.9890677187 memory point, and does not replace the polynomial-space results.

## Mechanisms and limitations already present upstream

The joint affine time/space selector is coherent: it chooses one plan that
controls both resources, rather than combining incompatible separately
optimized plans. The weighted pair proof is also coherent: every diagonal
term occurs in `q-1` pairs, and a maximum is taken independently only after
the required norm expansion. This does not assume simultaneous attainment of
all pair maxima. No fatal error was found in these inspected identities,
recurrence charging, or the scoped barriers.

The incoming packets already analyze several tempting order improvements:
Cauchy-to-clique budget cancellation; a four-energy crossing-window rank
obstruction forcing denominator power at most one half under that interface;
the exponential cost of independently enumerating too many crossing pieces;
failure of current locality after thinning oscillator modes; sharpness of the
flag coefficient over all binary separator trees in its entropy model; and
loss of the needed cancellation in a restricted odd-prime substitution.
These are limitations of specific constructions and proof models, not lower
bounds for SAT. Repeating these observations would not constitute a new
order improvement. A conditional graded-dimension improvement still needs
new exact identities and effectivity bounds that escape the stated interface.

## Closing check against the repository update

The observed closing head was
[`0cf10036e6ad732c27f13e6058f4acd9b3d78415`](https://github.com/VladimirReshetnikov/ProveIt/commit/0cf10036e6ad732c27f13e6058f4acd9b3d78415).
The only subsequent commit touching the two requested paths was
[`324f3d9b009ab0323f33be65cd6577867c9c4338`](https://github.com/VladimirReshetnikov/ProveIt/commit/324f3d9b009ab0323f33be65cd6577867c9c4338),
which placed these five packets under `Computability/SubexponentialSAT/Research`.
Comparison of exact ZIP member bytes with Git blob IDs found **all 213 placed
files byte-identical**, including all 160 `.tex`, `.py`, and `.json` files.
There were no mismatches or unexpected added packet files. The nine omitted
members were the documented generated byproducts, duplicated project README,
and checksum ledger. [round5_closure.json](round5_closure.json) records every
comparison. Thus that placement introduced no mathematical change requiring a
second source audit, and the primary analysis pin remains unchanged.
