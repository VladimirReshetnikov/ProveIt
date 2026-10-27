# Degree-aware schedules and consistency certificates for 3-SAT contraction

Research prepared for Vladimir Reshetnikov, October 26, 2026 (Pacific time).

Start with **report.pdf**. Its complete source is **report.tex** plus `sections/`
and `results/constants.tex`. This archive is self-contained for checking the
new finite certificates; its asymptotic theorems explicitly import the exact
deformation, mode-entropy, packing, recovery, and matrix interfaces of the
reviewed sources. It contains no new Lean formalization or full fast SAT solver.

## Main results

All coefficients below multiply `s / sqrt(ceil(log2(s)))` in a base-two
exponent. Here `s` is a normalized Boolean tensor-wire budget, **not the number
of SAT variables**. Time and space bounds include polynomial description-size
factors. Each row's time and space are achieved simultaneously.

| Input degree promise | Time coefficient | Space coefficient | Contribution |
|---|---:|---:|---|
| `Delta <= s^0.51` | `< 13.690` eventually | `< 12.798` eventually | Degree-aware composition of the complete paid recursion; applicable after the already known square-root-degree 3-SAT grouping |
| `Delta <= ceil(s^0.9)` | `29.74605709379457...` | `28.32957818456625...` | New exact support-consistency certificate; previous matching generic time coefficient `29.81160894538347...` |

The lower-degree leading time coefficient is `13.68968074358...`; its space
coefficient is `12.79756505004...`. Its time improvement comes from the new
degree-sensitive schedule and already available contraction plans. Applying
the old pairwise certificate under this same schedule gives the same leading
time coefficient: the depth-one branch dominates. The new consistency
certificate supplies the tighter simultaneous root-space bound.

The lower-degree schedule is

```
group counts: 10, 13, 7, 7, ...
eta_0 = 59/800
eta_1 = 181/4000
eta_d = (89/5000) * (4/9)^(d-2),  d >= 2
sum eta_d = 472/3125
```

The generic theorem uses the earlier schedule unchanged, and improves the
leading time coefficient by about 0.21989%. Its space coefficient improves by
about 4.97% relative to the accompanying space bound of the fastest generic
incoming packet. These are comparisons of exponent coefficients, not measured
speedups or ratios of actual memory consumption.

For a stronger lower-degree comparison, uniformly scaling the old incoming
schedule by `17/4` already gives `14.46075441781...` time. The new stage-specific
allocation improves this inherited composition by about 5.33%, to
`13.68968074358...`. The scaled comparator is evaluated here, rather than being
a coefficient printed in an earlier packet. Neither value is an optimality
claim over all possible schedules. The existing `13.379649...` cached option
for the stronger degree `s^(1/12)` remains separate.

**No smaller unrestricted logarithmic order for 3-SAT is proved.** The general
order remains `2^{O(n log log n / sqrt(log n))}` up to polynomial input factors;
the fixed-density order remains `2^{O_D(n / sqrt(log n))}`. The degree-sensitive
improvement must be compared with earlier degree-sensitive algorithms, not
only with the generic headline bounds. The report makes this distinction and
credits readily extendable older schedules. Unknown constants in the separate
Anthropic development prevent a numerical ranking against that algorithm.

## The new consistency inequality

An incoming norm bound maximizes each pair of plan supports independently.
These independent maxima can choose conflicting supports for the same plan.
We redistribute support-dependent potentials among the pairs, with their sum
exactly zero at every indexed support. Every genuine simultaneous choice has
unchanged total cost, while the sum of independent upper bounds decreases.

The witness contains rational weights on nine plans and integer potential
numerators. A fixed common denominator makes every verification decision an
integer comparison. The exact result is

```
beta_10^2 = 283611964650596186827 / 875000000000000000000.
```

Seventeen boundary supports per plan can be added with multiplier `21/20`
without increasing any certified pair maximum. The algorithm selects one plan
minimizing the maximum of its time score and `21/20` times its storage score.
This is essential for simultaneous time and space bounds.

An exact Gram-matrix witness puts this fixed nine-plan, fixed-root-taper
average-norm method within `4.3e-10` of its best possible generic time
coefficient. This does not prove that the actual adaptive minimum, other
menus, or 3-SAT algorithms are optimal.

The report also proves a full-rank obstruction for a particular universal
bilinear summary of variable unions, a sharper degree-array counting bound,
and an obstruction to exhaustive array enumeration with uniformly small
groups. These are narrowly stated representation results, not SAT lower bounds.

## Reproduce

Python 3.10+ and the standard library suffice for all exact verification.
From the extracted archive directory:

```sh
python3 code/verify_manifest.py
python3 code/run_checks.py
```

The first command checks all shipped file hashes. Run it before rebuilding
files. The second reconstructs supports and runs the exact checkers normally
and with `python -O`, requires identical parsed results, and saves receipts
under `replay_results/`. The delivered receipts are under `results/verified/`.
The checks use explicit exceptions rather than removable assertions.

Rebuild the manuscript with a normal pdfLaTeX installation:

```sh
python3 code/build_report.py
```

The builder runs pdfLaTeX three times with shell escape disabled and rejects
overfull boxes and unresolved references. The preamble lists the required
standard LaTeX packages. A later PDF build can have different metadata bytes.

Optional numerical discovery, requiring NumPy:

```sh
python3 code/discover_certificate.py --sweeps 80
```

This optional run was executed and reproduced the exact displayed beta
fraction after rounding and exact verification. Discovery is not needed to
trust or replay the delivered witness.

## File map

- `report.pdf`, `report.tex`, `sections/`: complete argument and review of all
  29 filed packets and five newer incoming packets.
- `data/support_consistency_certificate.json`: exact potential witness.
- `data/support_consistency_receipts.json`: frozen pair-maxima receipts.
- `data/exact_optimal_weights.json`: exact Gram and stationary-weight witness.
- `code/certify.py`: primary exact support, schedule, and coefficient check.
- `code/independent_audit.py`, `code/independent_joint_audit.py`: independently
  reconstructed support and joint-storage checks.
- `code/check_low_degree.py`: degree-sensitive schedule and matched old/new
  comparison.
- `code/check_weight_lower_bound.py`: exact near-optimality witness.
- `code/check_inherited_menus.py`: complete inherited 13- and 7-group supports.
- `code/check_structures.py`: independent finite checks of structural identities.
- `code/finite_contraction.py`: finite exact prototype over a ring with zero
  divisors; ordinary scalar multiplication, not the fast matrix backend.
- `code/run_checks.py`, `code/build_report.py`, `code/verify_manifest.py`:
  reproduction entry points.
- `results/`: exact and numerical receipts, including normal/optimized replay.
- `provenance/`: pinned source inventory, commit history, downloaded-file hashes,
  and final document checks.
- `CLAIMS.json`: machine-readable proof-status distinctions.
- `INTEGRATION.md`: suggested placement in ProveIt without changes to original
  upstream manuscripts or formalization status.
- `MANIFEST.json`: SHA-256 integrity manifest of this deliverable.

## Frozen comparison

ProveIt: `8e76d515063c4b9fbd8743a846b457e3a01bc039`.
The five latest incoming packets were added by
`26bd83d4b37d3c5a3ccb45bab2e6385fae3977f1`.
Anthropic source revision: `1a6eee293b9e00cb432eef6018a21f523623a9af`.
OpenAI formalization scope page:
`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, `lean/docs/378.md`.

The source inventory covers 148 downloaded objects checked against their Git
blob identifiers. Source identity, finite certificate replay, analytic proof
dependencies, and Lean source inspection are separate claims. No full Lean
project was rebuilt for this report.
