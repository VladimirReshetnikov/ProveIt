# Independent accelerator and sample-CA audit

## Result

PASS. No defect was found in the intended sample-CA API or accelerator. The audited source SHA-256 is recorded in `audit-results.json`. This is an implementation audit and mathematical inspection, not machine-checked verification of the theorem or an exhaustive search over cellular automata.

Run with Python 3 and the standard library only:

```
python audit_accelerator.py --module /path/to/test_single_unit_acceleration.py
```

If this file and the audit script are placed under `independent/` beside a parent `test_single_unit_acceleration.py`, omit `--module`. By default JSON is written beside the audit script; `--output PATH` overrides its destination. The original module is imported without invoking its main test run and is never modified.

## Independent checks

The audit covers all 23 sample rules. Its completed run includes:

- 1,186 boundary initial configurations and 118,600 accelerated/direct time comparisons, plus a translated replay of every comparison with offset −10^20+37
- Boundaries around S, 2S and 4S, both marker orientations, heavy labels, empty/singleton inputs, reversed dictionary insertion order and normalization/sorting
- 4,109 first-core answers compared against independent direct simulation for up to 200 steps, including no-hit cases, transient profiles and nonzero/zero phase drift
- 66 linear-solver cases with predetermined answers at huge positive and negative offsets and with positive, negative and zero drift
- Gap 10^40+17, 61 exact closed-form whole-configuration checks, 300 direct checks following huge-gap core entry, and reflected binary trajectories at time 10^80+123
- Huge-gap approach in both directions; typed oscillating zero-drift walkers; typed transient conversion to fixed unit pairs; ordinary four-state merge and escape; and support reordering after interactions
- 216,160 finite-window conservation tests, including all binary windows of width 11 for every binary/ECA sample, all ordinary four-state windows of width 8, all weighted-alphabet windows of width 5, and targeted guarded-rewrite cases
- 7,616 rewrite exclusion-boundary/translation cases and 11,500 finite locality comparisons
- 900 direct huge-gap ECA comparisons and five fixed-three-unit ECA checks at time 10^80+123 after the sparse evaluator improvement

These finite tests supplement the exact conservation arguments below. Passing dense windows alone would not prove conservation for arbitrary configurations.

## Exact conservation and locality arguments

### Binary directed swaps

Each chosen update replaces an input 10 pair by 01 in one fixed direction. All chosen pairs are disjoint: their sources are distinct occupied sites, their targets are distinct empty sites, and an input-empty target cannot equal another input-occupied source. Each swap preserves numerical mass exactly, for every finite configuration. Context selection only decides which disjoint swaps occur and cannot change this argument. An output site's own departure and possible arrival depend only on radius-2 data.

### Elementary rules

The audit independently traverses the de Bruijn graph, constructs candidate vertex potentials, and checks every local identity

f(a,b,c) − b = P(b,c) − P(a,b).

Exactly rules 170, 184, 204, 226 and 240 pass among all 256 rules. Verified potentials, in vertex order 00, 01, 10, 11, are:

| Rule | Potentials |
|---|---|
| 170 | 0, 1, 0, 1 |
| 184 | 0, 0, −1, 0 |
| 204 | 0, 0, 0, 0 |
| 226 | 0, 1, 0, 0 |
| 240 | 0, 0, −1, −1 |

The identity telescopes on every finite-support configuration because both far boundaries have vertex 00. This proves conservation exactly, rather than only on the tested windows. A comoving translation also preserves mass.

### Ordinary four-state and weighted rewrite rules

A heavy center is eligible only when no other heavy center lies at distance at most 4. Eligible centers are therefore separated by at least 5. Every rewrite changes sites only in its center's radius-1 interval, so these change regions are disjoint. The guards either require destination sites to be empty or explicitly consume their unit occupants. Suppressed heavy centers cannot be touched by an eligible rewrite.

Every elementary rewrite preserves the listed weights: moving or relabeling a weight-2 symbol keeps mass 2; consuming an adjacent unit gives 2+1=3; splitting a weight-2 symbol gives 1+1=2; splitting a weight-3 symbol gives 1+2=3. Consequently every finite configuration conserves mass, with no assumption that total mass is at most 3. To determine an output site, one needs possible centers within distance 1 and their exclusion neighborhoods out to distance 4, giving radius 5.

## Accelerator inspection

The first-core bounds are correct. For a mass-2 profile with left endpoint a, width w and marker b, diameter at most B is equivalent to b−B ≤ a ≤ b+B−w, since w ≤ B. Each phase uses its actual translated left endpoint and a nonnegative cycle count. The sign reversal in the negative-drift linear solver preserves both inequalities.

Normalized-state repetitions record the correct elapsed time and translation. Cycle replay maps to already stored segments, including intermediate excursions. Lambda defaults freeze the intended per-segment configurations and profile objects. First entry is excluded from an outside segment and handled by the next core segment, avoiding off-by-one overlap. Dictionary sorting and large negative translations passed independent replay.

The harness consistently names its unique unit symbol `u`; the accelerator's hardcoded unit label is appropriate for these sample rules. It should not be advertised as a drop-in interface for arbitrary symbol names without a renaming convention or parameter.

The final elementary-rule evaluator visits only radius-one neighborhoods of occupied sites and explicitly requires f(000)=0. This is equivalent to the original support-hull scan, since every site outside those neighborhoods has an all-zero input neighborhood. The revised evaluator also passes direct astronomical-gap tests; the original support-hull performance limitation is removed. The portable audit was replayed from an unrelated working directory against the final copied source.
