# Subexponential SAT: combined bounds and exact implementation improvements

Prepared for Vladimir Reshetnikov, October 26, 2026 (Pacific time).

Read **report.pdf**. Complete editable LaTeX is in `report.tex` and the four
included `.tex` sections. The report reviews seven established packets and
eight second-round packets, including the final matching-packing arrival, at ProveIt commit
`474ddba696a5d385c091c23fb2995f69edd13e00`.

## Results

For the stated normalized Boolean tensor interface (at most s wires, maximum
degree at most ceil(s^0.9), and the specified entry-oracle and precision bounds):

* Polynomial-space time coefficient **63.85220339055**, with convenient
  eventual coefficient **64**, on the scale s/sqrt(log2 s).
* Cached time coefficient **37.93010908288** and space coefficient
  **33.62304092166**, with convenient eventual coefficients **38 / 34**.
* An exact replacement for the existing asymmetric packet-labeling function
  reduces candidate-scoring work from O(N Q^3) to O(N Q^2) rational operations.
  It preserves all scores, labels, tie breaks, and returned certificates.
* Precision peeling computes normalized mode contributions at P−V bits,
  with safe division and frozen creation-time precision caps.

The comparison includes compatible prior compositions, including the stronger
fixed-alphabet cached boundary coefficient 38.1677456970. No claim of global
schedule optimality is made. The closing check also verified 187 relocated files byte-for-byte against the
initially reviewed archives. The mathematical constructions retain the
stated upstream exact-contraction dependencies. The SAT logarithmic order
is unchanged; coefficients are not automatically coefficients per SAT
variable. This package does not contain a full SAT solver or a new Lean/Rocq
formalization.

## Practical evidence

The labeling implementation matches the actual supplied reference on 840
complete certificates and 9,724 candidate scores, plus certificate-disabled
and invalid-input checks. Five paired timing trials give speedups from 1.50x
to 9.56x across the recorded fixtures; the largest is 304.464 ms versus
31.833 ms. Both implementations keep their exact internal checks enabled.

Precision peeling passes 544 randomized cyclic contractions, 18 actual-domain
Cauchy contraction comparisons, four invalid-input checks, and 1,601 canonical
cap checks. Its separate synthetic arithmetic benchmark records up to 14.34x
at residual precision 64 from input precision 2048, including normalization.
These are subroutine/kernel measurements, not end-to-end SAT timings.

## Files

* `report.pdf`, `report.tex`, `theory.tex`, `implementation.tex`,
  `delivery.tex`, `references.tex`: complete report and source.
* `code/cached_balancing.py`: improved labeling implementation with the
  original public function signature and returned data.
* `code/reference_balanced_packing.py`: byte-identical prior implementation.
* `code/precision_peeling.py`: exact scalar cyclic-contraction primitive,
  actual-domain Cauchy checks, and exact partition-work inventory.
* `code/verify_*.py`: exact correctness and schedule checkers.
* `code/benchmark_*.py`: paired, reproducible benchmark drivers.
* `results/`: recorded benchmarks, all raw trials, deterministic check outputs.
* `notes/`: detailed source audits and independent mathematical review.
* `provenance/`: immutable source pin, source hashes, archive members, license,
  and reference-code attribution.
* `PROOF_STATUS.json`: explicit established/imported/unresolved claim map.
* `MANIFEST.json`: hashes of delivered files, excluding itself.

## Reproduce

Python 3.10 or newer, standard library only for mathematical verification and
both benchmark programs:

```sh
python3 verify_manifest.py
python3 run_checks.py
python3 code/benchmark_cached_balancing.py --output new_packing_times.json
python3 code/benchmark_precision_peeling.py --output new_precision_times.json
```

`run_checks.py` runs all four checkers normally and with `python -O`, then
compares their parsed mathematical results. It writes to `replay_results/`
without overwriting the recorded evidence. Checks do not depend on removable
assert statements. On Windows, use `py` instead of `python3` if appropriate.

The supplied figure is sufficient to build the report. To regenerate the
figure from the recorded JSON, install Matplotlib and run:

```sh
python3 code/make_figures.py
```

To compile the LaTeX, use a standard TeX Live or MiKTeX installation with the
packages named in `report.tex`, then run:

```sh
python3 build_report.py
```

The build disables shell escape and requires no network. Temporary files go
to `_build/`. Original measurements remain in `results/`; benchmark runtimes
will vary by machine and load. The manifest establishes internal consistency,
not authenticity or independent formal verification.

## Integration

Start by replacing the original `balance_pair_labels` implementation with
`code/cached_balancing.py` and running the exact comparison suite. Adopt the
new contraction schedules only with their full packing and precision gates.
The cached schedule changes the memory guarantee. For precision peeling,
freeze the reduced child at its new creation precision; later lifting must
not return to an older representative. The report provides the full proofs
and source-to-change map.

No remote repository files were modified during this review.
