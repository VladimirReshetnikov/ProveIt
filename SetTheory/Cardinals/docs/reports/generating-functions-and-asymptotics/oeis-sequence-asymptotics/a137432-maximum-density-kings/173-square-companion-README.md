# Report 173: reproducible computational companion

This package checks the formulas for OEIS A137432: placements of n² nonattacking
kings on a labeled 2n × 2n board whose columns wrap and whose rows do not.
Rotations and reflections are **not** identified. The empty-board convention is
a(0)=1. Every script in this directory is original companion code; no downloaded
Matsuo implementation, paper, book, or internal working document is included.

## Quick start

Use Python 3.10 or newer. Default checks require only the standard library,
make no network requests, and neither install packages nor write to the source.
From this directory:

```sh
python3 -B run_checks.py
python3 -O -B run_checks.py
```

Both commands emit identical deterministic JSON. Checks use explicit exceptions,
so optimized Python does not remove correctness checks. A failed check produces
a nonzero exit code. The default workload is deliberately small:

- Every binary word at 1 ≤ n ≤ 7 (254 words): compare the directly defined
  transition matrix M with E₀E₁, compare its nth-power trace with the Gram trace,
  and compare twice that trace with the 2nth-power trace of the full tree
- Check connectedness, edge/vertex counts, and 0–1 component intersections for
  every such word; compare summed traces with the selected published terms
- An independent row-mask DP on the actual cylindrical board for 0 ≤ n ≤ 5
- Exact rational generating-function certificates for c₀,c₁,c₂,c₃; no sequence
  values or floating-point fitting enter these calculations

The matrix enumeration is exponential in n. It is intentionally a transparent
verification implementation, not Matsuo's more efficient counting algorithm.
The actual-board DP is also intended only for small n.

## Isolated, no-clobber rebuild

Choose a directory that does not exist, outside this source directory, with an
existing parent. For example, from the companion directory:

```sh
python3 -B rebuild.py --output ../verification-default
python3 -B verify_manifest.py ../verification-default/manifest.json
```

The rebuild creates `checks.json` and `manifest.json`. The manifest records
SHA-256 hashes of every packaged input and generated result, using relative
paths and excluding interpreter caches. It includes no timestamps, absolute
paths, or execution durations, so the same inputs, options, and interpreter/dependency versions give the same
bytes. It is an integrity receipt, not a digital signature or outside attestation.
A second build must use a fresh destination. Existing files are never replaced.
Subprocesses run in Python isolated mode, with a controlled source import path;
source directories are not populated with bytecode. This also works under `-O`.

To independently test deterministic output, use two fresh directories and compare
both `checks.json` and `manifest.json`. The rebuild emits `PASS` only after every
requested stage completes. A failed build may leave its new directory present;
inspect it and choose another fresh destination for a retry.

## Optional checks

### Larger exact enumeration

```sh
python3 -B run_checks.py --extended
python3 -B run_checks.py --transfer-max 8 --board-max 6
python3 -B rebuild.py --output ../verification-extended --extended
```

`--extended` checks **all three matrix identities at every word through n=10**
and the actual-board DP through n=7. It is substantially slower than default.
Supported fixture bounds are transfer n≤10 and actual-board n≤7. These are test
bounds, not validity limits of the formulas. Explicit maxima can be zero to
check only the empty-board convention for that enumerator.

### Generic finite-order symbolic engine

This optional script requires **SymPy**, installed separately in an environment
you control. No NumPy, mpmath, compiler, or external CAS is used elsewhere.

```sh
python3 -B symbolic_all_orders.py --order 3
python3 -B symbolic_all_orders.py --order 4
```

The order is any positive integer; expression size and runtime grow quickly.
Order 3 is the standard checked setting. Higher orders are algorithmic outputs,
not promises of practical runtime or new independently audited formulas.

The engine derives rooted-branch resolvents by finite power-series inversion,
solves the implicit equation for the large squared eigenvalue, and uses formal
logarithm/exponential recurrences to produce correction polynomials. It sums
boundary monomials with F(q)=(1−q)/(1−2q), h_j(q)=Σ(s≥1)s^j q^s, and Euler
derivatives q d/dq for powers of total boundary length. At orders 0–3 it checks
both the unsummed correction polynomial and the displayed rational coefficient.
It accepts arbitrary finite order and contains no hard-coded higher-order
coefficient. This is a computational realization of the report's fixed-order
algorithm; it does not prove the analytic uniform remainder estimate.

### High-precision residual diagnostics

```sh
python3 -B residuals.py --precision 80
python3 -B rebuild.py --output ../verification-all --symbolic --residuals
```

`residuals.py` needs only `decimal` from the standard library. It evaluates the
selected published integer terms at n=100,200,400,800 and prints

- a(n)/(C n^n)
- n²[a(n)/(C n^n)−1−c₁/n]
- n³[a(n)/(C n^n)−1−c₁/n−c₂/n²]
- the residual after c₃/n³

These published large terms are **not recomputed** here. Residual behavior is a
diagnostic and is not a proof of coefficient values, convergence, an effective
error bound, total-variation convergence, or the integer inverse theorem.

## Contents and mathematical independence

- `exact_counts.py`: integer-only matrix arithmetic, transfer/component/tree
  construction, and the separately implemented physical row-mask DP
- `coefficient_certificates.py`: sparse rational boundary polynomials and exact
  rational functions with denominator factors (1−q) and (1−2q); emits their
  numerator coefficients and an identically zero difference certificate
- `symbolic_all_orders.py`: optional independent generic formal derivation;
  shares only the displayed c₀–c₃ expressions and comparison polynomials
- `run_checks.py`, `rebuild.py`, `verify_manifest.py`: checking and integrity tools
- `residuals.py`: high-precision evaluation of the cited selected terms
- `fixtures/a137432_selected.json`: only n=1,…,10 and n=100,200,400,800, with source
  URL, retrieval date, and hash of the complete retrieved upstream b-file

A fixture hash records provenance of the retrieved upstream file; reproducing
this package never requires fetching or executing that file. The selected terms
are comparison data, not executable source. Exact default checks establish the
stated finite identities and the first coefficient formulas, while the report
supplies the mathematical arguments for all n and every fixed expansion order.

## Attribution and sources

- [OEIS A137432](https://oeis.org/A137432), and its
  [published integer table](https://oeis.org/A137432/b137432.txt), inspected
  2026-10-03. The fixture contains selected factual sequence values only
- The leading constant C=2e(e−1)²/(e−2)² is credited in the OEIS entry to
  Václav Kotěšovec (2023, updated 2024); it is not claimed as a new discovery
- Rintaro Matsuo's [A137432 project](https://github.com/windows-server-2003/OEIS_calculation/tree/master/contents/A137432)
  supplies prior binary-word/height encoding and polynomial-time counting work.
  This package reimplements small exact checks independently and neither copies
  nor executes that project's downloaded code

The companion is a reproducibility aid for an unrefereed report, not an external
peer review or a certification of exhaustive historical priority.
