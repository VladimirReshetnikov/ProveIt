# Report220: portable finite reproduction

This directory contains compact reproduction code and small machine-readable reference data. It is independent of a repository checkout and downloads nothing at runtime.

## Environment and commands

Tested with CPython 3.12.14. The combined replay and mpmath diagnostics require the usual integer-string digit limit of 4300 or larger; an already unlimited interpreter is also accepted. This requirement also applies when running `check_hypergraph.py` directly. Both diagnostic entry points explicitly reject a smaller configured limit before creating output and never change interpreter settings. Standalone certified recovery remains supported at the minimum configurable limit of 640. Install the exactly pinned dependencies in a virtual environment:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python reproduce.py
```

On Windows, use `.venv\Scripts\activate` instead of the activation line. The `rational_checks.py` recovery and certificate code uses only the Python standard library; SymPy and mpmath are needed by the symbolic and diagnostic scripts and combined negative controls.

The driver runs each program twice normally and twice with `python -O`, from separate temporary working directories. It rejects any byte difference among corresponding JSON files. One copy of each output and `reproduction_receipt.json` are saved in `results/`. It compares output bytes, not rounded printed summaries. JSON contains no runtime, timestamp, absolute path, hostname, or random identifier. The receipt records hashes of all generated result files.

Individual commands:

```sh
python derive_hierarchy.py
python check_hypergraph.py
python rational_checks.py suite
python rational_checks.py recover 2 25
python rational_checks.py recover 2 25 --cutoff harmonic
python negative_controls.py
```

Each command accepts an output option; use `--help`. Run from any working directory. Data defaults resolve relative to the script file. `recover d n` returns the recovered integer and its rational enclosure without computing the signed-Stirling/Fubini exact count when n >= 2. The endpoint identities n = 0 and n = 1 are handled separately. Recovery has no decimal-precision setting. The default `no_log` method uses the least positive integer M with `(6M)^d >= 2*d^d*n^(d-1)` and refines to interval width at most 1/4. The absolute omitted tail is strictly less than `13/(18*n^(d-1))`; the midpoint error budget is at most `35/72`, hence strictly below 1/2. The optional `harmonic` method uses the earlier harmonic cutoff and width at most 1/2. It has the smaller analytic tail bound but can retain more poles.

## What is established

- `derive_hierarchy.py` computes 15 exact symbolic coefficients through order four for d = 2, 3, 4 and compares them with the pinned coefficient reference
- `check_hypergraph.py` compares 27 small exact counts from two independent formulas and the sampled OEIS terms. Its 41 pole-tail checks and 72 asymptotic residual checks use high-precision mpmath. Those decimal diagnostics are **not interval certificates**
- `rational_checks.py` runs 29 primary integer recoveries, 29 separate exact-H-aware tail cross-checks, 35 independent small enumeration comparisons, and 10 endpoint recoveries. The finite inequality tests include 5,049 harmonic and 5,049 composition Stirling bounds, 55,539 factorial chains for each method, 1,089 cutoff/constant checks for each method, and 465 exact ordered-composition identities through n = 30. It uses exact integers, Fraction constant bounds, and outward dyadic interval arithmetic. Its standalone recovery chooses precision without an exact-count oracle. A separate, explicitly labeled exact-H-aware cross-check may refine further using the independently computed exact count
- `negative_controls.py` exercises 44 deliberate rejection cases and one oracle-independence test. It deliberately submits invalid mathematical domains, invalid interval inputs, context mismatches, and corrupted reference data. Each must raise an explicit exception. It also disables the exact-count oracles during a genuine precision-refining recovery

The finite computations do not prove universal analytic statements or all-order uniform asymptotics. Those conclusions depend on the proofs and hypotheses in the article. A successful finite tail cross-check must not be advertised as a proof for arbitrary d or n.

### Decimal-output and process semantics (v3)

Trusted computed integers are serialized in base-10 chunks of at most 18 digits. This supports large signed interval endpoints, integer answers, rational numerators and denominators, and numeric JSON fields without changing Python's interpreter-wide integer-string conversion setting. Output is canonical: zero is `0`, negative values have one minus sign, and leading zeros are absent. `certify` compares canonical computed answer strings directly; it does not parse its own large decimal output back into an integer. The decimal-output helper accepts actual integers only, not decimal strings. The JSON-output helper supports ordinary acyclic JSON data with string dictionary keys (and tuples represented as arrays); floats must be finite. NaN, infinities, non-string keys, and unsupported types are rejected. It does not serve as a general serializer for arbitrary Python objects.

This is an output-only change. Ordinary CLI argument conversion and reference JSON input parsing retain Python's configured digit guard. The code never disables or changes that guard, whether on import, success, or failure. It also does not promise unlimited computation: large d or n remain constrained by available time and memory.

The fixed-limit subprocess regressions in `negative_controls.json` run full recovery at `(d,n)=(2,150)` with `PYTHONINTMAXSTRDIGITS=640` and at `(2,600)` with the standard limit 4300. Each checks saved JSON against stdout, records a deterministic output hash, and verifies that an oversized external CLI integer is rejected. Additional tests cover 5,001-digit positive/negative integer and rational output, numeric JSON, zero/internal-zero padding, rejection of noninteger serializer inputs, unchanged generic `int`/JSON input guards, and synthetic large-output cross-check serialization. The synthetic interval tests serialization plumbing only; it is not an additional mathematical certificate. Both normal and optimized runs exercise these tests. Separate negative controls run both `reproduce.py` and direct `check_hypergraph.py` under 640 and verify clear preflight rejection and absence of output. Diagnostic corruption-control subprocesses explicitly use 4300, so direct `negative_controls.py` remains usable when the caller has a 640 limit. The precondition is checked at diagnostic call entry, never at module import. The diagnostic formatter remains unchanged; the combined-driver guard documents the mpmath 1.3.0 requirement rather than altering diagnostic precision or library behavior. Evidence records the explicitly requested child-process limits, so it is independent of the caller's inherited setting.

All enforcement uses explicit exception checks, never Python `assert`. Reference JSON is protected by SHA-256 over canonical JSON. This detects accidentally altered terms, identifiers, coefficients, or orders; it does not authenticate the historical source of a sequence. Coefficients are independently regenerated before comparison. The decimal diagnostics are guarded by the same reference readers tested by the corruption controls.

## Sources and provenance

The enumeration terms are the first nine values (n = 0 through 8) of [OEIS A173217](https://oeis.org/A173217), [OEIS A301466](https://oeis.org/A301466), and [OEIS A301468](https://oeis.org/A301468). Attribution: The Online Encyclopedia of Integer Sequences. This selected, JSON-formatted term sample is made available under CC BY-SA 4.0. The OEIS [license and attribution policy](https://oeis.org/wiki/The_OEIS_End-User_License_Agreement) applies to its entries. No full entry, paper, or source PDF is bundled. These terms are also recomputed by two independent exact formulas in the suite.

`PROVENANCE.json` records SHA-256 hashes of the small source scripts and reference data from which this portable version was adapted, along with the changes. These hashes identify inputs; they are separate from the reproduction receipt, which hashes the regenerated outputs. `SHA256SUMS.txt` inventories this finished bundle.
