# Smaller explicit Diophantine forms of ZFC consistency

This research package combines constructions from ProveIt's audited
`con-zfc-diophantine-forms` catalogue at commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`.

For every delivered form, with its stated domain, the ordinary mathematical
proof establishes in ZFC that **there is no solution if and only if
Con(ZFC)**. The positive form of the equivalence says that solutions exist
exactly when a finite ZFC refutation exists. New proofs are formalizable in
ZFC but have not been converted to an end-to-end Lean or Rocq certificate.

## Results

| Construction | Domain | Variables | Equations | Exact degree / maximum residual degree | Binary operations |
| --- | --- | ---: | ---: | --- | ---: |
| Signed 16 | Integers | 16 | 1 | `813056*5^32+10024` | 1865 |
| Signed 17 | Integers | 17 | 1 | `406528*5^32+27512` | 1874 |
| Positive cancellation | Positive integers | 12 | 1 | 1065 | 118 |
| Positive economical | Positive integers | 12 | 1 | 1081 | 108 |
| Cancellation system | Positive integers | 12 | 3 | 1056 | 114 |
| Cancellation shifted system | Positive integers | 12 | 3 | 1056 | 113 |
| Economical system | Positive integers | 12 | 3 | 1072 | 104 |
| Economical shifted system | Positive integers | 12 | 3 | 1072 | 103 |
| Quadratic system | Positive integers | 31 | 22 | 2 | 62 |
| Quartic sum of squares | Positive integers | 31 | 1 | 4 | 127 |

Operations are binary addition, subtraction, or multiplication; squaring
and multiplication by fixed numerals are charged, reuse and equality
comparisons are free. Constructing fixed integers is separate from
evaluating the variable-dependent circuit. Named intermediate nodes are
abbreviations, not extra unknowns. The comparison convention matters for
systems: forming their residuals and summing their squares has extra cost.

The new coefficient tuple uses `B=2^1064921`. All four direct integers are
materialized as minimal unsigned little-endian files. Together they occupy
533,099 raw bytes, compared with the preceding minimum of 977,220 bytes.
The much larger fixed Jones indices are specified by exact finite recipes;
their physically enormous expansions are not included or needed.

Read [report.pdf](report.pdf) for the full exposition. Its source is
[report.tex](report.tex), with all included sections in `sections/`.
[RESULTS.json](RESULTS.json) records every delivered form and its binding.

## Main combinations

1. Combine the compact 31-variable Jones evaluator with the signed relation
   combiner, use a smaller signed separating weight, and restrict the
   coding radix to a cofinal family `b=b_scale*e^2`. This removes one guard
   witness and yields the 16-integer equation.
2. Combine the sharp positive-root bound with the weighted carrier and the
   compact trace/product norm. The smaller carrier creates two more
   leading cancellations, lowering degree 1069 to 1065.
3. Reassociate the economical norm evaluator to save three operations.
4. Shift three positive coordinates in the quartic system, saving another
   three operations without changing the variable count or degree.
5. Combine mixed-radix local decoding and zero-field population padding
   with a general odd-dimension Boolean controller. This yields the
   smaller complete coefficient tuple.

## Reproduce all finite checks

Requirements: Python 3.10 or later, standard library only. No network,
proof-assistant installation, or simulation of the machine is required.

```sh
python3 reproduce.py
```

The script resolves paths relative to itself, so it also works when invoked
from another directory. It verifies authenticated sources, runs all seven
component builders/audits, compares the regenerated mathematical artifacts
with the delivered files, and writes `verification/REPRODUCE.json` plus
individual logs. Run without `python -O`, which disables assertions.

To check the original delivery's byte integrity before rebuilding:

```sh
python3 reproduce.py --check-manifest
```

To rebuild the report:

```sh
make pdf
```

This runs `pdflatex` twice with no shell escape. Common TeX Live packages
used by the sources are listed in `report.tex`.

## File map and fixed coefficient binding

| Directory or file | Contents |
| --- | --- |
| `coefficients/` | Literal K215 table, coefficient generator, raw/gzip integer files, binding and receipts |
| `positive/` | Six retained 12-variable circuits, generator, checks, component README |
| `quartic/` | 62-operation system, 127-operation quartic, sparse polynomial audit |
| `integers/` | 16-/17-integer generators, circuits, index recipes, degree certificates, authenticated source subset |
| `sources/` | Pinned inherited proofs, catalogue, endpoint statements, and `SOURCE_MAP.json` |
| `reviews/` | Independent mathematical reviews and separately implemented finite checks |
| `verification/` | Reproduction receipts and logs |
| `LICENSE`, `NOTICE.md`, `licenses/` | Repository license, attribution and inherited third-party notices |

The direct ports **must be replaced as one complete tuple**:

| Circuit port | File in `coefficients/` |
| --- | --- |
| `beta` | `beta.bin` |
| `K0` | `K.bin` |
| `MC` | `MC.bin` |
| `MF` | `MF_source.bin` |

Here `MF_source = MF_native+B-1`; using the native mask as the fourth
input is incorrect. The signed circuits' fixed leaves are defined by
`integers/generated/INDEX_CONSTANTS.json`. In particular, the 16-variable
circuit uses `b_scale=2^(4269856*(5^32+1))` and has no `y_index` leaf.

The signed branch intentionally uses the **predecessor's** literal quartic31,
rebound to the new complete tuple. The new shifted quartic is separate.
Substituting one for the other requires rebuilding all Jones index data.

## Proof and comparison boundaries

The new reductions have ordinary proofs and explicit inherited interfaces.
Finite checks verify the literal implementations, not consistency or an
unbounded machine computation. The independent reviews are separate work
inside this AI-assisted collaboration and are not external endorsements.

The comparisons concern the frozen repository catalogue, not universal
minimality. The existing nine-positive-variable route, 67-operation single
equation, and 59-operation higher-degree systems retain their respective
advantages. Sun's September 2026 ten-integer representation theorem gives
a smaller general bound but has not been instantiated to a fixed K215
polynomial here. The report discusses that distinction explicitly.

The archive is suitable as a new contribution beside the current numbered
packages; it changes none of their files. All source paths in
`sources/SOURCE_MAP.json` refer to the frozen commit rather than `main`.
