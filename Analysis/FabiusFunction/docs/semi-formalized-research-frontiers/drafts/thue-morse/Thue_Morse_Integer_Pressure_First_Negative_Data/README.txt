FIRST POST-CANCELLATION NEGATIVE THUE–MORSE PRESSURE DEGREES

This research dataset records rigorous finite certificates for integer orders m=2,...,128.

Convention
Write P_m(t)=p_m(t/pi). The quantity N_m is the first even degree strictly greater than 2m whose coefficient in P_m is negative. Initial negative coefficients below 2m and the cancellation at 2m are excluded. Each N_m is certified by a negative upper bound at N_m and strictly positive lower bounds at every even degree from 2m+2 to N_m-2.

Contents
- DEGREE_TABLE.txt: all 127 values in a readable table
- FINITE_RESULTS.txt: exact counts, formula exceptions and resource measurements
- dataset_summary.json: the exact degree table, automatic formula comparisons, and measured resource/precision information
- first_negative_manifest.json: all 127 accepted cases, original source/trace hashes and certificate provenance
- compact/: exact outward-rounded dyadic intervals covering both independently propagated rational intervals
- first_negative_interval.cpp: directed response enclosures, including the cubic logarithm term
- audit_first_negative.cpp: an a posteriori projected-residual verification with fresh error propagation
- verify_dataset.py: fast verification of compact hashes, degree coverage, prefix signs and first-negative endpoints
- reproduce_dataset.py: compile both proof programs and reproduce selected cases
- METHOD.txt: the enclosure extension, sign criterion and exact rounding rules
- inputs/: the preceding enclosure report and its editable source
- validation/: exact comparison, rounding and final coverage receipts
- SHA256SUMS: package file provenance

Read a dyadic interval
Each row means
  lower_mantissa * 2^binary_exponent
      <= [t^degree] P_m(t)
      <= upper_mantissa * 2^binary_exponent.
All mantissas and exponents are integers. There are at most 96 mantissa bits. Use exact rational arithmetic; in Python, Fraction(2)**exponent avoids a floating-point conversion at negative exponents.

Quick verification
  python verify_dataset.py

This checks the delivered compact certificate structure and signs. It does not rerun the response-vector enclosure proof.

Independent mathematical replay
A C++17 compiler, GMP and zlib development libraries, and Python 3.11 or later are required. No package is installed automatically.
  python reproduce_dataset.py --m 2 20
  python reproduce_dataset.py --m 64
  python reproduce_dataset.py --all --workers 4

The full replay uses substantial runtime and several gigabytes of working traces. It generates both independent rational enclosures, checks the first-negative prefix, and verifies that the delivered dyadic interval contains both replayed rational intervals. Per-case timing measurements are recorded in dataset_summary.json; timings depend on the machine and concurrent load.

Scope
The finite values alone do not prove a limiting slope or an eventual floor formula. A separate analytical companion proves a slope and logarithmic correction; these finite certificates are supplementary to that proof. The proposed expression 2*(floor(10m/3)-1) is compared automatically against every accepted case, and all exceptions carry the original production and independent certificate hashes. In particular its failures at m=90 and m=93 are exact finite counterexamples.

A separate analytical theorem proves liminf N_m/m>=6.6 with an unspecified eventual cutoff. The finite table is not used to fill an unspecified complement. The exact equality N50=330 implies that any cutoff for positivity through degree 6.6m must be at least 51.

Provenance
The response induction is the method from The Full Pressure Positivity Range at Every Integer Order, 1 October 2026. This dataset extends it through degree 8m-2 and retains the exact cubic logarithm term. It also recomputes all error radii from projected residuals, without relying on the producer's claimed radii or inverse evaluation.

Full original rational intervals, closed response traces and fresh-radius traces are retained in the execution workspace. Their hashes are preserved in the manifest. They can be regenerated from the included source; raw traces are not included in this compact archive. Runtime fields and compressed-byte encodings can vary across implementations, while the integer arithmetic and the reproduced sign claims are checked directly.

This is unrefereed ordinary mathematics with directed integer arithmetic, not a formal proof or an asymptotic claim.

