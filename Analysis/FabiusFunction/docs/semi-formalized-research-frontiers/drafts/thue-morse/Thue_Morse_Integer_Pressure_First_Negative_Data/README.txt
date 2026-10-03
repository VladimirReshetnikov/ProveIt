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
- inputs/: the preceding enclosure report and its editable source (not filed; see the editorial amendments below)
- validation/: exact comparison, rounding and final coverage receipts
- SHA256SUMS: package file provenance (retired on filing; not in the repository)

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


Editorial amendments (ProveIt, 2026-10-01)
------------------------------------------

Made in the editorial pass after batch 72 of docs/incoming/ (see
docs/incoming/README.md). This is the thirteenth of thirteen packages of one
series, filed beside the manuscript they continue,
../Thue_Morse_Integer_Pressure/, in logical order: the positivity series
../Thue_Morse_Integer_Pressure_First_Positive/,
../Thue_Morse_Integer_Pressure_Higher_Positive/,
../Thue_Morse_Integer_Pressure_Positive_Triangle/,
../Thue_Morse_Integer_Pressure_Feedback_Boundary/,
../Thue_Morse_Integer_Pressure_Beyond_Boundary/,
../Thue_Morse_Integer_Pressure_Linear_Region/,
../Thue_Morse_Integer_Pressure_Full_Range/, and the sign series, which
imports the full-range theorem,
../Thue_Morse_Integer_Pressure_Sign_Changes/,
../Thue_Morse_Integer_Pressure_Sign_Densities/,
../Thue_Morse_Integer_Pressure_Negative_Bound/,
../Thue_Morse_Integer_Pressure_First_Negative/,
../Thue_Morse_Integer_Pressure_Cluster_Asymptotics/, with the dataset
../Thue_Morse_Integer_Pressure_First_Negative_Data/. An earlier version of
../Thue_Morse_Integer_Pressure_Full_Range/, The Full Pressure Positivity
Range for Large Integer Orders (m >= 4096), was superseded by it and not
filed; neither was a duplicate archive.

- This package has no article; this section is its series map. The method
  source named under "Provenance", The Full Pressure Positivity Range at
  Every Integer Order, is ../Thue_Morse_Integer_Pressure_Full_Range/; the
  "separate analytical companion" proving a slope and logarithmic correction
  is ../Thue_Morse_Integer_Pressure_First_Negative/; the "separate
  analytical theorem" liminf N_m/m >= 6.6 is
  ../Thue_Morse_Integer_Pressure_Negative_Bound/. The inputs/ copies (that
  article's PDF and source, and two of its C++ programs, which are
  finite/producer_v1.cpp and finite/audit_residual_enclosures.cpp there)
  were not filed; no program of this package reads them. The submitted
  checksum ledger was retired.
- Use on filing. The interval archives of
  ../Thue_Morse_Integer_Pressure_Full_Range/ (its finite proof for
  2 <= m <= 111) were not delivered; the compact intervals here certify the
  same range again: checked on filing, every even degree strictly between 2m
  and 6m has a strictly positive lower endpoint for 2 <= m <= 128, and for
  m = 24 the intervals enclose all 48 exact values of that package's
  finite/exact_reference_m024.json (degrees 48 to 142). N_m = 6m exactly
  for m = 2, 3, 4; the m = 2 interval at degree 12 contains
  -35360872/93555. The values for m <= 20 equal the table of
  ../Thue_Morse_Integer_Pressure_Sign_Changes/, those for m <= 14 the
  table of ../Thue_Morse_Integer_Pressure_Feedback_Boundary/; the
  degree-4m intervals are positive for every m <= 128, which certifies the
  pressure statement of ../Thue_Morse_Integer_Pressure_Feedback_Boundary/
  for its finite range, whose traces were not delivered. With gamma and
  Lambda of ../Thue_Morse_Integer_Pressure_First_Negative/ evaluated
  numerically, N_m - (gamma m - log log(2m)/Lambda) lies in (-1.75, 0.36)
  for every m here.
- verify_dataset.py writes nothing; a rerun on a copy (2026-10-01, Python
  3.14.4, standard library) passed and printed exactly the record
  validation/compact_verification.json. reproduce_dataset.py (C++, GMP,
  zlib; not run) writes replay/ here. The scripts under provenance/
  overwrite the records first_negative_manifest.json,
  dataset_summary.json, compact/ and files under validation/, and need
  the multi-GB working traces that were not shipped: kept as delivered; run
  them only on a copy. Commands say python; use py on the ProveIt machine.
- README.txt: the inputs/ and ledger lines under "Contents", and this
  section.
