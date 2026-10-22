# Twelve positive variables for a fixed Diophantine Con(ZFC) encoding

## Results first

Relative to the reviewed candidates at repository commit
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`:

* **12 strictly positive variables**, one polynomial of **degree 1257**, with
  **139 binary operations (93 multiplications, 46 additions/subtractions)**.
  Its three-equation version uses 135 operations, with residual degrees
  7, 2 and 1248.
* **26 unrestricted integers**, one polynomial of **degree 2465**, with
  **192 binary operations (117 multiplications, 75 additions/subtractions)**.
* A materialized four-coefficient compiler tuple based on **943 Wang tiles**,
  with `B = 2^(5^10)`. Its four exact unsigned little-endian binary integers
  occupy 5,312,269 bytes before compression and **20,260 bytes as deterministic
  gzip payloads**. These are actual coefficient bytes, not just existence claims.
* Useful alternative tradeoffs include 27 integers / degree1116 / 136 operations;
  28 integers / degree258 / 128 operations; and 15 positive variables / degree44 /
  76 operations. The article lists additional reviewed tradeoffs.

Read **report/twelve_variable_con_zfc.pdf** for the complete mathematical
article, including exact bounded coefficient definitions, the radical-free norm,
proofs, the primary 139-gate straight-line program, limitations and further
research questions. Its editable TeX source and build helper are alongside it.

These statements depend on the explicitly pinned machine-calibration,
Pell and arithmetic/compiler theorems. They are ordinary mathematical arguments
with independent finite audits, **not an end-to-end proof-assistant certificate**.
They do not prove Con(ZFC), assert an actual halting computation of K215,
establish a globally optimal variable count, or beat the reviewed 67-operation
or 32-positive-variable quartic benchmarks. Circuit operations are not bit
complexity, and the huge constants are not charged as construction gates.

## One-command portable verification

Requirements: Python 3 with its standard library, no network and no packages.
From the extracted directory run:

    python3 -B verify_package.py

The verifier checks the release SHA-256 manifest, all 127 inert repository files
against both SHA-256 and Git blob hashes, then inflates and verifies the four
coefficient payloads. It checks every final literal circuit for closure, liveness,
operation counts and degrees at two finite-field specializations using the
**actual materialized coefficient residues**, checks the printed primary SLP
against its exact JSON, independently multiplies the four formal norm factors,
and invokes the explicitly identified newly authored mathematical/compiler and
integer checkers. It never imports or executes the received repository programs.
The finite-field tests supplement the included uniform degree proofs; they are
not the proof of the unbounded Diophantine equivalence.

The public verifier rejects optimized Python (`-O` or `PYTHONOPTIMIZE`) and
requires the release manifest. It copies the release into a fresh temporary
directory, runs all mutable checks there, deletes that temporary copy, and
confirms the original release remains byte-for-byte unchanged. You can safely
run it repeatedly. It prints the result; `RELEASE_CHECKS.json` preserves the
pre-release diagnostic receipt. `verify_worktree.py` is the internal mutable
implementation, not the public entry point.

## Exact binding and file map

**COEFFICIENT_BINDING.json is the authoritative complete tuple for every circuit
listed in FINAL_FORMS.json.** Aliases are:

    beta or Bm1 -> beta.bin
    K0 or Kconstant -> K.bin
    MC -> MC.bin
    MF -> MF_source.bin

The last alias is crucial: `MF_source = MF_native + B - 1`, not `MF_native`.
Never mix ports from different compiler backends. Older 5^11 and original
coefficient bindings in provenance notes describe alternatives, not the default
instantiation. Only the compact 5^10 payloads are shipped.

* `roots/`: the leading saturated 12-variable form and two earlier, now dominated,
  12-variable forms, plus their systems, proofs, exact JSON and checkers.
* `integers/`: the leading 26-integer form and lower-degree 27/28-integer
  alternatives, together with earlier dominated forms, proofs and exact checkers.
* `compiler/`: 943 literal tiles, directed-signal language, helical and population
  compiler proofs, compact finite support, bounded formulas and exact payloads.
  `COMPACT_REPRODUCE.md` explains complete coefficient regeneration.
* `arithmetic/`: grouped polynomial schedules, proof notes and a portable emitter.
  Its inert parent input is included. `PORTABILITY_TRANSFORMS.json` records the
  input-path-only adaptation, which preserves the emitted circuit contents.
* `audit/`: separately authored mathematical and finite-code audits.
* `review/`: repository review, source pins and inert source texts.
* `root/ADDITIONAL_MATHEMATICAL_REVIEW.md`: additional mathematical review.
* `SHA256SUMS.txt`: exact checksums for every packaged file except this manifest.

For optional regeneration, first work on a separate copy and follow
`compiler/COMPACT_REPRODUCE.md` to inflate the coefficients. All integer forms
can then be rebuilt and checked with:

    python3 -B integers/replay_integer_forms.py

The default uses only the shipped compact primary backend. Do not use the
optional `--all-backends` flag without separately materializing the fallback.
Some optional exploratory scripts outside the top-level portable verifier use
NumPy; neither installing NumPy nor running those scripts is needed to verify
this release. The TeX build requires an existing compatible TeX installation;
`bash report/build_report.sh` uses installed pdfTeX resources and local caches,
without installing software or enabling shell escape.
