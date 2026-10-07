# Report212 reproducibility package

This package supports the finite computations in Report212. It contains authored
source, a complete small fixture, exact table values, and scoped verification
records. It contains no third-party papers or raw large-row output.

## Requirements and two distinct workflows

Use Python 3.11 or later (standard library only). The full workflow also needs a
C++17 compiler and the GMP development libraries (`gmpxx` and `gmp`). No dependency
is downloaded or installed by these scripts. Invoke from any working directory:

```sh
sh reproduce.sh quick
sh reproduce.sh regenerate --max-k 256
```

`quick` reads the complete stored fixture through k=32. It directly enumerates
walks through k=8, independently generates the recurrence in Python through k=16,
checks the stored fixture, and runs the deliberate-corruption harness. **It does
not regenerate the table through k=256 or claim to validate unstored higher rows.**

`regenerate` compiles `code/moments.cpp`, freshly produces every root-departure row
and moment through k=256, repeats both verifiers in normal and optimized Python,
then regenerates and exactly compares all public table values. It also checks the
complete k<=32 fixture prefix and full k<=256 output digests. This is a fresh
execution of the C++ algorithm, not an independent higher-row algorithm.

An optional larger run is available:

```sh
sh reproduce.sh regenerate --max-k 512 --work-dir build/optional512
```

It generates all rows through512, checks their consistency, compares the complete
256 prefix and public table, and emits an additional table including512. That
optional512 workflow is supplied for the reader; this package's fresh public
replay evidence stops at256. No raw512 output is distributed. Generation at512
requires substantially more time and disk space than the fixture replay.

`CXX` selects the C++ compiler and `PYTHON` selects Python. `--work-dir PATH`
selects a new, nonexistent output directory, either under `build/` or outside the
source package. Existing directories and protected source destinations are rejected
before output writes. Choose a new directory for each replay. Work output is
disposable; distributed inputs are not overwritten. The C++ recurrence and loop
ordering are unchanged from the checkpoint; argument parsing and file I/O were
hardened. The generator accepts exactly one integer in 1..512 and checks opening,
writing, flushing, and closing both output streams.

## What is checked, and how independently?

- `independent_audit_checks.py` creates normalized walks directly by following an
  existing adjacent edge or discovering one fresh vertex, closing at vertex zero.
  It enumerates through k=8 without a recurrence and checks both the first-edge
  and partition/cut recurrences, weighted rotation, and exact double-hub counting.
  It checks 36 first-edge, 36 partition/cut, 20 rotation, and 20 double-hub cases
- `diagnostics.py` separately implements the first-edge recurrence in Python
  through k=16 and compares every row with the input data. The pinned reference
  totals through16 are a further reference check, not another fresh generator
- Above16, complete key sets, duplicate exclusion, nonnegative integer entries,
  row sums, three boundary identities, finite union integrality/range, and the
  finite ratio decrease are consistency checks. They do not establish asymptotics
- The C++/GMP execution supplies exact complete rows through the requested range
- `verify_guard_failures.py` runs 44 deliberate failures: nine enumerative audit
  categories, six diagnostic categories, five malformed-data cases, exact
  table comparison, and duplicate JSON-key rejection, each in normal Python and `-O`. It requires a nonzero exit,
  the intended named failure, and no newly written success artifact. An AST scan
  rejects assertion statements in all Python files. Successful verifier results
  are also required to be byte-identical under normal and optimized Python
- `verify_cli_guards.py` adds 15 negative probes for bad generator arguments,
  stream opening and actual write failure, and replay output-directory safety,
  plus a successful exact k=2 generation. Full replay runs these in normal and
  optimized Python. The write-failure probe uses Unix file-size limits

## Exact tables and the unavailable k=16 union

`tables/table_values.json` retains exact numerator/denominator pairs, exact
moments, Bell values, integer union and double-hub counts, and rounded displays.
`tables/numeric_table.tsv` is the convenient public table. The two generated TeX
fragments use `booktabs` and `amsmath` and are ready for the report's tables.
Here B always denotes B_(k+1), and ln is the natural logarithm.

The quarter-power window uses S=floor(k^(1/4)); the other uses
S=ceil((ln k)^2). The latter integer is computed at 60 and 100 decimal digits and
required to agree. Counts and weighted sums use integers or exact `Fraction`s;
`Decimal` is used only for this threshold choice and final display rounding.

For k=16, the log-squared choice gives S=8 and L=k-S=8. The two-hub formula requires
L>k/2, so its union and complement entries are explicitly N/A. They are not zero.
The middle interval is empty and its displayed R/B is zero; this is not an
asymptotic tail conclusion. At every displayed valid threshold, the union uses
the exact two-hub correction, rather than the weighted rooted count alone.

To regenerate only the public table from an already generated complete256 run:

```sh
python3 code/make_tables.py --data-dir build/regeneration256/regenerated256 \
  --expected-max 256 --compare tables/table_values.json \
  --output-dir build/recomputed_tables
```

The comparison is exact JSON equality, including the unrounded fractions and
integers. It is not a tolerance check of rounded printed numbers.

## Included records and provenance

`CODE_INVENTORY.txt` lists the reproducibility files intended for distribution.
`verification/package_metadata.json` records source provenance, exact scope,
fixture size, and successful fresh256 checks. The other verification JSON files
record actual runs; none substitutes for the scripts. Build directories, Python
bytecode, binaries, complete256/512 raw outputs, and local logs are excluded.

The source checkpoint was dated 4 October 2026 and its SHA256SUMS file had digest
`7995d901ebf29fba97abe42df42c9c89025805a0806f318faa7f694ad5dc15fc`.
Only the authored recurrence source (with CLI/I/O hardening), small exact rows,
and reference totals were carried forward. The full source checkpoint is not redistributed in this public package. Finite calculations do not prove the full equivalent
M_(2k) ~ 2 B_(k+1), which remains outside the result established by this report.
