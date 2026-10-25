# A direct quartic in 314 unrestricted integers

The equation is the sum of squares of all 204 literal residuals in
`equation.json`, with its 314 coordinates independently ranging over Z.
`expanded_polynomial.json` supplies every collected coefficient. The exact
degree is 4, support is 5,721 monomials, and coefficient height is 128,446.

The ordinary theorem, composed with the specifically retained C222/ZF/ZFC
refutation calibration, is that absence of an integer zero is equivalent
in ZFC to Con(ZFC). This does not prove consistency, global optimality, or
an end-to-end new proof-assistant certification.

The matched package 131 parent has 324 integer variables, 208 residuals,
5,808 monomials, the same degree and the same coefficient height. Its literal
equation and exact source are retained, so the comparison is independently
recomputed rather than copied from a prose table.

## Mathematical change

Reuse the already required syntax-label Pell pair as a semantic cap, then
replace the independently chosen CRT comparison center by the fixed polynomial

    D = A + (1-A) H^2.

The norm identity makes D congruent to A modulo H and to 1 modulo 4C.
An even square frame permits an odd auxiliary quotient for every semantic
index, and a signed-base proof allows the main scale guard to be removed.
All new unbounded steps and the full witness order are in `proof.md` and
the includable report section `section.tex`.

The center identity is the new local idea. The semantic-anchor construction,
odd quotient at even indices, signed-base theory, Pell growth, Horn factoring,
monic elimination and underlying logical calibration have identified earlier
sources. The package states the exact composition and measured endpoint;
it makes no worldwide-priority claim for those general techniques.

## Files

- `proof.md`, `section.tex`: complete new ordinary proof.
- `equation.json`, `expanded_polynomial.json`, `metrics.json`: normative endpoint.
- `residuals.tex`, `residuals.txt`: every residual; the TeX is parsed back exactly.
- `variables.tsv`: complete coordinate order and source names.
- `source.json`, `source_change.json`: changed semantic source and literal edit map.
- `projected.json`, `projection.json`, `translation.json`: all restoration maps.
- `baseline/`: accepted factored input, interfaces and literal 324-variable parent.
- `source_pins.json`: exact pinned repository paths, Git blob IDs and SHA-256s.
- `proofs/`: credited ordinary predecessor arguments and named Lean endpoint files.
- `code/`: rebuild, independent checks and document transcription.
- `check.json`, `optimized_check.json`, `replay.json`: recorded successful checks.
- `licenses/`: inherited license and notice texts.

## Reproduce offline

Python 3.10 or newer, standard library only. From this directory:

```sh
python3 -B code/check.py
python3 -B -O code/check.py
python3 -B code/check.py --rebuild
python3 -B code/print_equation.py --check
```

The independent checker imports no producer, optimizer or translation helper.
It verifies every changed source row, all fifteen pooled indices and the full
frame, 216 monic coordinate restorations, 94 absent free coordinates, all 62
integer translations and all 5,721 final coefficients. Three altered-artifact
controls must be rejected. `--rebuild` regenerates nine mathematical files
in a temporary directory and requires byte-identical results; it preserves
the delivered files. Use `--output /path/to/receipt.json` to write a receipt.

The rebuild deliberately starts at the pinned accepted factored input, rather
than recompiling every older C222/compiler or Lean dependency. Those ordinary
proof dependencies are retained and attributed in `proofs/INDEX.md`. The
formal interface files identify the exact named endpoints; their entire Lean
import closure is not bundled and no Lean execution is claimed. Historical
`source_commit` metadata inside inherited equation objects denotes their
original compiler provenance; the comparison snapshot and exact file pins
are given by `source_pins.json`.

Finite algebra checks are not consistency tests. The unbounded number theory
and proof-theoretic reduction are ordinary mathematical proofs, not assertions
inferred from sampling or file hashes.
