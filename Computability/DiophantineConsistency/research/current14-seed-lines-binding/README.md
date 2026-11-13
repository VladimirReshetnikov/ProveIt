# Decimal seed lines for the 14-variable equation

`SeedLines.lean` defines twelve explicit lists of decimal digits, preserving
the leading zero on line seven. The theorem `decimal_lines_eq_seed` proves
that every digit is below ten, the concatenated list has 715 digits, and its
ordinary left-to-right base-ten value is `DecimalMachine215.seed`. This is a
Lean theorem about the explicit digit lists and imported seed, without any
premise or `sorry`; the recorded `#print axioms` report says it has no axioms.
It does not interpret TeX or PDF inside Lean.

The separate `check_display.py` reads the digit-list literals in this Lean
file, the seed block of `equation.tex`, the source declaration of the existing
seed, and `pdftotext -raw` output for `equation.pdf`. It checks every digit,
line ordering and length, and the single leading zero, rejecting three
in-memory mutations. Its captured `display-observation.json` includes hashes
and the PDF-extraction hash. Optimized Python is explicitly rejected, and the
negative-control exit is recorded separately. This checker parses only these
specific source fragments; neither it nor the theorem establishes general TeX
or PDF semantics, or binds other page formulas.

The original bounded author run returned exit 0 in 4.1 seconds, with empty
stderr and no warnings or `sorryAx`. Its `observation.json` records before/after
hashes of the theorem source, Lean binary, original runner and directly
imported `DecimalMachine215.olean`. The byte-exact original runner is retained
as `run-captured.txt`, and its hash matches the recorded runner hash. A second
bounded author run using the new runner passed in 4.0 seconds with the same
axiom report and identical object bytes; its separate receipt is
`observations/second-author/observation.json`. Both runs used the same
inherited provider, so the second run is not an independent ancestry audit.
Two resource samples in each run saw at most one Lean process; the lowest
sampled available memory was 18,526,168 KiB. Sampling cannot rule out shorter
overlap or dips between checks. Each Lean process was capped at 2 GiB and
180 seconds, with an 8-GiB available-memory guard.

`run.py` requires a fresh `--attempt` name and refuses to overwrite its output
or receipt directory. It uses explicit guards, including rejection of
optimized Python; `refusal-observation.json` records a rejected reused attempt
and optimized invocation and confirms that both receipts and objects remained
unchanged. The selected imported object is inherited from the compact author
provider; the direct-input guards do not establish complete project, package,
dynamic-import or source-to-object ancestry, an independent replay, or an
iPRA endpoint replay. In particular, the external comparison to the current
`DecimalMachine215.lean` source does not authenticate that source's imported
object.

An initial attempt using `String.toNat?` did not elaborate under the kernel
reducer; its exact source and failed observation are retained as
`SeedLines-string-attempt.txt` and `attempt01.json`. The successful version
uses a simple list fold. The displayed recipe and other fixed-port bindings
retain their existing proof and transcription boundaries.

Reproduce from the repository root, while the recorded provider remains
available:

```sh
python3 Computability/DiophantineConsistency/research/current14-seed-lines-binding/run.py --attempt fresh-name
python3 Computability/DiophantineConsistency/research/current14-seed-lines-binding/check_display.py
```
