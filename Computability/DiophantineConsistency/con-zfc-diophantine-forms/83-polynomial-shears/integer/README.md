# Double centering and transport projection

Five explicit fixed-coefficient sum-of-squares equations over unrestricted
integers, with variable/degree pairs **23/10, 21/16, 20/20, 19/32, 18/88**.
The respective numbers of residuals are **11, 9, 8, 7, 6**.

The zero sets are related to the literal incoming Joint Guards parents by
integral polynomial bijections. Composing with the parents' ordinary native,
Pell and proof-calibration theorems yields a ZFC-formalizable proof that
each equation's absence of integer solutions is equivalent to Con(ZFC).
No new end-to-end proof-assistant certificate, global minimality result or
external priority claim is made.

Read `PROOF.md` for the complete 23-variable and 18-variable equations,
inverse coordinate maps, all exact degree certificates, comparison against
the newest incoming packages and further research questions. `section.tex`
is a report-ready LaTeX section. Every variable and every fixed coefficient
is listed in the corresponding `forms/*.json` packet; explanatory registers
are fully inlined in the actual residuals.

## Offline use

Requires Python 3 and SymPy 1.14:

```sh
python3 build.py
python3 check.py
```

The six authentic source-34/determinant coefficient payloads are included in
`coefficients/`. They total 615,883 uncompressed bytes, specified as unsigned
little-endian byte strings. `BINDING.json` states their complete binding;
the shifted MF convention is preserved. The compressed bytes make the
polynomial specification self-contained without an online lookup.

`SOURCE_PINS.json` records exact source hashes. The copied parent packets and
source proofs are preserved under `upstream/`, with their inherited license
and notice files. New code imports no upstream executable generator.

The polynomial improvements are compositional: the double root translation
was present in incoming Budget and Centering; the monic transport pivot
was present in incoming Round11. Their applications here to the newer
Joint Guards systems were absent from the inspected packets. All unbounded
calibration obligations remain clearly inherited; finite checks only
establish the exact algebra, data binding and transcription facts stated.

