# Independent complete-page review: Start-marker4177

Reviewer: `/root/controller_certificate`, 2026-10-25. Result: **PASS; no
blocking source, port, circuit or rendered-page finding.** The complete
ordinary proof and finite verifier have a separate review in
`start-marker4177-independent-peer.md`. This report covers the full new
builder, TeX, 66-row DAG, source manifest, ports, negative controls and
actual rendered page, not merely an excerpt or a layout mockup.

## Bound source files

All paths in this table are beneath
`Computability/DiophantineConsistency/candidates/one-page-start-marker4177`.

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `build.py` | 13192 | `70b0722ef4453d6bf6cca1deb7fbb58ad831e7c93abeaa734355d1b61e37e956` |
| `equation.tex` | 5072 | `831279d10a76e85a4366a85e18c8efec4afa9e98a5c9990369cbaa8e686bd4f9` |
| `polynomial.json` | 6754 | `3cac1cc5e1efd9167cc74ae36546fdf76d8119cb6f94a66247a5d863840e8333` |
| `BUILD_AUDIT.json` | 1391 | `bf606cc2a2af61f8071a86db2e0ca0bc05c570b8e0a505eb88d1688520faf950` |
| `SOURCE_MANIFEST.json` | 1772 | `fd18887323eb5edd5e53b88734332134784b1b10ce7ff8204a8a16e909de3e06` |
| `README.md` | 4248 | `cc1423625e6887561d0a6696dd9ca64a53053f8bd77967ac33151cc553e5d396` |

The builder authenticates the exact zero-weight6007 parent TeX
`8a1ef160bddb5f0520623546362fc9fe41c749d85dbf4937600aac01a92397d8`
and whole parent DAG
`cc67c35f522bd22ddc4265209860d681146da62d42cdc207c3266b697c5b42a8`.
Its six checked single-occurrence replacements move the base, clauses,
marker and padding, and replace the selector-count block by one monomial.
The complete front, all tile families, closed decoder, 436-character seed,
footer, type sizes and layout commands are preserved.

I read the whole builder before execution. Its finite subprocess and
import target are authenticated against verifier
`569d9da678dea56d1b610b2e1c436686e361b19ec66ad6cd2683c59344441067`,
certificate `b3e1368f3918e8a3371e11aed9746c2369e8770c9aaa2496b4cf797f3b85b8f8`
and proof `1db36f130e31087e751b2c83f9988ba4dda34e4f7525d5c9514766238858386e`.
All three were independently read/reviewed before these runs.

## Full source and integer checks

Both commands returned PASS in their default read-only mode:

```text
python3 -B Computability/DiophantineConsistency/candidates/one-page-start-marker4177/build.py
python3 -B -O Computability/DiophantineConsistency/candidates/one-page-start-marker4177/build.py
```

The optimized mode propagates to the finite subprocess. Explicit exception
guards remain enabled. Only `--build` writes artifacts; neither run above
used that option. All generated source/port bytes match their stored files.

The printed Psi recipes expand to all3297 weighted coefficients and all980
physical positions. The marker term `t^34*(2-t)*x^1048` contributes to
Psi at one and vanishes at two. The source-derived MC therefore retains
the zero-weight physical marker. The exact printed beta, K, MC and MF
expand to the same four whole integers as the finite certificate, including
the full zero tail and the once-shifted source mask. Minimal unsigned
byte lengths are24540,24599,24540,24540, totaling98219. Their raw hashes
are recorded in the accompanying proof/certificate review; every gzip
port and its digest is reproduced and byte-compared by the builder.

The corruption control deletes the actual TeX substring
`&+t^{34}(2-t)x^{1048}`. Re-expansion leaves every weighted coefficient
unchanged but removes physical position1048. `validate_printed` then
raises exactly `Entire physical support, including zero-weight flag`.
The audit records `actual_TeX_flag_deletion_rejected=true`; separate
controls reject a restored weighted marker and Psi-one used in weighted
Phi. These are specific source corruptions, not a claim to parse arbitrary
TeX or to exhaust all possible corruptions.

The entire inherited free-port DAG remains38 multiplications,15 additions
and13 subtractions. Every one of its66 rows, fifteen strictly positive
input variables and four fixed ports is live. Directly reading each row
against the displayed polynomial abbreviations found no mismatch. The
new specialization is a different integer polynomial; the retained
nonzero leading coefficient `8*beta^92` proves the same exact degree157.
The builder verifies graph identity and does not claim a fresh symbolic
degree calculation or native compiler execution.

## Actual full-page rendering

ROOT rendered the reviewed candidate source to
`/tmp/diophantine-start-marker4177/equation.pdf`. I independently inspected
the complete corresponding PNG through `view_image`; it was not cropped.
The original raster is1391 by1800 pixels, shown by the tool at1376 by1780.
The full page shows all unknowns, abbreviations, equation, four fixed
integer recipes, Phi/Psi, tile-table rows, closed action decoder, alphabet,
all436 seed characters including the final `8P`, and the proof-status
footer. The changed marker term is visible. There is no text clipping,
column overlap or omitted bottom content. The source retains9pt body and
7.7pt seed/footer settings.

| Actual artifact | Bytes | SHA256 |
| --- | ---: | --- |
| `equation.pdf` | 159631 | `6b827d3f52320a726fd4ebeb27ea6fdbba820d178279e38244ca8a2531a4d3f7` |
| `equation.png` | 440215 | `07dab06fd0b17d22e8380b048ea94f267074791f83b2e2569cc7f98380007ad0` |
| `equation.txt` | 7933 | `7ab7b4e758760853f479790f945d98a03d7418b3c211e290c2d4e4c93e74c749` |

`pdfinfo` reports one unencrypted Letter page,612 by792 points, PDF1.5.
The log identifies the actual candidate source and has no overfull or
underfull boxes. It does retain the predecessor's3.84999pt font-size
substitution warnings; this is not a warning-free compilation claim.

The exact TeX has5072 characters,4728 excluding whitespace, compared with
5085 and4741 for zero-weight6007:13 fewer under either count. Extracted
PDF text has7766 Unicode characters and2699 nonwhitespace characters,
seven fewer nonwhitespace characters than the parent's2706. The PDF is
5 bytes smaller than the parent's159636. These measurements describe
the complete artifact with fixed data and fonts intact; the substantial
integer saving43007 bytes is a separate size measure.

The proof author is `/root/complemented47_review`; the finite verifier
author is `/root/circuit_reduction`; ROOT authored the page builder and
produced the actual rendering. This reviewer inspected all bound inputs,
reran read-only checks and independently viewed the full image. No source,
port or accepted predecessor was edited in this review. No Lean,
native-compiler or end-to-end internal-ZFC replay, actual unsolvability,
consistency decision or global minimum is asserted.
