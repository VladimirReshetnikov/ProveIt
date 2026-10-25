# ROOT release of fresh compact66 checks and actual visual reviews

All ten separately released commands pass on their first attempts.
ROOT inspected the full source result and PDF result, all ten complete
JSON/stdout pairs and all ten empty stderr files. Both audit mode pairs
differ only in their optimization flag. Both pure rerenders reproduce
every one of the five artifacts. All184 whole held/closure input files
remain unchanged; the candidate contains exactly its20 held files plus
the nine released outputs. The extended pre-replay snapshot binds193
whole files at `/tmp/compact66-root-pre-replay-snapshot.json`.

The actual PDF is159875 bytes, SHA
`25458f58d4af6887eaf6cfc379dee0838e5aa867596268068f59da961f8f45bd`.
It has one Letter page,9-point body,7.7-point seed, no overfull boxes and
2801 nonwhite extracted characters versus2885 in the accepted grouped
page. Both full actual PDF glyph comparisons pass, including the entire
new recipe, full seed/alphabet and footer. The ordinary equation and all
295388 raw coefficient bytes are identical.

ROOT separately releases these six read-only fresh commands from the
repository root, retaining full JSON/stdout/stderr at the matching stems:

```sh
python -B Computability/DiophantineConsistency/candidates/one-page-compact66/build.py --check --output /tmp/compact66-root-build-check.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-compact66/build.py --check --output /tmp/compact66-root-build-check-optimized.json
python -B Computability/DiophantineConsistency/candidates/one-page-compact66/FRONT_AUDIT.py --output /tmp/compact66-root-audit.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-compact66/FRONT_AUDIT.py --output /tmp/compact66-root-audit-optimized.json
python -B Computability/DiophantineConsistency/tools/render_compact66_page.py --check --output /tmp/compact66-root-rerender.json
python -B -O Computability/DiophantineConsistency/tools/render_compact66_page.py --check --output /tmp/compact66-root-rerender-optimized.json
```

These independent reads have separate external receipts and scratch
directories and may run concurrently. Stop dependent work on any
failure. All twelve full JSON/stdout strings and six stderr files must
equal their first-run counterparts exactly; all193 snapshot files must
remain byte-identical. There is no repair, retry, search or new code
release.

ROOT also releases two independent actual visual inspections of the
exact PDF above. Use read-only pdfinfo/pdffonts/pdftotext and scratch
pdftoppm views outside the repository; inspect a whole page and enlarged
details as needed. ROOT and peer must actually view the PDF-derived
images for glyph clarity, table/column fit, seed case, clipping, overlap
and footer legibility, and write only separate outside visual records
under reviews/one-page-compact66-visual-{root,peer}.{md,json}. Source or
proxy counters cannot substitute for actual viewing. Keep the candidate
and maintained page unchanged.

Final metadata/sealing and maintained-page promotion remain separate
decisions after actual fresh-check and visual outcomes. Lean remains
paused; no native calibration or consistency assertion is released.
