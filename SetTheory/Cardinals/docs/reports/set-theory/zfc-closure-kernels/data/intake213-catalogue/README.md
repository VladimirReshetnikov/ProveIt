# Batch 213 catalogue build and review

The collection stays at 290 reports; the existing closure-kernel host has 187
numbered sources, written coverage 1–164 and 167–187, and pending 165/166 follow-ups.
The Write commit is `8a298fa5fbbc9d9d5db250c3671c9b26fe67cabb`.

[Final review](final-review.json) checks all 290 entries: the other 289 entries,
all report title/directory/main-file fields and category counts are unchanged.
The complete old source-archive and placement lists are exact prefixes; only the
eight arrivals and two parallel-placement references are appended. Inverting
all declared changes recovers the complete previous manifest exactly. The old
collection README is an exact prefix. The base article and its 50 labels remain
unchanged; the Write separately checked every host TeX file and all 734 labels.

The [two-pass build](build-result.json) produced 142 pages, sequential entries
1–290, correct page footers, embedded fonts and no diagnostics. The author
visually read pages [2](page-2.png), [123](page-123.png), [141](page-141.png) and
[142](page-142.png): no clipping or overlap. The final footer is 142.

The [gzip-JSON build records](build-records.json.gz) preserve exact raw logs,
standard output, extracted PDF text and finite records, with a
[member index](build-records-index.json). Decode each `content_base64` field to
recover the named bytes. These are our own LaTeX build records, not incoming
verification logs. No supplied code or proof compiler was run. The final PDF
is the collection's canonical `manifest.pdf`; auxiliary TeX files are excluded.

`prepare.py` and `validate.py` preserve the actual source-update/history checks
and their original scratch paths. They are historical tools, not blind replay
commands against a later catalogue. `build_catalogue.py` is portable and pins
the exact final source before running two bounded `pdflatex` invocations with
shell escape disabled. From this repository, a fresh scratch replay is:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake213-catalogue/build_catalogue.py --repo . --out /tmp/catalogue213-replay
```

The output directory must not exist. The builder leaves the canonical PDF
alone. No additional formal status is conferred by this catalogue build;
selected phase-twelve proof work and the other proposals retain the precise
boundaries of `intake-213.md`.
