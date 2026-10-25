# Unsealed prospective sequential command plan

No command below is released by this document. Two FULL final static
approvals must cover every new/adopted application, source/TeX/proof,
guard, renderer and runtime dependency; ROOT must separately release each
stage against that exact HOLD. Stage A may not imply stage B permission.
Fresh commands and final inert result/data closure require later separate
releases. Run from the repository root with a reviewed Python3 runtime.
No native compiler, machine, optimizer, search, Lean or other application
is part of this plan. All *.tex are included in the held inventory.

Before the first command verify the exact HOLD, all pinned inputs/whole
parents, all thirteen candidate output paths absent, and all48 first/fresh
receipt/stdout/stderr paths absent. Before each stage/command verify its
fixed external capture paths remain absent and previous frozen bytes
unchanged. Each command has a complete JSON receipt identical to its
complete stdout; preserve stderr even when empty and observe the real
process exit code. Stop immediately on the first nonzero exit or missing
receipt. Preserve the whole failed snapshot and all output/captures; no
repair, retry, reseal, render or next command follows without disposition.

Stage A, first coherent tuple/source materialization and full source checks:

```sh
python Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/build.py --output /tmp/complemented47-page-build.json > /tmp/complemented47-page-build.stdout 2> /tmp/complemented47-page-build.stderr
python Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/FRONT_AUDIT.py --source-only --output /tmp/complemented47-page-source-audit.json > /tmp/complemented47-page-source-audit.stdout 2> /tmp/complemented47-page-source-audit.stderr
python -O Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/FRONT_AUDIT.py --source-only --output /tmp/complemented47-page-source-audit-optimized.json > /tmp/complemented47-page-source-audit-optimized.stdout 2> /tmp/complemented47-page-source-audit-optimized.stderr
python Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/build.py --check --output /tmp/complemented47-page-build-check.json > /tmp/complemented47-page-build-check.stdout 2> /tmp/complemented47-page-build-check.stderr
python -O Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/build.py --check --output /tmp/complemented47-page-build-check-optimized.json > /tmp/complemented47-page-build-check-optimized.stdout 2> /tmp/complemented47-page-build-check-optimized.stderr
```

Only these eight candidate source outputs are permitted:

    coefficients/beta.bin.gz
    coefficients/K.bin.gz
    coefficients/MC.bin.gz
    coefficients/MF_source.bin.gz
    polynomial.json
    COEFFICIENT_BINDING.json
    CALIBRATION_BINDING.json
    SOURCE_INDEX.json

SOURCE_INDEX binds all seven other payloads, reviewed producer and frozen
pins. Whole-byte source rebuilds are pure comparisons. No measured raw
hash, successful audit or endpoint exists in this prepared folder now.

After stage A succeeds and ROOT separately releases stage B, render once,
audit the actual full PDF in normal/O and compare both pure rerenders:

```sh
python Computability/DiophantineConsistency/tools/render_compact66_complemented47_page.py --render --output /tmp/complemented47-page-render.json > /tmp/complemented47-page-render.stdout 2> /tmp/complemented47-page-render.stderr
python Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/FRONT_AUDIT.py --output /tmp/complemented47-page-audit.json > /tmp/complemented47-page-audit.stdout 2> /tmp/complemented47-page-audit.stderr
python -O Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/FRONT_AUDIT.py --output /tmp/complemented47-page-audit-optimized.json > /tmp/complemented47-page-audit-optimized.stdout 2> /tmp/complemented47-page-audit-optimized.stderr
python Computability/DiophantineConsistency/tools/render_compact66_complemented47_page.py --check --output /tmp/complemented47-page-rerender.json > /tmp/complemented47-page-rerender.stdout 2> /tmp/complemented47-page-rerender.stderr
python -O Computability/DiophantineConsistency/tools/render_compact66_complemented47_page.py --check --output /tmp/complemented47-page-rerender-optimized.json > /tmp/complemented47-page-rerender-optimized.stdout 2> /tmp/complemented47-page-rerender-optimized.stderr
```

The only five additional candidate outputs are equation.pdf,equation.txt,
RENDER.txt,TEX_DIAGNOSTICS.txt,RENDER_DATA.json. The renderer uses only
pdflatex,pdfinfo,pdftotext, with pinned executable bytes and a private
TemporaryDirectory. It fixes SOURCE_DATE_EPOCH=946684800,TZ=UTC and
FORCE_SOURCE_DATE=1, disables shell escape, restricts input/output, retains
complete normalized logs and rejects all overfull boxes. It compares all
five bytestrings on --check. Full actual PDF glyph audits and independent
visual inspection remain separate from these renderer-only checks.

Six fresh ROOT checks, separately released, must produce same-mode receipts,
stdout and stderr byte-identical to their first check captures. No receipt
contains its pathname, time or scratch directory:

```sh
python Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/build.py --check --output /tmp/complemented47-page-root-build-check.json > /tmp/complemented47-page-root-build-check.stdout 2> /tmp/complemented47-page-root-build-check.stderr
python -O Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/build.py --check --output /tmp/complemented47-page-root-build-check-optimized.json > /tmp/complemented47-page-root-build-check-optimized.stdout 2> /tmp/complemented47-page-root-build-check-optimized.stderr
python Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/FRONT_AUDIT.py --output /tmp/complemented47-page-root-audit.json > /tmp/complemented47-page-root-audit.stdout 2> /tmp/complemented47-page-root-audit.stderr
python -O Computability/DiophantineConsistency/candidates/one-page-compact66-complemented47/FRONT_AUDIT.py --output /tmp/complemented47-page-root-audit-optimized.json > /tmp/complemented47-page-root-audit-optimized.stdout 2> /tmp/complemented47-page-root-audit-optimized.stderr
python Computability/DiophantineConsistency/tools/render_compact66_complemented47_page.py --check --output /tmp/complemented47-page-root-rerender.json > /tmp/complemented47-page-root-rerender.stdout 2> /tmp/complemented47-page-root-rerender.stderr
python -O Computability/DiophantineConsistency/tools/render_compact66_complemented47_page.py --check --output /tmp/complemented47-page-root-rerender-optimized.json > /tmp/complemented47-page-root-rerender-optimized.stdout 2> /tmp/complemented47-page-root-rerender-optimized.stderr
```

The held scripts allow only these fixed receipt names, require absence
before any work and revalidate before exclusive write. ROOT observes all
actual exits and retains every complete capture. Final source/data/results
and whole manifest closure need a later inert-only release. Main promotion
requires complete ordinary evidence review, independent actual visual
reviews and ROOT acceptance; it does not follow merely from a program's
PASS string. All historical failed or unresolved contracts remain retained.
