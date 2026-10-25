# ROOT release of the exact grouped66 ten-command pipeline

ROOT explicitly releases the ten commands below after reading both full
final static PASS records committed in14e3f3d3d1. This release is separate
from those approvals and precedes the first candidate import or execution.
The exact approved HOLD is `25f4095d584e5021d67f93783706143433e3367e62f523aa432463126a77f2a3`;
SOURCE_PINS is `c502e8e4fad4143e064a03d9226c8ad5ba7e445a68f40eb955250ba3094ae0df`.
All16 local held payloads and the external renderer remain frozen.

The two full approvals have no remaining findings:

- `one-page-grouped66-static-final-root.md`: `6f071a5c38847a76d96911dd6694feb12574f081406d50cfc51804980f0b40ae`.
- `one-page-grouped66-static-final-root.json`: `06cf28784ab60751b76359f83036e426fc39bcc92c6fdafa9c71efa8606121d3`.
- `one-page-grouped66-static-final-peer.md`: `0ae8a976d522f8990fd4808625f4c28d84379b1004899a367166dc808f4abdd4`.
- `one-page-grouped66-static-final-peer.json`: `47d6795ebd03864e92d72ea9857d3069897bef376b69e10974b82b823a8a4b50`.

Run from the repository root, strictly in this order. Keep every complete
stdout and stderr externally next to its receipt using the same stem plus
`.stdout` and `.stderr`. A nonzero exit or tool/application failure stops
all dependent commands immediately; do not edit, retry or advance past a
failure without reviewing and re-freezing any substantive correction.

```sh
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/build.py --output /tmp/grouped66-build.json
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --source-only --output /tmp/grouped66-source-audit.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --source-only --output /tmp/grouped66-source-audit-optimized.json
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/build.py --check --output /tmp/grouped66-build-check.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-grouped66/build.py --check --output /tmp/grouped66-build-check-optimized.json
python -B Computability/DiophantineConsistency/tools/render_grouped66_page.py --render --output /tmp/grouped66-render.json
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --output /tmp/grouped66-audit.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --output /tmp/grouped66-audit-optimized.json
python -B Computability/DiophantineConsistency/tools/render_grouped66_page.py --check --output /tmp/grouped66-rerender.json
python -B -O Computability/DiophantineConsistency/tools/render_grouped66_page.py --check --output /tmp/grouped66-rerender-optimized.json
```

The producer may materialize only the four named source files; the renderer
may materialize only its five declared PDF/text/log/data files. No held
source, TeX, proof, seed, parent, maintained page or paused Lean file may
change. No compiler/search/Lean execution, optional variant, final metadata
or final manifest is released. JSON receipts and full stdout/stderr remain
external until root reviews them. A PASS is evidence only after the actual
command exits successfully and its complete record is inspected.

After all ten pass, ROOT must separately authorize six fresh independent
normal/optimized source checks, full audits and pure rerenders; compare all
twelve JSON/stdout byte strings and snapshot every immutable input. Two
actual visual reviews and separately authorized final metadata/inventory
closure precede acceptance or promotion. No success, measured size, fit,
visual approval or maintained equation.pdf update is claimed by this release.
