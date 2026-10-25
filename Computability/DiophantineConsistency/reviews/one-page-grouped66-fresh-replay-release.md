# ROOT release of fresh replay and actual visual review

All ten exact r2 commands released in c0cef8a8be exited0. Every full JSON
equals its complete stdout and every stderr is empty. The normal/optimized
source and full PDF audits passed all60 negatives/11 valid cases, plus the
actual delimiter/fixture checks. Both pure rerenders reproduced all five
render artifacts. The whole actual PDF has2885 nonwhite characters against
3025 in its accepted parent, one Letter page and zero overfull diagnostics.
No main-page promotion or final metadata has occurred.

ROOT separately releases the six fresh commands below, in this exact order
from the repository root, stopping on the first failure. Keep complete JSON,
stdout and stderr externally at their respective stems. No source edit,
compiler, search or Lean operation is released. Each command is a fresh
process using the exact frozen core; compare every resulting JSON and
stdout byte with its corresponding successful r2 record.

```sh
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/build.py --check --output /tmp/grouped66-r2-root-build-check.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-grouped66/build.py --check --output /tmp/grouped66-r2-root-build-check-optimized.json
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --output /tmp/grouped66-r2-root-audit.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --output /tmp/grouped66-r2-root-audit-optimized.json
python -B Computability/DiophantineConsistency/tools/render_grouped66_page.py --check --output /tmp/grouped66-r2-root-rerender.json
python -B -O Computability/DiophantineConsistency/tools/render_grouped66_page.py --check --output /tmp/grouped66-r2-root-rerender-optimized.json
```

The exact pre-replay snapshot is saved externally at
`/tmp/grouped66-r2-pre-replay-snapshot.json`, containing all26 current
candidate files and all125 distinct held/input/closed-parent files in the
combined source closure. Every whole byte must remain unchanged across the
fresh replays. The ten complete first corrected-checkpoint records are
listed in `/tmp/grouped66-r2-ten-runs.json`. The original earlier failed
checkpoint stays preserved separately in27f83b98fa.

ROOT also releases read-only PDF rasterization into /tmp and two actual
visual inspections, by ROOT and the independent peer, of exact PDF SHA256
`c60f35c31bfbf8d386ee28f718f23c50c004f461cfa41ec58bfb44326ed13106`
and TeX `b55974f915875136060858a6a763821183ad6a1c7b0b2326aa87f01c708f7ea4`.
Inspect the complete front, all fixed definitions, floor/reciprocal terms,
943-tile table,430-action decoder,436-digit seed,62-symbol alphabet and
footer for legibility, clipping, overlap and missing content. Outside visual
review records may be written; candidate files stay frozen. Further final
metadata/inventory closure and promotion require a separate ROOT release
after all fresh comparisons and both actual visual reviews pass.
