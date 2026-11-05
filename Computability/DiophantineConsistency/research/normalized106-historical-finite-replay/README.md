# Isolated historical-input 67/106 finite-audit replay

The original `fourteen-normalized-product106/audit.py` passed when run
without `--write` in a fresh isolated directory populated by copies of its
16 pinned inputs. The two Lean files whose live workspace bytes had drifted
were the exact Git-recovered versions recorded in
`../normalized106-degree-audit-drift/`; every copied input and its source
was hashed before and after the run. The auditor reported 14 variables,
67 integer-leaf operations, exact degree 106, 47,313 raw port bytes and
the original certificate SHA-256
`16358ce2d453371d2f2d1cad8ab22136ea61ec9ff77200a55264ad56d4a57879`.

The driver and auditor both exited 0. Outer execution was directly observed
separately from the subprocess receipt. The command ran at nice 19 with a
120-second subprocess timeout; stdout and stderr are retained. The copied
inputs and their source files had stable hashes at both checks. This
reproduces the historical-input finite graph/degree/port audit; it does
**not** pass the unchanged audit against current Lean source, rebuild Lean,
formally prove the degree in Lean, parse a PDF, or independently certify
the historical source's proof ancestry. The separate drift packet retains
the failed current-workspace attempt and exact reviewed source diffs.

`replay.py` creates the fixed fresh output directory
`/tmp/normalized106-historical-finite-replay-20261105` and refuses to run
if it already exists. To repeat it safely, use an explicitly reviewed
fresh output path; do not overwrite or remove the saved result.

| Artifact | SHA-256 |
| --- | --- |
| `replay.py` | `279391ee3495666b3a36c071173eeb8b8ca478d0719a931c15622435f85ffeb0` |
| `observations/attempt01/stdout` | `3f3a27b1cbd4a1e496d3812fd7eee6ffd6640ed6bdeb99dfb4cb2e3a2ac22b22` |
| `observations/attempt01/stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `observations/attempt01/result.json` | `efb69ba7f0177db329772da9b2fdda4cd860649d7716902a7f285b849624ed92` |
| `observations/attempt01/outer-terminal.json` | `96c732de8f30ba79ecef33a979ba4ea218e138afb30290bdeae53bc5695483a6` |
