# Recorded verification

`replay.json` records the successful fresh aggregate `--full` replay of the
final portable packet: all 17 phases pass, including source reconstruction,
fresh-emitter certificate binding, independent fold/startup checks, restored
logical checks, and all 6,238 freshly derived unbounded runtime cases.
Its phase output is in `logs/`.

`upstream225_full_replay.json` separately records a successful fresh
`--full --full-baseline` replay of the unchanged predecessor, including both
K226 and K225 runtimes. The final aggregate uses its faster upstream audit
mode. Thus every required runtime has been freshly rederived; the two modes
are recorded explicitly rather than calling a stored-case audit a fresh proof.

The first packaging attempt exposed a CRLF-versus-LF input-pin mismatch in
Dag230.v after the complete upstream replay had already passed. The pin was
corrected to the authentic bytes inside the unchanged vendor ZIP. All 301
parsed source nodes and all source/machine/certificate outputs were preserved;
only the recorded input digest changed. `raw_zip_source_pin_audit.json` gives
the exact comparison. The final aggregate then passed from a fresh extraction.

`verification_summary.json` gathers these results. `pdf_qa.json` records
all-page visual review, compiler diagnostics, and exact transcription of all
448 transitions. The original paths and elapsed times in the receipts record
the development run; the portable scripts resolve their inputs relative to
the extracted packet and accept a user-selected output directory.

To perform all runtime replays in one new invocation:

```sh
python3 -B portable/reproduce.py --full --full-baseline --output-dir replay
```

These executable mathematical certificates do not claim a new end-to-end
Rocq or Lean kernel build for the final table.
