# Independent review and final artifact checks

`AUDIT.md` and `FINAL_AUDIT.json` are the separately assigned reviewer's
ordinary-proof and complete exact-algebra acceptance. They bind the frozen
producer, checker, proof, equation, expansion and original source archive.
A second agent independently recollected every coefficient in
`SECOND_INDEPENDENT_EXPANSION.json`.

Run the separate standard-library auditor from the package root:

```sh
python3 -B review/independent_audit.py .
python3 -B -O review/independent_audit.py .
python3 -B verify_report.py
```

The equation has 212 variables,151 rows,5357 collected quartic terms and
height17592186044420. The producer checker rejects15 actual-data corruptions;
the separately assigned auditor's own mutation controls are reported separately.

The review caught and repaired the small-t constructor estimate, incomplete
placed-source packaging and a transient readable-TeX parser error. Later
article review caught Markdown's interpretation of literal ASCII powers and
multiplication in the prose report. `build_tex.py` now preserves those
operators, and `REPORT_LITERAL_QA.json` checks four key identities and rejects
three conversion corruptions. The final PDF was recompiled and visually
reviewed after that repair; the proof and circuit bytes did not change.

All main certificates contain relative paths. The original archived source's
historical path strings are retained only as provenance, never as active
input locations. `SOURCE173_RECOVERY.json` identifies every exact source alias
and the restored original ZIP; the current verifier authenticates its bytes
and its immediate pre-optimization affine213 stage before optional replay.
