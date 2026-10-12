# Fresh complete replay, 12 October 2026

The unchanged archive was copied to the user's configured Linux worker,
codexbox, and extracted under the unique external scratch directory
`/tmp/proveit-lambert-incoming25-0caZtJ/extracted`. No original repository
evidence was used as an output destination or rewritten. The Windows host
has no WSL installation; the remote run supplies the extended-range long
double required by the unmodified verifier. The arithmetic guard was kept.

From the extracted package root, the command was:

```
/home/codex/.local/bin/uv run --no-project --python /home/codex/.local/bin/python3 --with-requirements verification/requirements.txt python verification/verify.py --output-dir /tmp/proveit-lambert-incoming25-0caZtJ/replay
```

Exit code: 0. The delivered four dependency versions were used. The full
fresh output directory and captured stdout/stderr are copied here. The
original verification directory remains as delivered. results.json records
the actual Python, platform and numerical formats.

Results: 5890 exact checks through q^12; 70 main cases including every finite
Lagrange summand through n=1025; 35 independent mpmath comparisons at 80
digits, 15 also compared with exact coefficient polynomials. The optional
large-index comparison uses a separate truncation at k=256 and its exact
omitted-term majorant. That bound does not bound floating-point roundoff.
All fourteen largest-index cases improve with the derived first correction.

These are finite exact identities and numerical diagnostics, not interval
certificates or a proof of asymptotics, continuation or summability. The
analytic audit is in ../INTAKE-PROOF-AUDIT.md. No delivered patch is applied.
