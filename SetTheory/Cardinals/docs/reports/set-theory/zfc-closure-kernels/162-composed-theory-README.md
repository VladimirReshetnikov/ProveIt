# Minimal replay of the inherited dominated-rho8 certificate

Only Python 3's standard library is needed. From this directory run:

```sh
python3 check_classical_compact.py dominated_rho8_full_certificate.json
python3 audit_classical_independent.py dominated_rho8_full_certificate.json
```

Both commands should report `verified: true`, 3,728 proof nodes and 5,160
shared term nodes. The second implementation uses nested tuples instead
of the first implementation's independently interned term algebra. Neither
performs proof search, unification, a binary-machine run, or an ancestor test
suite. `fresh_replay.json` records both executions for this delivery.
The inherited checkers use Python assertions: run without `-O` and with
`PYTHONOPTIMIZE` unset. `python3 -I` may be used in place of `python3` to
ignore Python environment overrides.

The certificate and both checkers are retained byte-for-byte from
`K218_Dominated_Rho8_2026-10-20.zip`, embedded in the K217 dominated
continuation predecessor. `NOTICE.md` is the predecessor's unchanged
attribution and reuse notice. This delivery does not claim authorship of
the inherited proof or its two checkers.

## Exact scope

The certificate derives identity, K, Peirce, cd59, B, S and the full
unrestricted rho8 schema from truth, modus ponens and dominated-rho8
instances. Each axiom satisfies the numeric side condition by the
implication-subterm inequality, or by its fourth parameter being zero.
The only normalization is `I(0,0)=0`; all schema variables range over
arbitrary native natural-number codes. The resulting theorem says that
the dominated and unrestricted numerical calculi derive exactly the same
codes, after proof-leaf replacement.

These scripts check **that finite logical bridge**. The unrestricted
native calculus's equiconsistency with ZFC is a separate inherited theorem
identified in the report. The scripts do not prove that foundational
calibration anew and do not establish any binary runtime or blank-start
claim. They also do not constitute an exact-K215 Lean/Rocq endpoint.
