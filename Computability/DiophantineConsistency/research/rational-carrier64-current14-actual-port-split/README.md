# Current14 fixed beta is nonzero

`Current14BetaNonzero.actual_beta_ne` checks that the actual first port of
`CurrentWindowCarry2011.ports` is nonzero. It proves the result from
`1 < radix ^ 2011` and `beta = radix ^ 2011 - 1`, keeping the huge fixed
beta irreducible rather than evaluating its full numeral. This is a
standard Lean arithmetic fact about the actual port, not an internal iPRA
theorem or a proof of consistency.

Attempt01 passed: Lean and runner exit 0, no warnings or `sorryAx`, with
axiom report `[propext, Classical.choice, Quot.sound]`. Direct providers,
captured current14 sources, and fresh-base state were guarded and stable.
The run took 1.383 seconds with peak sampled process-group RSS 1,690,439,680
bytes under `-M2400`, 120 seconds, 3.5 GiB RSS and 10 GiB available-memory
limits, nice 19 and idle I/O. Transitive/dynamic ancestry and sampling are
inherited limitations. The output object is
`/tmp/rational-carrier64-current14-beta-priority-check01/Current14BetaNonzero.olean`,
SHA-256 `3cd491a204ca63a508e5f810010a71aa934f82c6c77d9f337d0f5ca43bd06a01`.

| Artifact | SHA-256 |
| --- | --- |
| `Current14BetaNonzero.lean` | `5bafdd5655d635580b6be367e71d7b9314ea35109a4736f6076932395d1852fb` |
| `check_beta01.py` | `ff58b976f9fd2db16a53d6792d69438061ded8634af049e12199fb43d927ae0e` |
| `observations/beta01/compile.log` | `8209e0ae0677e6ad3b3fcafa5181697a0e787e2cb1625cda0afd816a52739390` |
| `observations/beta01/result.json` | `3e72bfa5ba7d4ba6fe0731404d4fa7e7662777e0dd04974521df299bc206f70a` |

The earlier combined rational/iPRA client stopped at the interpreter
memory limit before producing an object; it is preserved separately under
`../rational-carrier64-current14-actual-port/observations/attempt01/`.
