# Actual-port 66-row rational evaluator: external zero equivalence

For the fixed current2011 ports supplied by the coherent historical
provider, `actual_beta_ne` proves beta is nonzero without expanding its
large numeral. `actual_positive_zero_iff` specializes the checked generic
rational evaluator theorem: a strictly positive integer valuation is a
zero of the 66-row rational evaluator iff that **same valuation** is a
zero of the 67/106 integer syntax.

This is an external Lean statement about ordinary integer/rational
evaluation. It is not an internal iPRA formula containing rational leaves,
does not establish an integer-leaf 66-operation equation, and does not
alter the maintained equation/PDF. The parent integer syntax has the
separately checked historical IΣ₁ and iPRA endpoint. The four fixed runtime
leaves and their storage accounting are documented in
`../normalized106-rational66/`.

Attempt02 passed: Lean and runner exit 0, no warnings or `sorryAx`, both
reports `[propext, Classical.choice, Quot.sound]`. It ran 1.637 seconds,
peak sampled RSS 1,982,001,152 bytes and minimum available memory
18,926,116,864 bytes under `-M2800`, 120 seconds, sampled 3.5 GiB group
RSS and 10 GiB available-memory stops, nice 19 and idle I/O. Direct guards
were stable; outer session 73833 was independently observed to exit 0.
The direct historical `CurrentKernelData2011.olean` resolves to
`/tmp/ha87-full-transitive-p3xt6wra/lib/DiophantineConsistency/CurrentKernelData2011.olean`,
SHA-256 `932f7951a955a29106d40b5e2b94feeb34c612164e3e606970dc0933a142a455`,
matching its recorded PASS producer. Its recorded source snapshot and
producer state are also pinned. The prior rational specialization object
and its receipt are direct guarded inputs. The stage-078 producer's
recorded direct-input/companion slots are rechecked; its syntax output was
directly guarded by the earlier 66/67 binding, not re-guarded here.
Historical transitive/package/dynamic ancestry and sampled monitoring
remain limits; no fresh current14 provider is mixed into this search path.

Attempt01 failed because the port-parametric syntax module did not import
the actual fixed-port definitions. Its exact source/log/receipt/outer exit
are retained under `observations/attempt01/`; attempt02 explicitly imports
the historical fixed-port object. The successful object is
`/tmp/normalized106-rational66-actual-priority-check02/Normalized106RationalActual.olean`,
SHA-256 `64287a9ab9685809828186004896973e5c46e252391fadc992aaaf8cc761ae7c`.

| Artifact | SHA-256 |
| --- | --- |
| `Normalized106RationalActual.lean` | `3a423c71cd37c7129b262042c512a8523f84b3a892ba4459564d5831681e48ae` |
| `check02.py` | `f8b0ffa2457f0ee3910f36eabb90bbebe64621f73f22c56dc3c3c78391edacd5` |
| `observations/attempt02/compile.log` | `cff2bb678953a4e2b0698006662f0dd2baf81a92368b87f9f26c786cb6753877` |
| `observations/attempt02/result.json` | `3b70da32f03ab55d9e52d01106e95a087f513869f33296cb78c558fc6f118394` |
| `observations/attempt02/outer-terminal.json` | `409516fd5ffa06cca004f9ca367cc45e5ce6875c35f4d159dc64cb0f37a836d1` |
