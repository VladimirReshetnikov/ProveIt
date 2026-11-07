# Independent partial-failure audit: strong transport

Author-recorded outer session 57859 exited 1. The first stage compiled successfully and produced its pinned object and standard `[propext, Classical.choice, Quot.sound]` report for conditional strong=1 to 38-terminal equality. The second stage dependency scan passed but its compile exited 1 at a maximum recursion-depth error; its `sorryAx`-contaminated report is not a theorem, and no stage-two object exists. One unused-simp warning was emitted. There was no monitor stop and the final provider postflight was not reached.

Both stages' logs, selected direct providers, 400 guard slots and 1,194 overlay links check without Lean replay. The successful first stage does not itself prove the 33-constructor mapping or seed equivalence. Provider observations are point-in-time; inherited initial-stage numeric outer exit remains unavailable.

Checker SHA-256 `e8f8aa4ecfd36c4f67f748950f07f5e16345164b1bc3eb2e51492314c5a49e71`; result SHA-256 `a7056937bf399a94d4b70e5f4dedbdb7d876c5586daef30f873b09384fba1178`.
