# Independent review of the bounded RSS retry

The independently tested driver snapshot has SHA-256 `2c8a7f84…`. Its
one-second missing-RSS retry passes the fake-process controls below, subject
to the limitations of the earlier [monitor review](../ordinary12-denominator-monitor-independent-audit/README.md).
The review does not run Lean or establish a successful full rebuild.

The preceding rebuild attempt ended with wrapper exit 1 and no paired proof:
its stopped `FreeJDenominator` compiler actually exited 0, but the monitor
recorded `rss_unavailable_while_unreaped`. The dependency check and peer
suffix did not run. This failed-closed result remains a failure, distinct
from the earlier proof-compilation failure and from these fake tests.

For the corrected driver, independent actual fake-child tests observed:

- A persistently live child with missing RSS was stopped after about one
  second and its leader reaped.
- A temporary missing reading was accepted only after a later valid sample.
- A child that exited 0 without any valid sample returned the explicit
  `no_rss_observation` stop reason; exit 0 alone is not a pass.
- A child that exited after an earlier valid sample was accepted when the
  later missing reading coincided with an observed exit.
- A zero `VmRSS` reading was treated as unavailable.

Separate actual fake-child controls delivered SIGTERM and SIGINT to the
monitor wrapper after a same-group descendant confirmed it ignored SIGTERM.
Both returned the appropriate interruption reason, and the leader and that
descendant were absent/reaped. These are specific process-group controls, not
a guarantee for escaped descendants, PID races or forced wrapper SIGKILL.
RSS still samples only the direct child, and sampling is not a continuous
memory limit or hard quota. The live driver also does not hash-pin the frozen
manifest at its read; the earlier post-run hash observation does not
authenticate its execution-time contents.

The independent aggregate verifier exited 0 in tool session 24915. Its
receipt `CHECK.json` and `terminal-observation.json` preserve the exact driver
hash, previous failed-wrapper/child exit distinction, and observed control
results. Re-run with temporary fake processes only:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-rss-retry-independent-audit/verify.py
```
