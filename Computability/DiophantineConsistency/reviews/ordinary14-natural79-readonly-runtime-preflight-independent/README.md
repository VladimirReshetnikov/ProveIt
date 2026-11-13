# Independent review: non-launching runtime observations

The pinned [preflight](../../research/ordinary14-natural79-readonly-runtime-preflight/README.md) is a read-only observer, not a build guard. Its deterministic static receipt reproduces. The independent checker verifies the exact Python imports and call sites against an audited allowlist, then runs controlled mocks of its observation function; it does not invoke Lean, launch a subprocess, or write to the observed inputs. At the pinned revision, neither supported mode contains a process-launch, Lean-execution, materialization, reservation, or filesystem-write call. Unsupported CLI arguments go to the failure handler. This conclusion concerns the checked script and standard Python behavior, not a system-wide permission boundary.

The mocked controls confirm that the disk flag is true only when available bytes are **strictly greater** than 5,100,000,000, for each reported filesystem: equality and one byte less both give false. A false flag does **not** make `--observe` exit with failure: the program reports the observation and always states `launch_supported: false` and `launch_authorized: false`. Thus this script cannot enforce a future build's stop threshold; an actual build would require a separate guard which fails closed and continues checking during execution. The read-only observer itself cannot start a build at any disk level.

The mock also checks exact `lean`/`lake` basenames in executable and `argv[0]`, and confirms that a denied command line or disappearing process is counted as inaccessible rather than as a negative match. Failure to enumerate `/proc` or read filesystem statistics propagates to the outer failure handler. A nonzero inaccessible count leaves idleness unknown; an empty match list does not establish exclusivity. The scan cannot detect all wrappers or establish persistent process state.

The static receipt reports 201 ordered source/header checks, 41 selected project frontier records, six selected external records, and a Lean binary hash. These are pinned observations, not actual Lean import resolution, transitive source or object provenance, companion validation, output reservation, an atomic disk reservation, or authorization to launch. The `assert` checks rely on the documented Python invocation without optimization. All observations may become stale immediately; the runtime result is intentionally not recorded in the deterministic receipt.

From `Computability/DiophantineConsistency`, while the pinned providers remain available:

```sh
python3 -I -S -B research/ordinary14-natural79-readonly-runtime-preflight/preflight.py --static | cmp - research/ordinary14-natural79-readonly-runtime-preflight/static.json
python3 -I -S -B reviews/ordinary14-natural79-readonly-runtime-preflight-independent/check.py | cmp - reviews/ordinary14-natural79-readonly-runtime-preflight-independent/result.json
```
