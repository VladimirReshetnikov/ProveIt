# Inherited normal-surface worker communication failure

The maintained test `test_normal_surface.NormalSurfaceTests.test_communication_retains_input_across_polls` exposes a **reproducible inherited pipe-progress defect**. It also fails in isolation. It is not classified as flaky, benchmark contention, or a regression introduced by the modular observer. No production or test-source fix was applied.

## Baseline identity

The working `Topology/UnknotRecognition/fast/fastunknot/normal_surface.py` is byte-for-byte identical to the local baseline snapshot at commit `3179d245a6752749c09d4fe79c018c79d2209c2d`.

- Baseline and working Git blob: `5f4de5cdf153a3ca3fd575aff9989a653d013c07`.
- Unchanged SHA256: `18deb3f935fc860e5c4f618e494b9cedaa49699ae3183ff68606e623a7979239`.
- Runtime: CPython **3.12.14**, built August 25, 2026, with Clang 22.1.3; POSIX `subprocess` implementation.
- Interpreter: `/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python`.

## Reproduction

From `Topology/UnknotRecognition/fast`, run:

```bash
python -B -m unittest discover -s tests -p test_normal_surface.py -v
```

The isolated eight-test module reports one `NormalTimeout` error and three skips for the unavailable optional Regina dependency. The failing test needs no Regina installation. It sends 500,000 bytes to a child that waits 0.12 seconds before reading, using repeated 0.05-second communication polls and a three-second local allowance.

Separately loading `git show HEAD:Topology/UnknotRecognition/fast/fastunknot/normal_surface.py` into its own Python namespace and invoking the baseline `_invoke` with that same command and payload reproduces `NormalTimeout` after **3.001 seconds**. This reproduction does not import the new modular observer.

## Blocking cause

The first `communicate(payload, timeout=0.05)` sends **65,536 of 500,000 bytes** before timing out. `_invoke` then retries with `communicate(None, ...)`. In this runtime, `Popen._communicate` registers stdin for further writes only when the current `input` argument is truthy:

```python
if self.stdin and input:
    selector.register(self.stdin, selectors.EVENT_WRITE)
```

The internal input buffer survives, but subsequent calls stop writing it. Five observed polls retain the same 65,536-byte offset, an open stdin stream, and a live child. The child waits for the remaining bytes and EOF; the parent waits for output. Increasing the outer deadline does not repair this stalled transfer. Reusing the nonempty payload as the public retry argument is also rejected by `communicate` once communication has started.

With the same child command and payload, a **single** communication operation succeeds in **0.137 seconds**, returns all 500,000 bytes unchanged, exits with code 0, and returns stderr `note`.

## Scope and impact

This remains a separately documented limitation of the inherited optional native-worker path. A large pending request can time out and become **INCONCLUSIVE**; this evidence does not establish a false topological verdict. The modular implementation and its tests are unaffected. A future repair should preserve pending stdin progress while maintaining cancellation and child cleanup, with its own focused validation.

The accompanying `normal_surface_baseline_issue.json` records the exact hashes, runtime, poll trace, comparison measurements, and baseline reproduction method.
