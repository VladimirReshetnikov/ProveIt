# Independent review of the original coexistence launcher

This review is pinned to commit `2b44686e4b`. **Do not use this review as a
launch approval:** an actual child-process test found that its coordinator
inherits `PYTHONPATH`, allowing Python `sitecustomize.py` to run before the
coordinator's code. A correction requires its own independent review. The
review does not start a project build.

The checker retrieves the exact four historical launcher, gate and toy-test
files from Git into a temporary tree and verifies their SHA-256 pins. It
also hashes the launcher's seven current fixed wrapper/document inputs and
the actual source manifest, provider receipt, Foundation input manifest and
Lean executable against the historical launcher pins. These are point-in-time
checks only; they do not authenticate uncontrolled Python startup, all
transitive dependencies, or changes between checks and use. The original
provider wrapper's outer exit was not recorded, and the stored provider
receipt is not a new build.

Both historical toy suites exited 0 in normal Python. Independent temporary
receipt controls accepted a valid receipt and rejected a wrong receipt pin,
terminal pin, status, observed exit, or claimed receipt hash. A missing fixed
launcher pin was rejected. Direct launcher invocations with `-O`, `-OO`,
`PYTHONOPTIMIZE=1`, and an unexpected argument each exited 1 before a build.
These controls do not independently replay the full 70-source preflight.

For the environment test, the review imports the exact historical launcher,
replaces its preflight and output paths with temporary toy values, and sets
its monitor directory to a temporary directory containing a harmless fake
`paired.py`. The launcher uses its actual `subprocess.Popen` to start that
fake coordinator. With `PYTHONPATH` set to another temporary directory whose
`sitecustomize.py` sets `AUDIT_SITE_EXECUTED=yes`, the child exited 0 and
reported both the inherited path and that startup marker. It also inherited
`LEAN_PATH`; the later actual `rebuild.py` sets its own `LEAN_PATH`, so this
observation alone does not show that the inherited value reaches Lean.
`LEAN_SRC_PATH`, `LEAN_SYSROOT`, `LD_LIBRARY_PATH`, `LD_PRELOAD`, and
`LD_AUDIT` were absent in the fake child. Python startup may also run before
the launcher itself executes, so sanitizing only its child environment does
not authenticate the launcher's own startup.

The full observed outcomes are in `CHECK.json`. This is a finite launcher
audit, not evidence of a successful 70-source replay, graph transport,
denominator integrality, checker calibration or an iPRA proof. Source and
provider rechecks remain point-in-time rather than protection against all
concurrent mutation. Sampled disk limits are not hard quotas.

Run from the repository root in normal Python, with the historical commit
and pinned temporary provider/source inputs available:

```sh
python3 -B Computability/DiophantineConsistency/reviews/ordinary12-launcher-independent-audit/check.py
```

The checker exits 0 after finding the documented environment weakness. Its
status is `PASS_AUDIT_WITH_ENVIRONMENT_FINDING`, not a launch-ready verdict.
