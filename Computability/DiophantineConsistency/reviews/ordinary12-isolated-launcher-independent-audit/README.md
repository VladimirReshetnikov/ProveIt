# Independent review of the isolated coexistence launcher

**Verdict:** the exact launcher from commit `face1a63cd` passes this no-build
review and is ready for the documented coexistence-only replay, subject to
the point-in-time and runtime limitations below. This verdict does not claim
that the replay itself has succeeded or that an iPRA theorem has been proved.

The audit verifies the exact launcher, gates and toy-control bytes against
their historical commit and SHA-256 pins. Its isolated, read-only invocation
of the launcher's real `preflight()` exited 0: it checked 70 project sources,
1,540 Foundation artifacts, 14,764 provider guard paths, six pinned review
receipts, and sampled 6,035,574,784 free bytes. It did not call launcher
`main()` or create any of its three real output paths. The preflight records
its observed Git HEAD; the real launch must repeat all checks because inputs
and available space can change.

The author's gate and launcher toy controls exited 0. Independent direct
invocations rejected non-isolated, `-I`-only, `-S`-only, optimized `-O` and
`-OO`, and nonempty `PYTHONOPTIMIZE` before starting a build. A temporary
positive control confirmed ordinary Python executes a supplied
`PYTHONPATH/sitecustomize.py`; an isolated invocation of the real launcher
did not execute it.

A second isolated harness imports the exact launcher and replaces only its
preflight and destination paths with temporary test fixtures. Its unmodified
`main()` then runs a **real subprocess** containing a harmless fake coordinator.
The coordinator confirms isolated and no-site flags, the bootstrap's local
wrapper import, absence of the injected startup marker, and removal of the
tested Python, Lean and dynamic-loader environment variables. A deliberate
child exit 7 is preserved as the launcher's exit 7 and in its terminal record;
child exit 0 is similarly retained. No real Lean builder is accessible from
these fixtures. The separately reviewed actual coordinator-to-monitor-to-fake-
builder chain is pinned by the corrected launcher's review checks.

Run the exact pinned launcher using externally enforced isolated startup,
`python3 -I -S -B .../launch.py`, and a trusted clean process and loader
environment. Python and system startup precede any script-level guard; the
launcher is not a defense against a compromised interpreter, loader or OS.
The preflight is a sequence of point-in-time checks, not an adversarial
concurrent-mutation barrier. Disk monitoring samples available space and
logical output size; it is not a reservation or hard quota. The Foundation
provider's original outer wrapper exit remains unobserved, and package-
transitive and dynamic dependencies remain inherited.

The review process actually exited 0 in session 58848. `CHECK.json` preserves
the individual exits, exact source hashes, preflight result and fake-child
observations; `terminal-observation.json` binds that actual exit to the
receipt. Reproduce this audit from the repository root while the pinned
temporary source/provider inputs remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-isolated-launcher-independent-audit/check.py
```
