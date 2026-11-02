# Independent isolated wrapper-chain audit

The exact coordinator, monitor and path-guard bytes from commit `ad4cd81e5f`
pass an independent actual-subprocess toy test. This is **not** a verdict on
the outer launcher or a real Lean build. In particular, invoking a Python
script non-isolated can run startup hooks before its own guard executes; the
outer launcher still needs an independently checked isolated entrypoint.

`check.py` retrieves the three historical files from Git into a temporary
tree and verifies their SHA-256 pins. A positive control first confirms that
an ordinary Python child runs a temporary `PYTHONPATH/sitecustomize.py` hook.
The check then runs the actual historical isolated coordinator and monitor
with temporary dummy provider/source files, two fake builders and one fake
comparator. The coordinator exits 0 and reports `MATCHED_PASS`; the three
fake builder/comparator processes report `sys.flags.isolated = 1`,
`sys.flags.no_site = 1`, and no startup marker. The marker remains absent
even though `PYTHONPATH` is present in their environment. The actual monitor
terminals confirm the child command uses `-I -S` and exits 0.

The non-isolated coordinator and monitor CLI entries and an optimized
environment are also rejected. An independent author full-chain canary test
is reported at commit `f1dea51802`, with session 73693 exit 0; the test in
this packet is a separate implementation. The exact wrapper hashes and
observed child flags are in `CHECK.json`; `terminal-observation.json` binds
the actual review process exit 0 to that receipt.

The test does not use the real 70-source snapshot, provider calibration,
Lean, or the actual launcher. It does not prove non-Python executable,
dynamic-library, package-provider, concurrent mutation, or sampled-resource
assumptions. It does not establish an object-theory proof or iPRA theorem.

Run from the repository root, with the historical Git commit available:

```sh
python3 -B Computability/DiophantineConsistency/reviews/ordinary12-isolated-chain-independent-audit/check.py
```
