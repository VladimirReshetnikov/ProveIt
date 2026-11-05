# P64 missing-source and retained-payload comparison

The package-64 `positive14/polynomial.json` points to
`native/COEFFICIENT_BINDING.json`. At the time of the original observation,
that file was absent from this checkout: of the 40 files listed in
`SOURCE_PINS.json`, 6 paths existed and 34 were absent, including the binding
and all four compressed coefficient payloads. The 34 paths have since been
restored from their verified historical Git blobs without overwriting the six
existing files; the recorded operation is [`restoration.json`](restoration.json).
After restoration, a new read-only run observed all 40 paths present with the
pinned hashes; its output is
[`observation-after-restoration.json`](observation-after-restoration.json).
The separately recorded
[`restoration-verification.json`](restoration-verification.json) reports that
the package verifier exited 0 in a temporary copy and reproduced `CHECKS.json`
byte-for-byte.

[`check.py`](check.py) verifies all 40 pinned historical `commit:path` Git
object identities and SHA-256 hashes against the local Git object database.
All 40 historical blobs are available and match, including the previously
absent binding. It also checks that the four restored compressed payloads are
byte-identical to the retained files in
[`candidates/ten-positive-shifted-strong/coefficients`](../../candidates/ten-positive-shifted-strong/coefficients),
and records decoded sizes and hashes. It does not restore any package path.

This is an external byte and Git-provenance comparison. It does **not**
evaluate the symbolic Lean `paramKernel` or prove that a Lean port equals
any payload byte string, interpret JSON or PDF in Lean, or establish exact
polynomial degree. The P64 Lean replay has its separately documented
captured-provider boundary.

On 2026-11-04 the original presence-specific script ran twice with observed
exit 0; the second output is retained as [`observation.json`](observation.json)
and its exact script as
[`check-before-restoration.py`](check-before-restoration.py). The current
checker accepts either presence state and verifies any existing package
copies. Run it with:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/fourteen-p64-payload-provenance/check.py
```

The original script SHA-256 is
`40e39098c6d1f097c224c24830ea560933efc2058e0fafe3716f6c7e838b8b21`;
the observation SHA-256 is
`bf10c61c3417df683a2824eaf2d7c83e9d7f29f39cf05188b1c50485eefd1b06`.
The updated checker SHA-256 is
`f4da4b9efbeb9edae70a79f0675e8b0dbd2da77b5dea46dd35467a6988fd6c0a`;
the observed post-restoration output SHA-256 is
`9cef15c01a68ce5e73daa427fb566516fbcd840ade371bfd411ca22314035049`.
The script depends on these historical objects remaining in the local Git
object database and refuses optimized Python. The original script intentionally
expects the recorded pre-restoration package-path presence state.
