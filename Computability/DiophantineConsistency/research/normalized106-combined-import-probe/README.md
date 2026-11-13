# Prepared normalized106 combined-import diagnostics — not launched

**Do not run the prepared `--run` path:** independent review found unresolved descendant and session-drain limitations; the parent requested a simpler bounded direct-process approach instead. This prepared runner is retained as an unlaunched draft, not an approved launcher. This
packet prepares two separate, narrow import probes against the fresh
current14 base and its recorded package provider; no Lean import was run by
this packet. Neither probe builds project modules or proves a theorem.

* `EndpointPlusExternal.lean` imports the fresh-base
  `IPRAStandardCurrentEndpoint` and the five additional Mathlib modules in
  the [16-module source preflight](../normalized106-current14-sixteen-source-preflight/README.md).
  A successful actual import would test that precise combined environment,
  not every later source or dynamic dependency.
* `MatrixPlusExternal.lean` imports `Foundation.Vorspiel.Matrix` and the same
  five modules. It targets the known Matrix declaration as an independent
  diagnostic. A failure in this deliberately enlarged environment would not
  alone prove the endpoint imports that Matrix module or reaches a conflict.

The prepared runner pins both source files, Lean, the owned-session helper,
the source preflight, earlier direct-dependency probe, fresh-base state and
endpoint source. Before and after each case it checks the endpoint's base
producer, source, direct inputs and log; checks the 210 direct object,
companion and shadow paths for the endpoint and six package names against
the prior provider evidence; and refuses competing Lean processes. It uses
one fresh `/tmp` output directory, `-M2400`, a 120-second timeout, sampled
3.5 GiB session-RSS and 10 GiB available-memory stops, a 512 MiB free-space
floor, nice 19 and idle I/O. This is sampled monitoring, not a hard kernel
memory limit. Direct guards do not authenticate all transitive or dynamic
loads and cannot establish source-to-object provenance for the package.

The local `owned.py` is a narrowly modified copy of the previously reviewed
owned-session helper. It retains the direct leader until the session drains,
uses only owned-session signals, passively waits on monitor exceptions, and
records the actual reaped child exit through a new callback before either
returning or raising. If an exception stops a case, the runner records a
failed/stopped state and does not start the next case. Its normal final
status means both diagnostics terminated; each case's actual Lean exit and
log must be inspected separately, and a nonzero import exit is not itself
classified as a Matrix conflict. A descendant that moves to another process group within the same session may
survive `killpg`; the session-drain check prevents a false success but can
then wait indefinitely beyond the nominal timeout. Forced termination of the
Python supervisor, escaped-session children, inaccessible procfs and
unrecoverable receipt writes remain outside the guarantee. The operator must separately observe and
retain the runner's outer tool-session exit.

No-launch controls passed: [selftest-result.json](selftest-result.json) covers
pure import, guard-equality and resource refusal cases;
[preflight-result.json](preflight-result.json) reports 210 current direct
path guards; [owned-control-result.json](owned-control-result.json) records
three short **Python-child**, not Lean, tests for success, controlled
termination and monitor exception, including actual child exits and reaping.
These controls do not test successful Lean imports, every error path, or the
actual `--run` positive path. The first synthetic resource-stop test exposed
that the helper may report “finished outside resource bounds” after sending
SIGTERM; the test was corrected to recognize both rejection messages, and
the saved final controls passed. No actual diagnostic output is claimed.

Review-only commands:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/normalized106-combined-import-probe/runner.py --selftest
python3 -I -S -B Computability/DiophantineConsistency/research/normalized106-combined-import-probe/runner.py --preflight
python3 -I -S -B Computability/DiophantineConsistency/research/normalized106-combined-import-probe/test_owned.py
```

After independent review and coordinated resource clearance only, the
operator can execute `runner.py --run` with the same Python flags and retain
the actual outer session/exit plus `/tmp/normalized106-combined-import-probe-20261105/`
state, result and logs. A stale input or existing output path must be
investigated; do not overwrite prior evidence.

| Artifact | SHA-256 |
| --- | --- |
| `EndpointPlusExternal.lean` | `31aa8357e3b93245b71ffb41ad8c83b9897e1271f83dc478b922eb9c6b10ba2e` |
| `MatrixPlusExternal.lean` | `f31db847dd1b042c5b3f772e64acf13c9a0f91bfe42971afdb039964009ae722` |
| `runner.py` | `ed5f3f1bf138e5ae3586dd9c7c1ae4b46b4f2065de7b9295e4c827b7cc935866` |
| `owned.py` | `a41aee499bcef7b6ece79e1e7eae2b99210a70c1dafc1e54f2de55fbfc8d6201` |
| `test_owned.py` | `ee871f6d88a5d726953b72a8c4de1b061d2ed6f134ae106667696f674a44fc3d` |
| `selftest-result.json` | `e031d2071d3e981a2e63d31cd647778c44151a1c6fe38f6b1d100448c60c983d` |
| `preflight-result.json` | `bbeb1c0012b6f00824c43f445911a4e49a68e5fa698eb2a2e2a0ae24864d78ae` |
| `owned-control-result.json` | `245337268d6e87ede6de01ddc2cb00e627fb252666f2b08e1700f39adefbd1d9` |
