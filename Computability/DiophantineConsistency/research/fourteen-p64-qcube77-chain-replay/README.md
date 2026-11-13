# Guarded replay of the 77-operation same-zero chain

On 2026-11-04, [`run.py`](run.py) replayed `P64QCube77Unit`,
`P64QCube77OldFacts`, and `P64QCube77Existence` in that order into a fresh
temporary overlay. Each Lean process exited 0 and emitted exactly its
expected `[propext, Classical.choice, Quot.sound]` axiom reports, with no
warnings or `sorryAx`. All three resulting object hashes matched the earlier
author-produced objects byte-for-byte. Before and after each stage, the runner
checked the source files, Lean binary and three declared direct captured
inputs. The overlay takes precedence so later replay stages import earlier
replayed objects.

The [receipt](receipt.json) records commands, elapsed times, input/output
hashes and statuses. Full outputs are [Unit](Unit.log), [OldFacts](OldFacts.log)
and [Existence](Existence.log). This is a three-module guarded replay, not a
rebuild or authentication of full transitive project, package, dynamic or
search-path ancestry; it also does not bind external coefficient payloads,
JSON or PDF semantics. It does not independently replay the separate iPRA
endpoint.

The runner refuses to overwrite its temporary overlay and receipt files; a
repeat needs fresh paths in a copy.

| Artifact | SHA-256 |
| --- | --- |
| `run.py` | `21510ad2b4949be10a49c503327c7733980a555ffea5ad34bd23f42615994229` |
| `receipt.json` | `823b4c7be42bf86472b12974e3b4bbe57dd9d3d4fe92c23ff53195badfb6be63` |
| `Unit.log` | `9d05730a8ac3d21d606f00658c5db9676ad628b4f4904573ec73ec8fc2530886` |
| `OldFacts.log` | `1ac2ff834e128dfdc50ca3ef9399c6b4c87ac5f97971a16c81d59a27362e3630` |
| `Existence.log` | `fd0b66617a2aad80d240d5a48dc6f80c09c6163a784bc133e5f29436ab08fb72` |
