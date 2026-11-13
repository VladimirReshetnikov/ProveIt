# P64 q³ quotient: iPRA endpoint client

`P64QCubeEndpoint.lean` composes the checked all-model positive-zero
equivalence `P64QCubeExistence.positive_zero_iff` with the existing P64
positive-zero/halting bridge. It then applies the same generic adapters to
obtain native, standard, and equality-only iPRA derivability statements for
the q³-quotient graph's `positiveShift expression` and the selected mapped
Foundation refutation negation. These are proof-existence statements in the
specified object theories; they do not assert consistency itself.

The corresponding candidate has 14 positive inputs and 81 live operations;
its externally checked exact degree is 68. The endpoint concerns the Lean
graph with the symbolic compact44 ports. The finite graph/degree and retained
coefficient checks, external JSON or page transcription, and a formal
filesystem/gzip/PDF identification remain distinct from this client. It does
not prove global minimality.

## Observed check

On 2026-11-04 tool session 24311 actually exited 0. Lean 4.32.0 reported
`[propext, Classical.choice, Quot.sound]` for the positive bridge and all
three endpoints, without warnings or `sorryAx`. The exact command, elapsed
time, search path and direct input hashes are in
[`observations/attempt01/result.json`](observations/attempt01/result.json);
the full log is [`compile.log`](observations/attempt01/compile.log). The
runner checks the source, Lean binary, `P64QCubeExistence.olean`, and the
P64 endpoint object hashes before and after compilation, and refuses an
existing output directory. Reproduce while the captured providers remain
available, after choosing a fresh output directory in a copy of the runner:

```sh
python3 -u Computability/DiophantineConsistency/research/p64-qcube81-ipra-draft/run.py
```

| Artifact | SHA-256 |
| --- | --- |
| `P64QCubeEndpoint.lean` | `bd571e2b4d0c7d9c8b25d4737dc51bc02890fb7e241a06b30238d66c06bf52e0` |
| `/tmp/p64-qcube81-ipra-check01/P64QCubeEndpoint.olean` | `893103d30af30a2da273e6f9509a18933c5adce8c9de391cc414c6e98aac6763` |
| `/tmp/P64QCubeExistence.olean` | `74ef2f50d92729ca37cea7aaa5ea1d21df54eeaa6314aeb0fe5138818f23b8f2` |
| Captured `IPRAPositive64.olean` | `9416a700b41ca923ad20ad90ef27fc275d99dae7cc59ad3e91d82bf720b8b59d` |
| `run.py` | `a5ce73b1d168461c5fcb977e34454461a358bc33801e324cbb13a13b4633aa94` |

This is a single guarded client check against temporary prebuilt providers,
not a paired end-to-end replay. Complete project, package, dynamic and
search-path ancestry remains inherited and was not independently rebuilt or
audited in this check. The earlier P64 captured-provider replay and the
zero-equivalence packet have their own precise scopes.
