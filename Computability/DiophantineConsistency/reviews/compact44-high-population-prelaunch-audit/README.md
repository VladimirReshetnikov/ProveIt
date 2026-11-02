# Conditional no-build high-mask population review

This reviews exploratory packet `eb3e089ecb` and its exact proposed replay
driver, SHA-256
`52b10e75fe24d6aa883b7db3c011171ce7c5fc82e5c45e46ba0a39aa4aa1fd30`.
The source defines a standard 8807-digit radix-`2^67` list and states that
its cast list value has population 986 and is below the word bound in each
IΣ₁ model. The packet reports a successful single-side exploratory session
70407, and its retained log has exactly the two expected axiom reports and no
warnings. That single-side record is not a paired compilation or an
independent verification of the full dependency/object chain.

The separate external checker in this review parses the pinned Lean list
syntax, independently reconstructs the high positions from the pinned recipe
builder, and checks all 8807 digits and the full integer against retained
`MF_source−β`. It confirms binary population 986 and rejects four altered
positions. It passes in both normal and optimized Python with explicit checks.
The original display checker also passes in both modes and rejects its three
mutations. These are finite external byte/source checks; they do **not** prove
an internal equality to the retained high payload or the graph's high port.
They do not establish machine semantics or an iPRA proof.

The optional mod-8 residue attempt remains **unproved**: retained attempts
04, 06, 07 and 08 have recursion-depth errors (with `sorryAx` in their failed
reports), while attempt 05 has a Lean memory exception; the packet reports
its exit as 134. These failed sources are separate from the successful
population/word-bound source. An external numerical residue is not a model
proof of the needed graph-port residue.

The exact driver pins its source and independently audited 342-module parent,
checks the two named axiom reports and allowed sets, rejects compiler
warnings/errors/`sorryAx`, checks direct imports and both outputs, and reruns
the parent audit. This review's two-child fake compiler/dependency loop
passes and rejects wrong report names, injected warnings, `sorryAx` and wrong
dependency output. Bad-pin, existing-output and optimized-interpreter guards
also pass. The first reviewer guard test itself exited 1 because it expected
the wrong wording for the existing-output error; it was corrected to match the
actual error and rerun successfully. None of these fake controls compiles Lean.

A real pair is conditionally ready only with a trusted clean **initial**
loader/interpreter environment and externally enforced stable-HEAD,
sole-Lean window. The driver does not enforce HEAD stability and stripping
child variables cannot retroactively protect the initial loader. The pinned
monitor has the previously reviewed sampled RSS/disk and process-group
limits, not hard whole-process-tree quotas; separate `--deps` and parent
audit processes have ordinary timeouts without those RSS/group controls.
Provider/source hashes are point-in-time and complete package-transitive or
dynamic ancestry is not authenticated. A post-build audit must inspect both
actual child/outer exits, exact source/object/log/import chains and axiom
reports, preserving the retained-port and mod-8 limitations.

Reproduce the static source/byte and mock review from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-high-population-prelaunch-audit/audit.py
```

This static script does not itself rerun the long parent artifact audit; the
separately observed exact-driver `check_pins()`/`verify_parent()` preflight is
recorded in `terminal-observation.json` once completed. Original `/tmp`
provider objects are required and changed pins fail closed.

The separate exact-driver parent preflight session 51061 and full returned-JSON
comparison session 71189 each exited 0.
