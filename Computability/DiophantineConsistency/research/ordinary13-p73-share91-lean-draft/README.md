# Uncompiled P73 91-operation Lean bridge and read-only preflight

This packet proposes a three-stage Lean client for the independently reviewed
91-operation P73 graph. **None of these source files has been compiled or
kernel checked.** `preflight.py` is a read-only source/resource survey, not a
Lean runner, an authorization to launch, or evidence of a successful build.

`P73Shared91.lean` copies the maintained P73 graph's literal block and changes
only `(1+k*qm)*q3` to `q3+k*(q3*qm)`. It proposes generic evaluation equality
for every `CommRing R`, every `p : Fin 4 → ℤ`, and every valuation. The proof
uses a small `share_eval` ring identity before evaluating the first residual;
the other three residual expressions are proposed to agree by reduction. The
sum-of-squares output then uses those residual results. Tactic elaboration,
simplifier behavior and resource feasibility are **untested**: the existing
P73 proof specifically warns that expanding the full first carrier with `ring`
previously exhausted memory.

`P73Shared91Model.lean` proposes same-valuation `InternalZero` equivalence in
all IΣ₁ models and composes it with `IPRAPositive73.positiveBridge`.
`P73Shared91Endpoint.lean` proposes the native, standard and equality-only iPRA
endpoints using the existing `IPRAOrdinary12Chain` adapters. Those are proposed
statements, not results. They are conditional on successful compilation and
on the actual authenticated provider ancestry of the existing P73 theorem.

The candidate's four fixed leaves remain integer constants, interpreted in a
ring through its integer cast; there are no additional fixed leaves. The
91-operation count is the external named-gate/DAG convention, not a Lean
theorem about a circuit evaluator. The finite comparison checks that each
named operation matches the independently reviewed candidate JSON. It does
not make Lean read JSON or PDFs or prove file-content semantics.

## Read-only preflight

From the repository root run:

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary13-p73-share91-lean-draft/preflight.py
```

It pins the draft, maintained P73 source, current endpoint source, candidate
JSON and independent candidate-review receipts; it compares all 91 literal
operations with the candidate, verifies the input and port names, samples
`/tmp` free space, and observes whether two conventional project `.olean`
paths exist. These observations do **not** authenticate any object or its
transitive packages/dynamic inputs. The output always says launch readiness is
blocked because neither a complete audited provider closure nor a reviewed
resource-guarded runner is supplied here. Free space is point-in-time and is
not reserved; the previously established runtime disk-stop floor is
5,100,000,000 bytes. The tool invokes no Lean process.

The P73 endpoint's existing [author-side build description](../thirteen-p73-endpoint/README.md)
reports successful results, but it is not a paired independent replay or an
authenticated full project/package/dynamic closure. The required source and
project objects for `P73Graph` and `IPRAPositive73`, their direct and
transitive dependencies, and any imported local client objects must be
authenticated in an isolated reproducible provider plan before a guarded
compile. The existing compact44 P73-source and JSON/file correspondence
remains external. P73's fixed-port byte checks use the P72 physical copy
matching P61 binding hashes; the P61 physical payload paths were absent in the
prior audit. No new claim about those files, the rendered PDF, or the truth of
either side of the consistency biconditional is made.

After provider authentication and adequate disk headroom, prepare and
independently review a staged runner with per-stage time, memory and disk
guards, direct-object route pins, stage receipts and postflight. Run the graph,
model, and endpoint stages only with an explicit allocation of the shared
Lean slot. Preserve all earlier artifacts and record any failure honestly.
