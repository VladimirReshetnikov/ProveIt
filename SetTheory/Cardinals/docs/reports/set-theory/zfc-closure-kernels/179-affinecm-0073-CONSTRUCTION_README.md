# Proof-only batching for four K215 Lean certificate checks

This overlay replaces the proof of `fwd_ok12`, `fwd_ok13`, `fwd_ok14`, and
`fwd_ok15` in their existing modules. Imports, namespaces, public theorem names,
and public theorem statements are unchanged. The program and certificate
literal data in `KSource215Data.lean` are unchanged.

Each previous proof asked one `decide +kernel` call to check a complete
140-entry certificate subtree. The replacement divides that existing subtree
into four 35-entry quarters, checks each quarter in a private theorem using
`decide +kernel`, and reassembles the original statement with Boolean equality.
The private theorems are opaque checked facts, so the final theorem can use
them without recomputing every entry in one kernel reduction.

The root shape equality unfolds only the two outer levels of the literal
`CTree`; the certificate values themselves are not copied or regenerated.
Every branch of the original finite check is included. No native evaluation
or new axiom declaration is used.
The function `fwdF` still checks successor entries against the complete
original `fwdCert`; taking quarters does not renumber or restrict those
successor lookups.

## Prior work and implementation evidence

This uses the existing quarter-block proof method already present in the
incoming normalized proposal and in
`automatic-certificates/lean_auto/BusyBeaver/ZFC/KSource215AutoCheck12.lean`.
It is an application of that existing method to four current production
proof modules, not a new mathematical certificate technique.

The installed Lean 4.32.0 source
`src/lean/Lean/Elab/Tactic/Decide.lean`, function `doKernel`, calls
`mkAuxLemma` with `Elab.async` set to false and returns the checked lemma
constant. Its comment explains that the added declaration avoids checking
the proof again. This supports dividing one large conversion task among
separate checked declarations. A command-line setting for asynchronous
elaboration would not remove this synchronous kernel reduction.

## Files and validation scope

- `../source/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/` preserves the exact four current proof modules in the bundled pinned snapshot.
- `BusyBeaver/ZFC/` contains their replacements at the same relative module paths.
- `quarter-batches.patch` applies the changes at repository-relative paths.
- `prior_work_and_construction.json` records source hashes, exact public statements, the prior
  implementation used as a template, and the inspected Lean source hash.

The original monolithic check of module 12 was killed with exit code 137
under the host's memory constraint. That resource failure is not a false
certificate or a mathematical counterexample. The baseline failure receipt
and the actual replacement-compilation/full-endpoint receipts are maintained
by the accompanying endpoint audit. All four replacement modules have now
compiled successfully with Lean 4.32.0 and the original `decide +kernel`
checking mechanism. The dependent `KSource215` module also compiled. The
corresponding source, object, log, and command records are retained under
`../evidence/baseline/`; `overlay_receipt.json` binds the four successful checks; the complete endpoint gate is recorded separately by the
endpoint audit. A patched endpoint build must be reported with its changed
proof sources disclosed.

| Replacement module | Compilation time |
|---|---:|
| `KSource215FwdCheck12` | 58.841 s |
| `KSource215FwdCheck13` | 60.177 s |
| `KSource215FwdCheck14` | 69.986 s |
| `KSource215FwdCheck15` | 59.496 s |

During those existing compiler invocations, sampling process memory every
0.25 seconds observed a largest process high-water mark of 2,403,745,792 bytes
(about 2.24 GiB). These sampled values are lower bounds on the process peaks,
not exact complete-process maximum measurements. The original failed attempt
and these successful replacements were run under the same host memory
constraint; this is evidence that this batching strategy made these concrete
checks practical in this environment, not a general complexity or timing
claim.
