# Revised AX11H push and field reader

The revised source proofs hold in PRA models whose arithmetic reduct
satisfies `IΣ₁`. The initial register file is model-valued and its scratch
registers 6 and 7 start at zero.

- [`revised_push_exact`](PA194AX11HPushExact.lean) takes the actual
  candidate source run from site 3553 to 3572 with the complete
  `PA194ModelMPPush.pushed` file. The proof checks the 19 relocated
  instructions and transports the exact primary first-exit result.
- [`revised_field_exact`](PA194AX11HFieldExact.lean) takes the candidate
  from site 3572 to 3586 with its exact `PA194ModelMPField.fieldArgs` file.
- [`push_then_field`](PA194AX11HPushField.lean) composes the two runs and
  establishes the complete `fieldArgs (pushed a)` file at site 3586.

The remaining work covers the rest of MP, the connection between the source
and scheduler, and the literal-machine simulation.

The generators pin the delivered primary and revised input JSON by SHA-256
and reproduce the three checked-in generated Lean modules byte-for-byte.
Lean checks the declared instructions against the resolved primary trie and
the generated candidate program.

Run the repository-source push and field stages using a checked base
`LEAN_PATH` file for Foundation and the primary PA194 dependencies.

```sh
ax=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h
bash "$ax/check_candidate.sh" "$candidate_output" "$base_leanpath"
bash "$ax/check-paused-field.sh" "$candidate_output" "$primary_field_output"
bash "$ax/check_candidate_field.sh" "$field_output" "$candidate_output" "$primary_field_output"
```

The push stage rebuilds the local candidate chain and the
[paused primary push](README-paused-primary.md). The second command builds
the [primary field result](README-paused-field.md). The checkers audit the
Lean axioms and record the source hashes and provider paths for replay.

The [gate-window stage](README-gate.md) compares the revised and primary source
steps at sites 3519–3552 and identifies the sole gate exit at site 3553.

`PA194AX11HThroughPrep.through_prep` continues the exact revised AX-tail execution from site 3553 to the comparison input at site 3642. Under the same scratch-register and model assumptions, the endpoint is the complete file `PA194PausedPrep.result (pushed (fieldArgs (pushed a))) 0 (cantor (a 1) (a 2))`. `PA194AX11HThroughPrepValues.output_values` gives its relevant coordinates: T=0, W=`cantor (a 1) (a 2)`, D=`a 4 + fixedFirst(a 8)`, H=`a 5`, X=`impValue 0 D`, Y=0, and the remaining proof stream is `fixedSecond(a 8)`; register 3 is retained. The construction composes the two relocated pushes, field reader, D-copy, implication builder, and comparison setup. The comparison/return branch, complete source-to-scheduler simulation, and literal-machine simulation are separate obligations.

After building the separately documented second-push/double-push prerequisite, rebuild this preparation stage with:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/check_candidate_prep.sh \
  /path/to/fresh/prep-output /path/to/double-push-output
```

The preparation checker regenerates the 37-row source slice from the hash-pinned primary and revised JSONs, checks it byte for byte against the reviewable Lean source, compiles all 17 local modules in a fresh output, and rechecks the source and direct-provider object hashes. It retains the transitive paths recorded by the double-push prerequisite; it does not rebuild the primary/Foundation baseline.
