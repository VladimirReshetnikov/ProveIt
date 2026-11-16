# First actual primary field output for AX11H

`PA194PausedWalkerRound` and `PA194PausedWalkerLoop` prove the Cantor
walker arithmetic under any transition code agreeing with the primary step
below its stopping boundary. `PA194PausedReader` composes that walker with
boundary-safe register drains and proves the complete fourteen-row reader
output, for arbitrary model-valued register contents.

`PA194FirstActualField.first_actual_field` specializes the reader to the
primary field code frozen at site 3568 and uses the checked first-hit bridge.
In every PRA model whose arithmetic reduct satisfies `IΣ₁`, start at
primary site 3554 with X=Y=0. The first actual exit at site 3568 has the
entire `fieldArgs` file. The [revised field proof](README-candidate.md)
uses this primary result to identify the revised source output.

After running `check-paused-primary.sh`, source-replay this stage with:

```sh
bash check-paused-field.sh "$checked_paused_primary" "$new_output"
```

The output directory must be new. The script rebuilds the three generic
walker/reader modules and the first-field theorem in order and checks their
axiom audits. The supplied checked stage furnishes the transitive dependencies.
