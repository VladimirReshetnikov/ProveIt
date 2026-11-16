# AX11H second push and field prefix

The revised source has a second 19-row push at sites 3586–3604. The finite
row theorem checks that it is the previously verified inserted push with all
instruction destinations shifted forward by 33. `PA194AX11HSecondPushAdvance`
relates each actual candidate step to the corresponding primary push step,
and the paused paired-orbit modules extend this alignment to model-valued
execution lengths. `PA194AX11HSecondPushExact.revised_push_exact` proves the
actual candidate run reaches site 3605 with the entire exact pushed file.

`PA194AX11HDoublePushField.push_field_push` composes the inserted push, the
field reader and this second push: starting at site 3553 with zero X and Y,
it reaches site 3605 with the full file `pushed (fieldArgs (pushed a))`.
`output_values` gives its register coordinates. All statements hold in every
arithmetic `IΣ₁` model for arbitrary model-valued register contents. The
subsequent comparison/return branch and the complete machine correctness
are separate obligations.

For a source replay, supply a colon-separated LEAN_PATH file from checked
provider stages containing the candidate source, initial push and field
proofs, and the exact first-actual primary push theorem:

```sh
bash check-second-push.sh "$checked_provider_leanpath" "$new_output"
```

The output directory must be new. The script deduplicates the provider paths,
rebuilds all nine modules in dependency order, and audits their axioms. It
uses the supplied checked provider stages rather than rebuilding their full
transitive dependency closures.
