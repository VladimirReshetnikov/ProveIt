# Ordinary AX11H MP source command

`PA194AX11HCompareExit.compareAndReturn` extends the checked candidate
comparison to arbitrary model-valued files: it returns from site 3642 to
site 25, clearing H and X and adding D to T exactly on the H=X branch.
In particular, it handles equality with nonzero D; the separately proved
AX fall-through shortcut needs no such general copy.

`PA194AX11HMPPrep.mp_to_compare` composes the field reader, second push and
comparison preparation for ordinary MP. `PA194AX11HMPSource.mp_source` then
proves the whole revised source command from MP entry site 3572 to dispatch
site 25 with its exact no-push MP register file. The proof applies in each
arithmetic `IΣ₁` model to arbitrary model-valued contents when X=Y=0.
It does not itself establish scheduler fetch/dispatch into the MP entry.

Replay from a colon-separated checked-provider LEAN_PATH file containing the
candidate source, comparison/return stage, field and second-push proofs, and
preparation stage:

```sh
bash check-mp-source.sh "$checked_provider_leanpath" "$new_output"
```

The output directory must be new. The script rebuilds nine modules in order,
deduplicates the provider list, and audits their axioms; it relies on the
supplied checked stages for its remaining transitive dependencies.
