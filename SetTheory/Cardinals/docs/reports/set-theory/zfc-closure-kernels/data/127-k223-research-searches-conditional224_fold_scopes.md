# Conditional224 contextual search checkpoint

Stopped at the parent's request after discovery of the 223-state machine.
`REPORT.json` distinguishes completed negative screens from interrupted jobs.
No result here implies global minimality. The original224 report in `../folds`
was preserved unchanged.

Both conditional224 inputs completed ordinary, offset, adjacent-tag,
halt-aware, caller-plus-neutral-helper, neutral-repair-walk, and bounded
non-neutral-helper screens without a surviving reduction candidate. The
ordinary/offset/tag/halt screens used radius6/fuel65. Caller/helper screens
used radius5/fuel65, with caps documented in the original scanner sources.
The non-neutral-helper family covers the 210 pairs of self-looping states;
44 pairs had both ordinary partial branch solutions. Each basis tested 437
row combinations and 948,024 arbitrary helper edits, with no cap reached.
It jointly validates both merged-state contracts and the edited helper's
contract. Its synthetic control passes 400 reachable whole-tape contracts,
while the merge and helper fail the specified contracts separately.

Both source-relative radius6 projectors were stopped at hash-bound atomic
checkpoints. These are incomplete and must not be used as source-domain
certificates. Offset-plus-tag completed for variant 0 and was interrupted for
variant 1. Caller-only deletion
families later in the queue were not launched. The broad initial non-neutral
experiment was interrupted and superseded by the completed self-loop-pair
family; its partial log is not a complete negative result.

Fresh invariant/startup fixtures used for the partial projections were
independently checked per exact conditional source and table. They were not
copied by ordinal from the original source.

The exact 223 construction's independent audit is in
`../verify223_contextual`, separate from these negative search artifacts.
