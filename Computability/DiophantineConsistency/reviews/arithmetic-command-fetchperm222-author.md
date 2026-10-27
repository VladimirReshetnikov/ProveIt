# Actual permuted fetch: author checkpoint

26 October2026. Root authored and fully read both leaves before compiling.
The new fixed Sigma1 graph codes the actual fetch pair: pl=0 reads raw np
and advances the candidate counter, while pl!=0 reads pl-1 and preserves
the counter. Its total unique internal evaluation under IOpen uses the
existing subtraction and Cantor graphs. Combined with the actual parser,
it proves `tail(raw)+1 <= pl` for a nonempty shifted pointer. Raw0 is still
executed at pl=1. The all-state Nat adapter is bound to `EnumPerm.fetch`.

The [author record](arithmetic-command-fetchperm222-replay.json) fixes102
reused modules (86 Foundation),37 direct package boundaries and619 recorded
observations. Two final fresh bounded commands pass, with an empty main
log and eight standard-only reports. No dependency or Foundation source
was compiled. The [durable bundle](arithmetic-command-fetchperm222-author-replay/FILES.json)
preserves all three earlier development runs: two failed Nat-subtraction
adapters, then a successful main with a failed Cantor-zero check. The final
Nat adapter cases on the actual list field and applies the already proved
internal successor identity. It does not identify choice-defined model
subtraction with Nat.sub by definitional equality.

The [independent peer](arithmetic-command-fetchperm222-peer.md) read both
sources and actual fetch, and separately compiled both in a new overlay.
Both final objects match the author's bytes and all eight reports are
standard-only. It verifies628 distinct pins and21 durable artifacts.
This is a fetch/progress prerequisite; complete enumeration, internal
proof soundness, current machine calibration and the HA endpoint remain open.
