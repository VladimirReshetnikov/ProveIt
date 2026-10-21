# Independent review of the framed decoder certificate

Reviewed files: `FramedWindow.lean`, `DecoderCertificate.lean`,
`generate_data.py`, and generated `K215Decoder.lean`. File hashes are recorded
in `evidence.json`. This is a source/data review and an independently implemented
ordinary Python check. It does not add a separate Lean compilation claim.

## Assessment

No soundness defect was found in the generic arbitrary-tape execution theorem
or in the newly added finite `Chain` composition theorem. The appropriate
positive claim is:

> Every block in the checked 281-block list, at every integer head position,
> has a positive-duration execution to its stated exit, moves the head one
> cell right, and restores the entire tape, provided the explicitly stated
> local word is present. Any finite certified chain whose boundary windows
> are supplied has the composed execution on the same arbitrary tape.

The theorem permits arbitrary tape contents outside the finite word. A local
step cannot inspect an unspecified cell: `lookup = none` makes it fail. Every
write updates a present cell, and `overlay_put` proves exact agreement with a
full-tape write. Equality with the complete original local list at the end
implies whole-tape restoration, including the untouched exterior.

Duplicate entries in the generic `Cells` type do not invalidate the theorem.
Both lookup and put use the first matching entry; later duplicates are
shadowed. The input premise uses that exact effective overlay. Generated
`cells word` has distinct consecutive coordinates anyway. Documentation should
not interpret a generic list with contradictory duplicates as a conjunction
of all listed equalities: the semantics is explicitly first-match.

The translated theorem is correct for arbitrary integer origins. `Chain`
keeps the same tape throughout because each component restores it; induction
and `run_add` compose the runs. A `Chain` witness explicitly supplies each
window premise. No theorem currently constructs this witness automatically
from an arbitrary source path.

## Exact independent data check

`audit_decoder.py` imports no generator code. It independently parses the Lean
literal arrays, checks the 430 actions against the pinned native table, checks
all 202 source nodes and all 234 role records against the input certificate,
expands the source to all 4,751 pinned primitive occurrences, and reruns all
281 local blocks using partial-tape semantics. It also checks target closure
and 215 working states. All 234 roles are reachable from role zero in the
concrete certificate. The literal product contains 371 internal edges and
97 primitive edges.

The 281 minimal windows have widths 1, 2, 3 in counts 252, 25, 4. The independent
replay passes for every block.

## Structural checker boundary

`structuralCheck = true` must be used together with `all_blocks_checked`.
The structural predicate alone does not verify execution or positive duration.
This is deliberate separation rather than a flaw in `block_sound`.

The current structural predicate checks the root role, suffix lengths,
child-node decrease, edge types, exact primitive transition actions, internal
role/node/suffix links, and matching block entry/exit/suffix. It does not prove:

- a semantic correspondence between a leaf's opcode/argument and the primitive
  routine that its table action enters;
- the semantic decoder theorem relating arbitrary source paths, actual tape
  bits and role windows;
- identity with the repository's in-kernel `KSource215` program;
- universal arithmetic primitive contracts, startup, or the ZFC endpoint;
- role uniqueness or root reachability, although the independent check confirms
  full reachability for the concrete 234-role data;
- state/target closure by itself, although the separate literal-table check
  confirms the concrete table has the required closure.

Changing a leaf's argument does not affect `structuralCheck`, because primitive
leaves are matched as `.leaf _ _`. This confirms that the predicate establishes
an exact action binding, not the leaf operation's semantics. The generator's
expansion equality with `sites215.json` is an ordinary independently replayable
artifact binding, not an in-kernel equality theorem to the upstream source.

## Malformed controls independently replayed

All four mutation families below were tested on all 281 blocks:

| Mutation | Rejected | Reason |
|---|---:|---|
| Delete the leftmost supplied cell | 281/281 | 252 empty windows; 29 unspecified exterior reads |
| Replace the expected exit by 999 | 281/281 | Wrong exit |
| Reduce the duration by one | 281/281 | 252 nonpositive durations; 29 wrong exits |
| Set the duration to zero | 281/281 | Nonpositive duration |

Flipping the first block's scanned bit also gives a wrong-exit rejection.
These are ordinary independent controls, not additional Lean theorems.

Seven structural mutations are rejected: empty root suffix, wrong root state,
out-of-range target role, out-of-range block index, a nondecreasing root child,
a wrong primitive action, and a wrong primitive-node binding.

Three explicit controls are *accepted* by structure alone, as expected:
zero block duration, modified leaf argument, and a duplicate role. They make
the boundary visible and prevent future reports from silently attributing
more semantics to `structure_checked` than its definition supplies. Zero
duration is rejected by the separate block checker; the other two do not
invalidate the local block theorem.

## Reproduction

From this review directory:

```sh
python3 audit_decoder.py /path/to/decoder_component --out /tmp/decoder-audit.json
```

The root contains `inputs/`, `generation.json` and the four reviewed sources.
The checker does not modify them. Its input hashes and complete results are
in `evidence.json`.
