# Current-base thirteen-variable build evidence map

The first guarded build ([README](README.md)) obtained seven predecessor
objects before the adapted carrier failed on the interpreter memory limit.
Its [attempt01 state](attempt01/state.json) and source/log snapshots record
the actual failure. The exact original five carrier imports passed the
separate [import-only probe](../thirteen-carrier-import-probe/README.md).

The source-only carrier split and guarded checks are separate packets:

- [Generic split core](../thirteen-current2011-carrier-split-draft/README.md):
  literal 13-coordinate syntax and generic replacement lemmas checked;
  the remaining un-factored model source failed at the memory limit.
- [Model prelude](../thirteen-current2011-carrier-model-prelude-diagnostic/README.md):
  fixed-port, positivity and shifted-coordinate helpers checked separately.
- [Ring invariants](../thirteen-current2011-core-invariants-draft/README.md):
  seven ring-image equalities extracted from completion and checked.
- [Rank ordinate](../thirteen-current2011-rank-ordinate-draft/README.md):
  maintained first-index consequence extracted and checked.
- [Factored completion and bridge](../thirteen-current2011-complete-factored-draft/README.md):
  unchanged theorem statements, two checked helper calls; compilation failed
  at the interpreter limit.
- [Completion alone](../thirteen-current2011-complete-only-draft/README.md):
  removing the later bridge and endpoint declarations still reached that
  limit. This diagnostic does not pinpoint a single failing tactic.

Each packet retains exact source hashes, direct guards, output/log evidence
and separately observed outer exits, within its documented provider and
monitoring limits. The 13-variable completion, model bridge and iPRA endpoint
have **not** been checked by this fresh-source path.

A subsequent [seed-construction extraction](../thirteen-current2011-seed-construction-draft/README.md)
reached its 180-second timeout without a proof or axiom report. It remains an
unchecked draft and has not been integrated into completion.
