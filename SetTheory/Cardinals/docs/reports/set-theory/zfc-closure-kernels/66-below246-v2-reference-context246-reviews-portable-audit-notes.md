# Prefix246 portable verifier

This directory is ready to use as the code, machine, source, and evidence
skeleton for the final research archive. Run from this directory:

```sh
python3 -B code/verify_all.py
```

The command requires only Python's standard library, assertions enabled, and
the retained files in this directory. It performs no network requests and
does not import from the outside ProveIt checkout or another incoming archive.

## Exact machine

Starting with the supplied Prefix250 original-label table, delete states
`0, 1, 3, 97`, replace the two rows below, and select start state `95`.

| Read row | New action |
|---|---|
| `60 0` | `0 R 20` |
| `255 0` | `1 L 255` |

All other retained rows stay identical. State `254` is the separate halt.
The resulting table has 246 working states and 492 rows. The generator derives
the identical bytes directly from the pinned permutation252 source table.

| File | SHA-256 |
|---|---|
| `machine/zfc_prefix246_old.tm` | `303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee` |
| `machine/zfc_prefix246.tm` | `89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc` |

The canonical start is 0, and the canonical halt is 246. Renumbering is stored
in `machine/renumbering.json`.

## Meaning of the verification results

The unchanged `check_macro_inductions.py` establishes four one-block symbolic
identities, three whole register macro contracts, and all nine marking
contracts by explicit induction templates. Its quantified unary lengths and
finite block lists are unbounded. The execution rules are literal table
transitions, self-loop induction, structural list induction, and ordinary word
identities. It is a small mathematical proof checker, not a Lean or Rocq kernel.

The full-PC checker tokenizes the complete `Prog254.v` table without skipping
unrecognized text, checks the complete rooted tree, derives all 6,460 leaves,
and executes all 8,391 guarded instruction cases. It preserves the entire
successor PC, including trailing zeros and overflow. Its 342 oracle checks
also reject absent or wrong-register decrement guards.

The blank bootstrap checker directly executes both table numberings for
410,735 transitions. Both terminate that finite prefix at an empty-PC frame
with head -5, marker -6, header 176, gap 181, physical primary registers
`[0,0,0,3,0,0,3,0,0]`, and 167 value-one spares. Exactly 351 cells contain 1;
every other cell contains 0. The logical register order is
`[N,T,W,A,D,H,X,Y,L] = [3,0,0,0,3,0,0,0,0]`.

The inherited calibration specialization is
`DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0`, followed by the existing
register-machine, native-theory, ZF, and ZFC refutation comparisons. This
directory supplies the new finite and symbolic machine checks; the final
report must explain the inherited mathematical calibration and its proof
status accurately.

The remaining tests are independent finite corroboration: 33,564 literal
instruction cases (14,197,744 individual transitions), 16,200 complete-frame
exact-time macro cases, and 3,600 register-box regressions. Their successful
sampling is not substituted for the universal induction arguments.

## Code provenance

`check_macro_inductions.py` is copied byte for byte from the supplied
`zfc-prefix250-audit-20261017/zfc-prefix250-report` contribution. Its imported
`rebuild_machines` interface now produces the exact 246-state table.

`review_affine_source.py` comes from that same audit. Its execution and source
parsing semantics are unchanged; only its description, exact table SHA-256,
and asserted row count have been updated. Its retained source pin describes
the historical audit snapshot of the same immutable `Prog254.v` blob.

`sources/prior/prefix_affine.py` and
`sources/prior/instruction-sites-physical.json` are retained byte for byte
from that audit. Their hashes are recorded by the source review result.

`check_literal_instructions.py`, `check_local_contracts.py`, and
`check_prefix_boxes.py` are adapted from the supplied Prefix250 contribution.
The adaptations set the new paths/imports and handle the absence of state97;
the literal transition rules, painters, expected macro effects, and test
domains remain unchanged.

`rebuild_machines.py`, `check_bootstrap.py`, and `verify_all.py` are new adapters
for this contribution. Original machine/calculus/compiler attribution remains
in `sources/README.upstream-attribution.md`; the final archive should retain
the upstream notices and licenses supplied with the research inputs.
