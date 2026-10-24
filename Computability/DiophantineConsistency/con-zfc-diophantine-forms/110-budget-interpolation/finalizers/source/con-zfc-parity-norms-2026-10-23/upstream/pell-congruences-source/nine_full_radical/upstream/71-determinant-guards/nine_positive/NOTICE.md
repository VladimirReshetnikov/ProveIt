# Attribution and proof scope

This new composition was prepared with AI assistance for Vladimir Reshetnikov's
ProveIt project,23 October2026. It composes mathematical components from the
same repository, pinned at9cca523d9f27ad39d52993f4065cbd7e58f8bdd4.

- Shared coefficient positions, source layout and source proof:package65.
- Deflated seventh-order root majorant and264-term certificate:package63.
- Shared addition-chain rewrite:package62.
- Free positive-coordinate finalizer:package59 and its named predecessors.
- Original31 fixed native tuple and reconstruction:package31.
- K215 transition input and inherited native/compiler/calibration proofs:
  their original authors and repository notices remain applicable.

`circuit.py` and `rewrite_powers.py` retain the source code's original text.
`build_composed.py` adapts65's source builder and63's majorant builder.
`check_majorant.py` adapts63's exact checker to the new weighted degree.
`check_composed.py` retains65's exact source audit and adds a composition
checker. `PROVENANCE.json` records original paths and copied-byte hashes.

New files are offered under MIT-0, matching the included repository license.
The coefficient subtree also retains `LICENSE.Wade` and `NOTICE-K215.md`.

The mathematical proof is an ordinary composition of explicitly named
theorems formalizable in ZFC. The finite checks certify fixed data and
polynomial identities; they do not prove the unbounded semantic statements
by experimentation. No new end-to-end Lean/Rocq or object-language ZFC
derivation is supplied. Independent verification here refers to separate
code paths, not external human peer review.
