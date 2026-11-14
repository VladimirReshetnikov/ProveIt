# Provenance and attribution

The frozen source repository is
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/17f92105e2bc4317feae6c219cb2143437b482ff),
commit `17f92105e2bc4317feae6c219cb2143437b482ff`.
All corpus and historical-status claims refer to this snapshot.

## Supplied components

The imported PA196 register engine, source tree, axiom macro sources and
transition table are retained under `construction/reference/`. The builder
adapts the supplied PA194 compiler and symmetric cached-controller composition.
The frozen primary grammar and fold list come from the original PA194
67-reader/seven-fold construction.

The PA194CS baseline native table, sites and resolved instructions are preserved
under `inputs/`. Their origin is the `secondary/pa194CS` component of the
supplied `pa194_new_designs_2026-11-13.zip` packet. The baseline native hash is:

    00446d08d3c35909a11460a9e19507d53e8526ad822b94ce9a04c73951eb447b

The literal symbolic runtime and independent source resolvers are under
`verification/reference/`. Its README retains the upstream packet attribution
and historical source revision. The current wrappers set the header base and
physical-register mapping and rederive the four list lemmas against each
literal candidate. They do not import the construction compiler or use its
arithmetic-box oracle.

The original proof fragments in `references/` are unchanged copies. Their
exact SHA-256 values and all identical matches found in the pinned PA tree
and unpacked incoming archives are in `references/provenance.json`.
Historical relative paths inside those texts identify their original packets;
they are not dependencies of `report/main.tex`.

The complete cached-calibration fragment comes from
`pa194C_conpa_2026-11-13 (2).zip`. The cached and symmetric preservation
fragments come from `pa194_new_designs_2026-11-13.zip`. The earlier diagonal,
separate-head and PA195 calibration fragments are retained to make the
logical dependency chain inspectable.

The known-zero closing operation itself is prior work: see
`Computability/BusyBeaver/Research/PA/docs/pa_consistency_comparison_and_new196_2026-11-13/engine/TRIT_CONTEXTS.md`,
the section on the four register-3/4/5/6 closing variants. Cached Shift/MP and
the symmetric equality guard are also supplied prior designs.

## New work in this package

- Four new literal 194-state compositions, including the substantially
  reassociated PA194R decoder.
- Portable reconstruction wrappers and frozen new grammar/fold inputs.
- A four-site source invariant for the final-X change, with an independent
  finite premise checker, and small cuts for the entry-jump variants.
- New complete literal-check wrappers and receipts for all four tables.
- A recursive corpus inventory, graph-canonicalization comparisons and the
  41-packet architectural ledger.
- Joint local quotient synthesizers allowing repeated visits to the retained
  modified control, two-sided convergence probes, and bounded grammar screens.
- A report separating successful constructions, failed candidates, inherited
  ordinary calibration and uncompleted formal endpoints.

PA194R's association was recovered from a saved 194-cost plateau grammar and
then combined with the final-zero word and symmetric controller. Its discovery
input, sharing metrics, fold certificates and full reconstruction are retained
in the research and machine directories. A search score alone was never treated
as an accepted table.

## Proof and execution boundary

The ordinary mathematical calibration is inherited, restated and audited in
the report. The new source preservation arguments are proved there. Literal
bindings use inspected symbolic rules and finite Python checks. This is not a
new independent implementation of a PA proof-code compiler, an end-to-end
Lean/Rocq theorem, or an iPRA consistency-equivalence endpoint.

The finite trace in `research/rejected103/` is intentionally a counterexample
to a proposed startup-preserving edit; it is not an accepted machine.
Other experiment receipts preserve their exact bounds and failure status.

Original license texts are retained in `licenses/` and beside the imported
runtime. These wrappers and reports do not relicense the imported work.
