# Attribution and provenance

Prepared for Vladimir Reshetnikov and the ProveIt project, 19 October 2026.

The compact logical calculus, native set theory, register source and original
254-state binary machine remain credited to **Mira-Cult**. The upstream
Rocq verification and consistency calibration remain credited to **Jeff
Ketchersid and contributors**. The compiler framework remains credited to
**Andrew James Wade**. ProveIt contributors and preceding incoming work
retain credit for all inherited state reductions, routing and initialization
changes, source calibrations, and proof infrastructure.

The inspected ProveIt checkpoint is
`ce192939372ac7944fe2a0208c68a96d49fb5e3b`. The relevant incoming archives
were added at `83fd3585484e5dffb37992f91f7dd4d3e70c437a`. The inherited
source-to-consistency calibration is identified at
`13ec39ed43148b1807f51ed6e6528e1c84659562`.

Two prior 239-state constructions are used:

- `BusyBeaver239_Research_2026-10-19.zip` and
  `ZFC239_Companion_2026-10-19.zip` contain the same delayed-erasure machine,
  with deletion of inherited state `169`.
- `ZFC_239_State_Construction_2026-10-19.zip` supplies the distinct source
  boundary regrouping, decoder-context split, and deletion of state `218`.

Their full original attribution files, archive URLs and hashes are retained
under `reference/`. Statements in historical notices concern their original
packages, paths and dates. They are not fresh claims about this construction.

This submission contributes the literal **238-state composition**, exact
two-recipe reconstruction, inspection of all compatibility dependencies,
whole-tape local certificate, fresh unbounded selector-guard proof on the
changed source, direct unbounded final runtime instantiation, independent
sparse/dense initialization checker, source-interface replay, new six-valued
logical-basis obstruction, mathematical report and portable package.

The general symbolic runtime proof rules are inherited. The delivered
`verification/symbolic_runtime.py`, `independent_runtime.py`, and
`check_literal_runtime.py` are byte-identical to the corresponding files in
the boundary239 incoming construction. Its adapter provenance is preserved
as `reference/runtime_adapter_provenance.json`; the present fresh runtime
receipt binds those exact hashes to the new machine and source. Reusing
those rules is distinguished from freshly replaying them on the 238-state
table. The separate new local and bootstrap checkers provide additional
verification paths.

No historical priority claim is made for associativity, delayed erasure,
context-dependent state sharing, finite many-valued counterinterpretations,
or the standard model-theoretic comparisons discussed in the report. The
new concrete composition is distinguished from its two 239-state parents.
The report does not assert a global state minimum or an exhaustive search.

New research text, code and certificates were generated with ChatGPT for the
user's requested incorporation into ProveIt. No additional restrictions are
asserted over the newly prepared material. The inherited ProveIt MIT No
Attribution terms, Wade license and associated notices are preserved under
`licenses/`; inherited material remains subject to its applicable terms.

The mathematical proof is intended to be formalizable in ZFC. The delivered
evidence does **not** include a newly compiled proof-assistant endpoint for
the exact 238-state table, a fresh ancestor-library rebuild, or a serialized
internal PA proof. `research_status.json` records those distinctions.
