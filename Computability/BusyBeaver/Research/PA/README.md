# PA consistency machines

This directory contains machine tables, imported research, and Lean proofs
concerning small Turing machines associated with the consistency of Peano
arithmetic, `Con(PA)`. The current goal is a Lean proof of
`iPRA ⊢ Con(PA) ↔ ¬Halt(M)` for the primary 194-state candidate, followed
by the 195- and 196-state consistency candidates. The machines start
on a blank two-way binary tape; state counts exclude the halt state.

**Status:** Neither machine-specific direction of this equivalence has yet
been established in iPRA for PA194, the original PA195, or the PA196 candidate. In
particular, a Lean theorem about ordinary finite runs, a Python certificate,
and a conditional iPRA theorem are not themselves an iPRA proof of the
consistency equivalence. See the individual READMEs for assumptions, exact
statements, and reproducibility instructions.

## Primary 194-state candidate

The target table is `pa194_conpa/construction/tables/pa194.tm` in
[the PA194 research packet](../../../../docs/incoming/pa194_conpa_2026-11-13.zip).
It has 194 working states, start state 0, halt label 194, and 388 transitions.
Its SHA-256 is
`4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`.
The packet reports a PA-provable consistency equivalence and proposes a
second 194-state table; it does not provide an end-to-end Lean proof or an
iPRA proof. The primary table is a seven-fold quotient of a 201-control
parent with a ten-entry source interface. The arithmetic and simulation
results below provide reusable methods but do not by themselves establish
the PA194 equivalence.

[The PA194 arithmetic endpoint](pa194/ipra/README.md) binds the pinned table
to a standard-model halting sentence and constructs a conditional iPRA
equivalence. Both machine-specific reductions remain unproved.

## Original 195-state candidate

The target table is `pa195_conpa/pa195/pa195.tm` in
[the PA195 research packet](../../../../docs/incoming/pa195_conpa_2026-11-13.zip).
It has 195 working states, start state 0, halt label 195, and 390 transitions.
The table's SHA-256 is
`5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455`.
The packet claims a PA-provable consistency equivalence; it does not supply
an end-to-end Lean proof of that claim or an iPRA proof.

- [PA195 arithmetic endpoint](pa195/ipra/README.md) binds the table to a
  primitive-recursive halting test and an iPRA sentence in the standard
  model. Its equivalence theorem assumes two machine-specific classical PRA
  reductions; those assumptions remain open.
- [Quotient and dense-table proof](pa195-dense/README.md) proves in Lean that
  the 202-control parent and the delivered dense 195-state table halt under
  the same circumstances for every complete tape and head position.
  [The zipper bridge](pa195-zip-bridge/README.md) connects blank-tape
  halting to the arithmetic endpoint over the standard natural numbers.
- [Register engine](pa195-runtime/README.md),
  [source entry binding](pa195-source-entry/README.md), and
  [symbolic contract batches](pa195-symbolic/README.md) check parts of the
  parent machine's execution. The entry binding covers one source instruction
  and both branches; the complete source-graph and arithmetic correctness
  connections still need proof.
- [Explicit machine codes](pa195/ipra/machine-code/README.md) develop tape,
  transition-table, and configuration-step functions in the PRA language.
  Their model equations are ingredients for a weak-arithmetic proof, not the
  missing machine/refutation reductions.
- [Diagonal calibration](pa195-calibration/README.md) proves immediate
  formula-code descent in classical PRA, including nonstandard models.
  Recursive freshness and the proof-producing translation remain open.

## Other machines and related work

[James Chang's imported snapshots](jamesyc-upstream/README.md) contain the
upstream PA196 and PA209 developments. The imported PA196 result includes a
PA proof of the implication from literal nonhalting to PA consistency; this
alone does not establish the converse in PA or either direction in iPRA.
[PA196 versus U208](pa196-vs-u208/ipra/README.md) documents the PA196
arithmetic endpoint, conditional transfers, and the completed PA-refutation
witness certificate. The machine-specific reductions remain open.
[The archive audit](pa196-vs-u208/archive-audit/README.md) inventories related
196-state tables and distinguishes candidates from rejected machines.

[The later PA195 packet](../../../../docs/incoming/PA195_ConPA_research_2026-11-14.zip)
contains two further 195-state candidates, `machine_195S.tm` and
`machine_195C.tm`, along with source and physical execution certificates.
They are distinct from the original PA195 table. The packet gives mathematical
and executable evidence, not an end-to-end Lean proof of the desired iPRA
statement.

[The PA195 follow-up packet](../../../../docs/incoming/pa195_followup_research.zip)
contains another 195-state candidate, `M195S8`, and a claimed halting
equivalence with the original PA195. It also contains a rejected 194-state
construction. [A later PA194 packet](../../../../docs/incoming/pa194_conpa_2026-11-13.zip)
proposes two other 194-state candidates and claims a PA-provable equivalence.
These packets do not supply an end-to-end Lean proof of the iPRA statement.
