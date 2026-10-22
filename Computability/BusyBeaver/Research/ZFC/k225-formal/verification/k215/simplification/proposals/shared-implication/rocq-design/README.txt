STATUS: UNCOMPILED DESIGN DRAFT

SemanticSites.proposal.v was reviewed against the pinned K215 Rocq source.
No Rocq compiler ran on this file. Its proof scripts are a proposed interface
adapter, not kernel evidence. It also does not edit Sim230's consumers.

The intended integration preserves the full padded consumed word, r < 9,
length <= 48, both decrement branches, exact overflow/growth targets and
strict physical progress. RunSpec uses -->+, since the reverse-halting proof
depends on progress_halts. Prefix decoding may use zero-or-more steps.

Adapt inv_view to return EdgeSpec; adapt inv_step and inv_halt to eliminate
the semantic specification. Keep the public machine/program endpoint and
invariant unchanged. Then compile the affected closure, inspect assumptions
and run the repository's endpoint and recursive coqchk gates.

