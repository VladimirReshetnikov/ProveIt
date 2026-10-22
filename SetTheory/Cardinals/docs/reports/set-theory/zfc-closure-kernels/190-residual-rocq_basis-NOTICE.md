# Attribution and scope

This packet refactors the Rocq K215 implication proofs in Vladimir Reshetnikov's
ProveIt repository. The inherited 58-step derivation, generic language interface,
and K/Peirce exports are taken from the repository's earlier `shared-proof-core`
proposal. Its exact input digest and source URL are in `source-pins.json`.

The new work is the two-detachment S extension, adapters that share the core
between both live numerical proof developments, exact public-type comparisons,
fresh focused compiler/kernel checks, and synchronized K215 generation and
manifest overlay. The two-detachment S expression was found by the parent
research agent in this collaboration and independently checked here in Coq.
The 58-step underlying derivation is inherited work, not a new discovery.

`inputs/K215F` contains exact original ProveIt sources. `inputs/K230L` and
`inputs/K230S` contain exact sources from Elliot Glazer's pinned K230 proof
repository. The latter retain their original comments attributing Jeff's
numerical code calculus. No claim is made to relicense those inherited portions.
`licenses/K230-THIRD_PARTY.md` preserves the reference repository's full
license-scope statement, and its cited upstream notices are supplied beside it.
Those upstream components are not all dependencies of this focused packet.
`NOTICE.K215.md` is the inherited machine attribution, retained for context;
its historical cross-links refer to its original repository location.

New ProveIt material follows `LICENSE.ProveIt`. Coq/Rocq and its installed
standard library retain their own distribution terms. The complete K215
machine endpoint was not rebuilt for these changes. No state reduction or
unconditional nonhalting claim is made.
