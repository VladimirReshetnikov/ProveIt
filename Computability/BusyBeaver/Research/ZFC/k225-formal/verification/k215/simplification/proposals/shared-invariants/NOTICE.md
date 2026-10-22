# Provenance and scope

This research packet was prepared for incorporation in Vladimir
Reshetnikov's ProveIt repository. New material is licensed under the repository's
MIT No Attribution terms; see `LICENSE`. Copied sources retain their original
licenses, including the separately supplied BusyCoq license.

The reviewed production snapshot is:

`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`

Sources copied from the project retain their existing comments and names.
The file inventories and component manifests record their repository paths,
source commits, and hashes. The main prior proposal sources are:

- The shared six-goal implication core and unrestricted adapter from
  `49e99c5b7cc6c2e164331961de28bad3904361fd`.
- The checked `k215-transport` positive-stuttering prototype and the
  `further-simplifications/terminal_contract` finite-cleanup proposal.
- The `proof-contracts` semantic runtime interface and prefix/suffix
  composition, and the `sharing-interfaces` residual audit.
- The existing `rho8cd` Rocq source replacements, which are recommended for
  adoption but are not presented as new proofs in this packet.

New contributions include the smaller dense-bridge induction, checked
finite-cleanup adaptations and boundary examples, an exact computable
decoder-port attachment, and source-bound component validation and reporting.
The report distinguishes these from prior work and from remaining
production integration.

No production repository file, transition table, or machine state count
was changed while preparing the packet. The complete Lean/Rocq
machine-to-ZFC endpoint was not freshly rebuilt. No internally encoded PA
or ZFC derivation is supplied, and no unconditional non-halting claim is
made. See the report's validation ledger and the component receipts for
the precise successful checks and any experimental limitations.
