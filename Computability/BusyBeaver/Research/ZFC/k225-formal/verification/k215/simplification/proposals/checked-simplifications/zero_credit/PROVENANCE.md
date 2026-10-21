# Provenance and status

Repository inspection pin: `53269bcab1efc0f82d3022645bd7cf0c22d84959`.

The tag-lowering idea, command tags/fields, and zero-credit argument are inherited from
`Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/zero-credit/proofs/tag_lowering_credit.md`.
The finite-injection counting proof is adapted from the previously uncompiled
`candidate-k215/alternatives/gc-zc215/prefix_credit/PrefixCredit.v`.
The new contribution is `TagLowering.v`: a self-contained, standard-library Coq
formalization of the *concrete* Cantor codec, its parser and inverses, the
lowering map and injectivity, the entire finite-prefix credit inequality, and
strict positive credit immediately before NIP. It is not an invented new
scheduler or a new 215-state construction.

The exact M124 input comes from incoming packet
`ZFC215_Proof_Simplification_2026-10-21/m124_rocq/machine.native.tm`.
The bytes are also verified identical to the current pinned repository file
`candidate-k215/alternatives/dr215/markers/marker_family/m124/machine.native.tm`
(SHA-256 `8e0ccb4b631c4e4c1c02c4b52a6fe382984e67557dd1dcd949065479e38d07b9`).
The exact FM215 input comes from
`zfc-fm215-proof-compression-2026-10-21/machine/fm215.native.tm`.
Their ordinary marker arguments and existing standalone proof-assistant
certificates belong to those packets. This work contributes only the exact
comparison and correction of their potential conflation. Each has 215 working
states; they differ at exactly one native row and are not rooted graph
isomorphic, even with global left/right reflection.

New proof/checker material follows the repository's MIT No Attribution terms,
reproduced in LICENSE.ProveIt. No blanket relicensing of inherited third-party
proof developments is intended. Neither full upstream proof closure nor any
large inherited data archive is republished here.
