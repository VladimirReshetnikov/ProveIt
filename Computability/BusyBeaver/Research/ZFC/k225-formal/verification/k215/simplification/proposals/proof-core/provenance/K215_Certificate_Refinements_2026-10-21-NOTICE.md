# Provenance and contribution boundaries

Inspected repository:
https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `53269bcab1efc0f82d3022645bd7cf0c22d84959`.

The K215 machine, its complete correctness proofs and numerical-calculus/ZFC
calibration are inherited from the repository and its identified upstream
authors. This delivery does not claim authorship of those constructions.

The seven incoming archives are pinned by name and SHA-256 in
`zero_credit/incoming_inventory.json`. They already contain ordinary
zero-offset source proofs, offset symmetry, compact path encodings,
normalized source certificates, CM215/M124/FM215 transports, and structural
proposals. Those results are credited as prior work throughout the report.

New material in this packet consists of:

- balanced binary-index lookup and its refinement proof, with an exact
  current K215 source instance;
- the generic finite-table checker and soundness theorem for the two-marker
  family, and its three literal checked instances;
- explicit native/dense M125 files instantiating an already proposed provider;
- the concrete Cantor codec and exhaustive-prefix formalization of the
  already documented NIP-to-DROP injection;
- the restricted search implementation and run, independent audits,
  integration report, reproduction scripts and evidence packaging.

`balanced_lookup/` preserves the incoming path codec, compact certificate,
ordinary source proof and mirror proof; its `deps/` contains the minimal
inherited semantics and exact programs used by the new result. Corresponding
notices are in `balanced_lookup/licenses/`.

`marker_certificate/` preserves exact K215/M124/FM215 table bytes and the
relevant upstream notices and licenses. Its `NOTICE.md` records the detailed
table provenance. Provider 125 was explicitly mentioned by the earlier M124
note and is not presented as a new construction idea.

The ordinary credit injection is inherited from
`candidate-k215/alternatives/zero-credit/proofs/tag_lowering_credit.md`;
the earlier abstract formal prototype is in
`alternatives/gc-zc215/prefix_credit/PrefixCredit.v`.
`zero_credit/CantorCredit.v` is a new concrete formalization, not a claim to
discovery priority for the injection.

New report and code material is provided under the top-level MIT No
Attribution license for incorporation into ProveIt. Existing material
remains subject to its preserved licenses and notices.
