# Recovery provenance and identity boundaries

The execution filesystem reset was observed at 01:03:27 UTC on 4 October 2026. The earlier complete science packet, Report44 release, and full QA directories were lost before Report44 was uploaded. This is a reconstructed edition, not a claim to have recovered the original enclosing archive.

## Exact objects recovered and freshly checked

- The 174-node history174.json matches its prior byte hash 2075bb290f3f81d7c04a27b82f50c4f492638d55a3a27f434f66497ae9fb90ea
- The recoder, endpoint, anchor and coefficient recipe read closure were restored from authenticated, previously delivered Report42/40 ZIPs. SOURCE_PINS.json and history/SOURCE_PINS.json record their byte checks
- Freshly generated complete canonical streams match the retained pre-reset audited SHA256 values:
  - Two input: c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac
  - One input: 85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a
- A newly authored independent parser also reconstructs and verifies those same stream digests, all references and domains, the counts, every SOS gate, the final assertion and a signed off-solution modular evaluation
- Fresh sparse homogeneous calculations certify both degree-1152000 leading terms as -W^1152000, giving final leading part 2W^2304000
- Fresh history exact polynomial, finite-history and mutation checks have been rerun. Finite histories remain regression evidence rather than the general positive-domain theorem

## New bytes and new pins

The recovered merged_source.py is a new implementation file, SHA256 eafe92d6e57782347f430a4f1d6ea5693bd6a48300d2db0294b3ab7026b96395. It is not claimed to match the lost implementation file hash 5ae0f89fe1366e06a4f24b6e2c8d47fb5680f9a2ba0c82bcfc829dd887f63def. The identical arithmetic streams nevertheless show that its emitted source is unchanged.

Proof prose, helper implementations, receipts with recovery metadata, current audits, enclosing manifest and archive have new byte identities. The old science manifest 99032e3b73365abe00b77fb93348088ef8d2fece709b5d9da3fe5c183dc71d9d and old science ZIP d6ffde78a3f77b200a816a881d023d4a663199b6c5ea063eba072684de7b380c are historical references only. They must not be used to authenticate this recovered edition.

No lost screenshot, full old audit log or old checker is represented as recovered merely because a summary survived. Current audit files identify newly rerun checks explicitly. Primary input orientation was rechecked from the public PDF; its recovered note distinguishes the historical local PDF digest from the new web inspection.

## Execution boundary

Only newly authored or reconstructed own checking/generation code and normal local tooling execute. Upstream Python/Lean, saved upstream schedules, atlas and physical-program recipes remain read-only data. The astronomical literal 1/3 coefficient prefix is specified, never expanded or run. Authenticated delivered Report40/42 directories remain unchanged.
