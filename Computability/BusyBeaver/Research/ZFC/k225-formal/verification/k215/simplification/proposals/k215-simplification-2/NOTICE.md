# Attribution and scope of new contributions

This packet was prepared for Vladimir Reshetnikov's ProveIt project. Existing
K215, CM215 and other candidate transition tables, the existing ZFC calibration,
and all pre-existing proof simplifications are credited to their upstream
authors. CM215's six-row construction predates this packet. The report explicitly
distinguishes existing work from the newly checked transfer and prototypes.

The ProveIt snapshot is
`b6c7087477e51c017003bd729e712c8969733223`.
Its MIT No Attribution license is retained as `LICENSE.ProveIt`. New exposition,
proofs and helper scripts in this packet are supplied for incorporation under
those same terms, subject to the separate retained notices for upstream material.

The Rocq symmetry proof imports generic definitions from Elliot Glazer's
`k230-rocq` at commit `3142e4dd980f0be12f4abb636c4ae2528afc17eb`.
Their exact two-file hashes are in `coq/upstream-pins.json`; those upstream
sources are not redistributed in this packet. `coq/UPSTREAM-NOTICE.md`
retains the upstream attribution and license context. The build can use an
existing reference checkout or fetch only the two pinned files.

Subpacket notices identify all vendored material. None of these notices
relicenses third-party code or asserts ownership of it. Independent reviews
in `evidence/` were conducted within this collaboration; they are not external
human peer review. Search scripts and generators are untrusted, with formal
claims supported by the stated kernel theorems and exact data bindings.
