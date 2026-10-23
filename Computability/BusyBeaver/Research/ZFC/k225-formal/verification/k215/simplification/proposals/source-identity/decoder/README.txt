Direct-program decoder certificate proposal

Pin: cbf94cb552a3b49509e0eee80e7455d4eb5974c6 (VladimirReshetnikov/ProveIt).

Read PROPOSAL.md for the full proposal. decoder_section.tex is a report-ready
LaTeX section. This is a separately checked prefix-library simplification,
not an immediate reduction of the maintained K215 endpoint closure.

DIRECT_PROGRAM_AUDIT.json reports the owned finite source-data audit.
NODE_AND_ROLE_MAP.json contains the complete 179-fork-label map, 23 primitive
projections, 234 role relabelings and 468 branch bindings.
source_provenance.json authenticates 27 source snapshots in sources/ against
the exact pinned Git blobs.

DirectProgramCertificateDraft.lean is an UNCOMPILED checker/data pilot.
It intentionally has no generic semantic soundness theorem. Existing blocks
are imported from the old module as a migration convenience. Neither this
pilot nor its finite audit proves primitive/return opcode contracts.

Reproduce the owned finite audit:
  python -I -B audit_direct_program.py --output-dir /tmp/direct-program-check

Regenerate the uncompiled pilot:
  python -I -B make_direct_role_sketch.py

Only owned Python is executed. Upstream Lean and other source files are
parsed as inert text. No upstream generator, proof assistant or repository
mutation is involved. No net line, kernel-size, memory or build-speed saving
is claimed before integration and an exact fresh check.
