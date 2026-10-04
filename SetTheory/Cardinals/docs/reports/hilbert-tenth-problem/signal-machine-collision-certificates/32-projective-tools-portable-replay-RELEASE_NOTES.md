# Release-only replay acceptance

2026-10-04 UTC.

The portable replay adapter is accepted by a separate reviewer after final-source inspection, 24 independent CLI cases, six focused facade edge checks and assertion-preserving bytecode inspection. The owned release suite passed 42 tests. All original science and scientific-audit input bytes, modes and modification times are preserved; checker bytes remain unchanged.

Final adapter SHA-256:
`d1917acf7ef7880e874d2e302095b893ddb2a2001b3e8d9f33119a50e9d29ba2`

Unchanged scientific checker SHA-256:
`a945491e115e5f96dfc11e3d6e714ef367ecc0daddfce425d8310cb5949f4fec`

Complete input pin SHA-256:
`d20b85535be14fb12c2494447b8326dc260310c2d9441677f48866eb6e2658f8`

Independent replay-review manifest SHA-256:
`0830655bb8635877de11a44dd8f85f54d5166b20e74e6126793a5623ea760053`

## Scope of acceptance

The CLI authenticates all 14 science files and nine scientific-audit files, including both inert proof dependencies, the author source, rule data, manifests, checksum files and original metadata snapshots. It rejects additional/missing files and directories, altered inputs, malformed pins, symbolic and hard links, nonregular files, lexical aliases, overlapping roots and nonfresh/overlapping output.

Only the authenticated independent checker's exact source bytes are compiled, with optimization fixed at zero. A local import facade maps its historical source binding and externalizes its evidence path. Internal derived paths are wrapped as actual paths, avoiding accidental repeated historical remapping. No author/upstream program, physical simulator or saved collision schedule runs.

Mathematical evidence, complete rule-review evidence and stdout reproduce byte-for-byte. Actual relocated science metadata is measured before execution and compared to the checker's after snapshot byte-for-byte. Both full input trees and the pins are separately rehashed and checked for exact metadata preservation. Historical snapshots remain unchanged inert inputs. Audit-tree metadata comparisons are in-memory, not a second serialized JSON snapshot pair.

Relocation tests cover changed nanosecond modification times, read-only modes, spaces and Unicode. Both `-O` and `-OO` invocation paths have passed while checker assertions remain enabled.

## Distribution boundaries

Use this directory's `MANIFEST.json` and `SHA256SUMS.txt`. The `independent_review/` directory contains only its review manifest's regular artifacts plus that manifest and checksum file. Diagnostic directories containing deliberate symlink, hardlink and FIFO test fixtures are excluded.

The tools-only bundle expects complete science and scientific-audit trees supplied separately, as in the complete report layout described in README.md. It requires trusted Python and installed SymPy 1.14.0 on a quiescent POSIX filesystem. It is not an OS/network sandbox or a defense against a hostile runtime, adapter replacement, kernel/mount manipulation or concurrent adversarial races. Authentication is relative to the trusted release and pins.

No scientific theorem or frozen scientific file is changed by this release adapter. Its acceptance is reproducibility and boundary-check evidence for the bounded independent static audit.
