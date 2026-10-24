# Attribution and scope

This is new OpenAI-assisted mathematical research and software prepared for
Vladimir Reshetnikov's ProveIt repository. It combines the ideas credited to
the existing packages 20-root12, 21-norm12, 19-wang943 and 22-monic12, together
with the earlier blank-input arithmetic and the pinned K215 construction.
No external human endorsement or human authorship by the cited researchers
is implied. Independent reviews were performed within this assistant
collaboration.

New contributions are the distinct inner/outer weights and degree-1081 norm,
the uniform root-gap argument and degree certificate, the mixed-radix
coefficient decoder, external population padding, the shorter exact-support
layout, their proofs and audits, fixed-instance bindings, and this report.

The arithmetic emitter adapts package 21's scalar norm evaluator. The 943-tile
language and K215 table are unchanged. The 67-operation polynomial and
59-operation system are inherited arithmetic with a newly proved complete
coefficient binding. Original notices and the repository MIT No Attribution
license are retained under `licenses/`. New material follows that repository
license; inherited third-party components retain their original terms.

Some preserved historical notices refer to directories in their source
packages. They are preserved verbatim as provenance. The current package's
actual contents and paths are defined by README.md and provenance/SOURCES.json.

The result is an ordinary mathematical equivalence formalizable in ZFC,
with explicitly stated inherited dependencies. It is not a new end-to-end
proof-assistant certificate, a proof of ZFC consistency, or a global minimum.
