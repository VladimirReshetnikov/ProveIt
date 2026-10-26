# Exact decimal215 arithmetic machine: independent root review

26 October 2026. Root read all six new Lean sources/checks, the complete
decoder and its existing checks, the generic lookup/step/run interfaces,
the author's receipt and the replay drivers before accepting the packet.
The sole existing-source edit narrows one decoder import; every declaration,
proof body and machine datum is unchanged. No Foundation vendor is edited.

The graph uses both actual typed transitions for each of the215 states.
Its structural lookup theorem covers all430 actions. Positive action codes
preserve the write and move when the successor is halt; zero denotes absent
lookup. The step comparison covers every natural configuration code,
including absorbing halted and invalid states. The run is total and unique
at every internal time in every IΣ1 model. Its standard specialization
represents the actual complete tape and head at every ordinary natural time.
The closed halting sentence has the stated standard interpretation. The
IΣ1/PA proof here concerns run totality, not consistency calibration.

Root independently compiled the decoder, its checks and all six new leaves
in `/tmp/arithmetic215-root-peer-7nbm_glx`, retaining `-M6000 -j1`.
All passed;24 axiom reports use only `propext`, `Classical.choice` and/or
`Quot.sound`. There are no unfinished proofs or extra axioms.
The first decoder replay used a relative input path through `lake env`
without an explicit async flag and produced a different valid object
(`db808e3980fdfbab44c027c57a475315211ba81036dd757e66fde85e5400a7b6`).
A further replay with the author's absolute source path and explicit
`-DElab.async=false` passed and matched its object exactly
(`d3a3e00a4cd47a0a147cf51f35f2dba60266a0790cc118a84b89a7519f2d1a06`).
All seven other fresh objects matched the author. No single cause for the
initial decoder byte difference is inferred from these two changed settings.

The private prerequisite boundary is124 cached custom modules, not a new
full Foundation or native proof replay. Root rechecked125 source hashes
(including the fresh decoder) and409 cached object/companion hashes. All95
Foundation source hashes and380 companion Lake hashes were independently
recomputed against the actual4.32 traces:475 matches. Twelve BusyBeaver
arithmetic objects match the retained Rotation240 source/object receipt;
the other17 cached modules match the prior completed native closure.
Root separately checked all164 pins for the41 direct external precompiled
imports. These checks authenticate reuse; they do not freshly elaborate
those prerequisites. The installed Lean/package closure remains trusted.

The author's separate two-leaf `CurrentPositiveZero2011` regression also
passed with six standard-only reports and unchanged endpoint object bytes.
Root checked its recorded source/object/log/time hashes; this regression
was performed by the packet author, not independently repeated by root.
The original361-module validation and later15-command refresh retain their
historical scopes. The new Foundation arithmetic leaves are intentionally
standalone: broad existing umbrella imports still need compatibility work.

Durable independent commands, source/object/log hashes, prerequisite pins
and the recomputed Lake hashes are in
[arithmetic-machine215-root-replay/ROOT.json](arithmetic-machine215-root-replay/ROOT.json).
The separate author's complete bundle is
[arithmetic-machine215-replay/BUNDLE.json](arithmetic-machine215-replay/BUNDLE.json).
Root checked its14 file pins and archive integrity and read all executable
drivers before acceptance. The bundle preserves failed development attempts
as well as the successful final runs.

The [C222 audit](../research/ha-c222-internalization-audit.md) identifies the
missing all-model bridge to the existing C254 consistency endpoint: internal
seed-bundle calibration and the actual counter4 enumerator/runtime simulation
remain open. This packet proves neither an internal consistency equivalence
nor existence of its HA proof. The maintained decimal14/65/150 TeX/PDF are
unchanged.
