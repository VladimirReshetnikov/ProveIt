# Exact decimal215 arithmetic checkpoint: implementation plan

The new graph, step and run modules specialize the existing generic bounded
lookup/action and primitive-recursion APIs to `DecimalMachine215.machine`.
`literalRows` is `List.ofFn` of its215 pairs of typed transitions. A structural
lookup theorem proves all430 entries agree; neither a second machine nor
430 fresh evaluations of the715-digit decoder is introduced. Typed action
codes are positive and at most864, below the generic bound1012. Successor
halt has state code0 but a positive action code, preserving write and motion.

The step endpoint will cover every Nat configuration code, including halted
and invalid active codes. The run endpoint will be total and unique at every
index of every IΣ1 model, agree with the exact Core run at all ordinary natural
times, and provide a closed arithmetic halting sentence. IΣ1/PA proofs of run
totality do not identify that sentence with validator consistency and do not
constitute an HA derivation.

The selected prerequisite graph has125 custom modules:95 Foundation,
28 BusyBeaver,1 FirstOrder and1 DecimalMachine215. The worktree vendor directory
is unpopulated, so Foundation sources are read from the existing central
checkout at commit32e1a0956a8622fad067328ca1959729a7634428. All95 sources and380
object companions have independently recomputed Lake hashes matching their
v4.32 build traces (475 checks, zero mismatches). No Foundation rebuild is
needed. Twelve BusyBeaver arithmetic prerequisites absent from shared objects
were found in the maintained arithmetic and Rotation240 private caches; all
current source hashes and object hashes match the existing terminal receipt.
The other18 prerequisites are authenticated by the prior completed361 run.
These are cached prerequisites, not freshly rechecked mathematics.

Private overlay: `/tmp/arithmetic215-actual-private`. Initial dependency
manifest: `/tmp/arithmetic215-actual-private/dependencies.json`, SHA-256
`c7814a809f5411a9af3f9b2e25fcda8afa3f86e2c0778a2981744101e02cc1d1`.
The generic imported mathematics has been read; no existing verification
script is executed. The small fully read Lake file-hash program only reads
specified sources/objects. Installed toolchain/package objects remain an
explicit precompiled boundary. The build uses the private overlay and the
existing external package paths, excluding shared project objects.

The initial plan was superseded by the import collision documented in
`arithmetic-machine215-import-collision.md`. Root authorized exactly one
existing-source change: replace DecimalMachine215's broad Mathlib.Tactic
import with Mathlib.Algebra.BigOperators.Group.Finset.Basic. All declarations,
proofs and machine data remain byte-identical. The complete decoder and its
existing checks were rebuilt privately, followed by all six new leaves and a
separate two-leaf native endpoint regression. All passed with
`-M6000 -j1 -DElab.async=false`. No vendor source, shared object, umbrella or
Git state was modified by this work. The final author receipt is
`arithmetic-machine215-author.md`; its bundle preserves exact source/object/log
pins and distinguishes 124 cached prerequisites from the eight fresh machine
leaves. The original 361-module closure and subsequent 15-module refresh remain
historical pinned snapshots, not retroactively refreshed closures.
