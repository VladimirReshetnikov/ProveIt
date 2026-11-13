# Expanded compact/iPRA rebuild: rejected stage 64

This bounded single-stage author run resumed the guarded 425-module
merged-root build after the first 63 passed stages. Lean compiled the pinned
current `BusyBeaver.ZFC.L2Root254` source and returned exit 0, but emitted an
unused simp-argument warning at source line 126. The runner's policy rejects
all warnings, marked the stage unsuccessful and exited 1. The direct
source/dependency/companion checks in the receipt remained unchanged. The
post-batch full overlay check was not reached after the rejection.

The exact rejected source, direct dependency list, raw compiler warning,
output hash and receipt are under `observations/batch-013/stage-0064/`. The
object with SHA-256
`16e2ea23478f0720e51544e6ff25c51f061b2513d2f0871ec079b00a4eb63202`
is rejected and must not be imported as a successful stage. The exact runner
has SHA-256
`e77f12c13a337b32e2f638dad46e6221e7edd44fb4b7a2de1ee5ec7a25fb09b7`.

The warned source contained `simp [toAS, Enum254.fetch, h, hv]`; the Lean
warning specifically identified `h` as unused. The separately prepared
workspace correction removes only that `h`. It is not justified merely by
this rejected run; it requires a fresh check with an explicitly re-pinned
source and continuation. The full iPRA endpoint and inherited package and
provider ancestry remain open.
