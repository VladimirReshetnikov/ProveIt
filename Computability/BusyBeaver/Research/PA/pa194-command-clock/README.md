# PA194 clock and command scheduler

`PA194CommandClock.lean` composes the complete standard-source clock bridge
with the PA194-specific command-scheduler equivalence. It proves that each of
the two exact PA194 clock codes reaches 1 if and only if the command scheduler
halts from the initial state `(N,L,T,W,D,H) = (2,0,0,0,0,0)`. The proof
checks that the scheduler's initial configuration is exactly the seed source
configuration. Both equivalences print `[propext, Classical.choice,
Quot.sound]`.

This is a standard-natural-number Lean theorem. The command calculus has not
yet been related to PA refutations, and this does not establish an internal
PRA/iPRA consistency equivalence. The source tree retains the pinned Python
grammar-translation boundary described in `../pa194-source-tree/README.md`.

The source has been checked using independently rebuilt temporary source,
clock, coverage, and startup objects. On the machine used for this check, the
command from the repository root was:

```sh
LEAN_PATH="/dev/shm/pa194-ax-probe:/dev/shm/pa194-merge-fresh:/dev/shm/pa194-coverage-preserved:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$(lake env printenv LEAN_PATH)" \
  lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-command-clock/PA194CommandClock.lean
```

These overlays are temporary and are not distributed. The neighboring
`pa194-command-source` and `pa194-clock-source-complete` directories describe
the separate clean-build checks and their current status; a single combined
fresh build of this final composition has not yet been provided.
