# PA194HX and the primary startup seed

The [delivered PA194HX table](../../../../docs/pa194_research_2026-11-14/hx194/machine/pa194hx.tm)
has 194 working states, starts on a blank tape at state 0, and halts at
state 194. Its SHA-256 is
`3242a613d328d17c979ce3675a154733ea16a1949b4391cb824711b5aa46399a`.
PA194HX swaps the physical H and X register blocks. The shared logical
registers, spare, and suffix are preserved by the
[allocation map](PA194HXAllocation.lean).

The [dispatch check](PA194HXDispatch.lean) binds all 388 numerical rows
to the literal zipper machine. The [zipper bridge](PA194HXZipBridge.lean)
identifies their finite numerical runs. Lean checks all 439 startup
segments and their composition from blank.
[`PA194HXSharedStartup.sharedSeed`](PA194HXSharedStartup.lean) proves that
the HX run after 56,134 steps and the primary run after 58,154 steps reach
the same full packed configuration in every `IΣ₁` model.
[`PA194HXSeedFrame.reachesFrame`](PA194HXSeedFrame.lean) identifies that
configuration with the HX register file at source site 25 and header gap 42.
The equivalence of later execution through the changed routers remains open.

Run from the repository root with fresh output directories.

```sh
pa=Computability/BusyBeaver/Research/PA
literal=/dev/shm/pa194-primary-for-hx
shared=/dev/shm/pa194b-for-hx
bash "$pa/pa194/ipra/native-endpoint/check-literal.sh" "$PWD" "$literal"
bash "$pa/pa194/ipra/variants/pa194b/check.sh" "$literal" "$shared"
python3 -I "$pa/pa194/ipra/variants/pa194hx/check.py" "$literal" "$shared" /dev/shm/pa194hx-replay
```

The replay regenerates the two HX row representations and startup
checkpoints from the pinned table. It rebuilds the natural-number to
model-valued lift, the literal HX checks, and the shared-seed theorem. It
uses prebuilt dependencies from the primary and PA194B stages, including
the checked primary startup.
