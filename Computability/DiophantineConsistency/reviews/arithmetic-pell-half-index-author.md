# ArithmeticPellHalfIndex author receipt

Status: the complete new main and focused Checks are frozen after a clean private pair. This is author validation, pending independent ROOT review/replay. No accepted source, shared object, Git state, equation, display or dependency was changed.

## Exact scope

Both modules quantify over an arbitrary natural arithmetic model `V` with `ORingStructure V` and `V ⊧ IΣ1`; every index is internal, including nonstandard indices. The sole imports are accepted `ArithmeticPellIndexDivisibility` and `ArithmeticPellResidueClasses`.

`odd_x_dvd`, `odd_exact` and `odd_rec` construct the actual quotient `xcoord (2*h+1) b / (b+2)`, prove exact division, and derive its additive recurrence before any modular argument. Its initial pair is `1, 4*(b+2)^2-3`. `quotient_mod_norm` and `quotient_mod_divisor` use represented Σ₁ induction on adjacent pairs with alternating signs. They do not cancel or invert the base modulo either modulus.

`half_index` assumes positive `c,i,f,R,y`, the actual main norm `d²=1+δ(a)c²`, relaxed norm `(i*c²)²+δ(a)=δ(a)f²`, half norm `(i*c²)²*u²+y²=1+(i*c²)²*y²`, the caller's large bound `(a+2)*δ(a)²<c`, strict window `2*R<c`, and both signed residue alternatives `SignMod f u c`, `SignMod c u R`. It derives `d=xcoord R a` and `c=ycoord R a`.

The main and both auxiliary classification indices are obtained from the actual norm equations. The large bound excludes main indices 0,1,2; represented growth yields `2*p<c`. The accepted relaxed auxiliary theorem supplies the same `f=xcoord m a` and `c∣m`. Exact odd quotient transport and doubled step-down give the signed index class modulo `m`, then modulo `c`; the strict half-window forces `R=p`. The positive-ordinate premise remains explicitly present as `_hy`, although classification is strong enough that its proof does not need that positivity separately.

`literal_half_index` derives the residue inputs for the exact unsigned absolute difference of `f²*c*T` and `f²*R+c`, handling both orders and equality. The strict factor `f²=1+δ(a)*(i*c²)²` is passed to the relaxed theorem with the **full coefficient `δ(a)*i`**, not the original `i`. The large bound and strict half-window remain explicit. No sign of the underlying difference is assumed.

This does not derive the first-carrier identity `2*n=R+1`, the caller's scalar windows, power recovery, cofinal witnesses, a complete equation/consistency calibration, or an HA endpoint. No source-validity, desired-index, standard-index, or external fundamental-unit premise is introduced.

## Frozen sources and outputs

- Main: 522 lines; SHA256 `222bc3bd7e7fbb2c4924fee0b26c24f38e359475b956fd800116b1abe665871c`.
- Checks: 45 lines; SHA256 `439c7b26187dcb2b51437f0fe20eff9d56516151ca1811520f5ce3efd72efc7a`.
- Main object: `ba6797b357acfc6c59a0fceaccb58a8f0164bb7a51b25d2b2abdfcec626f6c79`.
- Checks object: `c3c3312dc9886933ff25be0c92d88b2cda01df2d79bb3fc7cd60f9c41d849b2a`.
- Final provider: `/tmp/arithmetic-pell-half-index-author-wucxxxm0/lib`.
- Main 57.354s, peak 1935776 KiB; Checks 2.080s, peak 1801912 KiB.
- Main log empty. Checks contain ten reports, each restricted to `propext`, `Classical.choice`, `Quot.sound`; no errors, warnings, sorry or new axioms.

Focused examples cover quotient index zero, the sign-sensitive first odd quotient under each modulus, equal/reversed absolute differences, and the endpoint with both opposite-sign residue branches. The ten axiom audits include both public endpoints and the quotient/transport/growth helpers.

## Authenticated reuse and execution

The frozen plan/proposal and all selected source/header/import/object/compiler pins were authenticated before each execution. The exact selected closure has 106 custom modules, including 95 Foundation modules, with 391 custom artifacts; 38 explicit package boundaries have 114 total artifacts (38 primaries and 76 companions). All **505 actual first providers** were checked on the precise private `LEAN_PATH`. There was **zero prerequisite refresh** and no Foundation build. Existing accepted providers are reused with the provenance recorded in the complete plan; this is not a fresh closure claim.

Each attempt used the unchanged, fully read driver `/tmp/arithmetic-pell-half-index-author.py` (SHA256 `aa2d979bb1eb36141be55f8c9199c07625ee7803d8ef6d0d39a8662154574053`). Its exact commands are in the packet: Lean4.32 `-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1`, one fresh regular nonsymlink output per new leaf, and a 512MiB disk guard before and after execution. Both source snapshots were taken before the first compiler, including Checks when main failed. The final run rechecked 1392 observed paths and ended with 953708544 free bytes. The freeze separately authenticated 5649 observations across 2635 paths.

## Preserved attempts

1. Main exited 1: explicit numeral/index normalization and local order/modular API elaboration errors; definability automation expanded represented coordinates into recurrence implementation and exhausted its existing default search/heartbeat limits. No cap increase was used.
2. Main exited 1: after keeping represented coordinates locally opaque and registering the exact quotient's Σ₁ function instance, only the zero-index normalization and an explicit `2≤3` proof remained.
3. Main exited 0 but the strict clean-log guard rejected the unused `hy` binder warning. Its actual emitted object is pinned separately in `attempt_objects`; Checks was not run.
4. Final main and Checks both exited 0 with clean diagnostics. The retained premise was named `_hy`; no mathematical premise or conclusion changed to resolve that warning.

All four complete input pairs, drivers, metadata, provider resolutions, logs, timings and states are durable in `arithmetic-pell-half-index-author-replay/`. No failed attempt was overwritten. Local opacity annotations affect proof elaboration only and are scoped locally; imported source declarations remain unchanged.

## Durable evidence

- Replay packet: `arithmetic-pell-half-index-replay.json`, SHA256 `2c255ff75da9cc19439fe6786055652eb65beabf7dc1ce2b754551b40e787083`.
- 42-file manifest: `arithmetic-pell-half-index-author-replay/FILES.json`, SHA256 `9cae06eaae911770bbd16f9cea8a654386d8f76f3b23e3bbee49beb02309565e`.
- Frozen proposal SHA256 `199cede28d2979dcb5907ee49496b1c64399e36fe710dd967372c05cbc03ef28`; plan SHA256 `d208392a2a3b6c4f32d2525b242c13adc588d3af9fce2e5579a4476bf883ad1b`.
- The durable bundle includes the fully read executed driver and freeze script, final input/provider evidence, and the complete chronology.

Controller's earlier arithmetic/proposal challenge is source-only and is not a complete implementation or replay review. ROOT independent review/replay remains the acceptance step.
