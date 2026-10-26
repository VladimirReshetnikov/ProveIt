# Independent review: actual rank calibration and forced multiplier

**PASS, with no source correction requested.** The controller-certificate agent independently read the complete frozen main, all focused checks, and root's complete author receipt, and freshly replayed both files in an isolated object overlay. Root authored this new composition. The reviewer authored the finite dummy-mutation and controller-unit prerequisites, plus several local word and scalar-bound dependencies. Those roles are disclosed: this is an independent review of root's composition, not an independent authorship or complete reconstruction of all its prerequisites.

## Critical binding review

I checked the full dependency order, including the complete current `SafeController`, `PackingRank`, `PackingParity`, `NativePacking`, and `WordRephase` interfaces and the previously independently reviewed generic/actual rank–stride pair. The exact `NativeRankVariation.windowRank` expression and its binding to `Carrier65.core.rank` were also checked.

The final construction requires an actual marked word on `N=120199^(k+1)` at stride `s=120199^rw`, `rw<k`, and `94517*120199<120199^k`. The selected support, successful masks, normalized word, rank congruence and desired ordinary increments are all conclusions or intermediate derived facts, not additional hypotheses.

The proof has the following coherent sequence:

1. It constructs a zero-dummy packing and calls the integer rank of **that** source and normalized word `R0`. The dimensions, repunit and ports are fixed. The actual coefficient `Gamma` depends on these dimensions, the original stride and literal `K`, rather than on the source/digit words that will change.
2. `exists_safe_gamma_sum` chooses a nonempty finite support with the target `R0-d*s` in the full modulus `d*N`. Its canonical physical safety inequalities supply exactly the assumptions of the finite-mutation theorem. All finite exponents and the complete support survive the natural/integer/`ZMod` casts; no term is dropped in `powerSum_cast_B`.
3. Finite mutation constructs actual final carries/digits and derives ordinary source and normalized-word increments. Its integer rank decrement then gives `Rnew = R0-Gamma*P(S)`. Casting this proved equality and using the selected target gives `Rnew ≡ d*s [MOD d*N]`, with the correct subtraction sign. There is no circular assumption of the desired increment or rank congruence.
4. The same final normalization is upgraded to a full marked packing, with the same actual source, carries, digits and Boolean controls. Both entire masks are established for that packing. The actual natural rank witness `R`, its population `σ 2 R=3*(width*N)+2`, residue `R%4=3`, odd decomposition and growth `2*(width*N)<R` all come from this particular packing. The low port is `lowPort`; the source high port is `highPort+beta`, shifted **once**, as in the exact rank definition and finite-mutation call.
5. Divisibility and the calibrated congruence determine the positive natural stride `t=R/d-N`. Its residue agrees with `s` in `ZMod N`, and its ordinary displacement is exactly `R-d*N`. Rephasing retains the entire source function, not merely a congruent source integer; it also retains the digit and carry functions. The final `hCeq` explicitly rewrites the actual source at stride `t` to the source at stride `s` before applying `hR`. Thus the final result binds `R` to the rank **after rephasing**, not to an unrelated former packing.

Consequently the equality `multiplier t=2^(R-width*N)` is an ordinary power equality derived from the exact natural quotient equation. It is not inferred solely from equal residues. The new ordinary multiplier and positive quotient may change; the source and normalized word do not. The growth conclusion makes the relevant subtraction nontruncated. The actual assignment and its marked matching at the new stride are retained as well.

No inconsistency or missing premise was found in these bindings. This packet discharges the supplied-`R` limitation of the earlier rank–stride adapter. Its scope remains native packing and rank calibration: it does not derive a marked word from a halt, assemble all positive outer/auxiliary Pell coordinates, construct a full polynomial zero, or establish an internal ZFC theorem.

## Exact frozen files

Paths are under `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines / bytes | SHA-256 |
|---|---:|---|
| `CurrentRankCalibration2011.lean` | 128 / 7,111 | `0f49fd9339d50e54d391427cc20ae2cbce450f1d4186bc6e3249dc305393e4a3` |
| `CurrentRankCalibration2011Checks.lean` | 51 / 2,390 | `ddd1ec8fa09118206e6729559a4bcb44c9350596a63a8319b959f5492f3f898d` |

Root's `reviews/current-rank-calibration2011-root.md` was read in full; its SHA-256 is `481ffc35b90dbd3b7174c77823bc72695378160b8599d60f959dd0a793160f3c`.

The four exact direct imports were pinned:

| Import | Source SHA-256 |
|---|---|
| `CurrentSafeController2011` | `561f7bdaf81a6973fbe713b7710ef9258eafeff35d82e55e9e75ed643f2a3d2f` |
| `CurrentFiniteDummyMutation2011` | `7828e384536178637eedc37358f46edfc0979b32d2ec2634619815dd2e218601` |
| `CurrentPackingParity2011` | `78ac7146d33518ee410891d93df7d19384adc2fca5b2970f2a1a090841de99bb` |
| `CurrentRankStride2011` | `5f7bbc932de6d984140e518864d275b2f0c655148ecf301d0235ae8e76c790ec` |

The review also pinned the sources/objects for `CurrentPackingRank2011` (`614f47e52f31dfc199f98387e5c720f1ae51fb0725ce8d9f21223b540a30c546`), `CurrentNativePacking2011` (`df17b8a5c2913b2ffec6d4b6fbd3fe5127aa45e76273ed88734f30da548fa92e`), `CurrentWordRephase2011` (`7a1df92104c40f502cc7b62fb1ac04327ce5c842be95172a5483d511a0b99332`), `CurrentControllerUnits2011` (`1c3bdb8af6c4113589b92b76aa895fbee3ecad4ca4d32f8e6290b382bf2f004f`), and `NativeRankVariation` (`46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73`).

## Fresh isolated replay

Both reviewed stems were excluded from the reused-object symlinks in `/tmp/current-rank-calibration2011-controller-peer/lib/DiophantineConsistency/`. The overlay was prepended to `LEAN_PATH` after `lake env`, so the focused checks imported the newly compiled main. Other prerequisites were reused; this is not a fresh full-closure build. Existing sources and objects were not overwritten.

Both commands used Lean `v4.32.0`, `-M6000 -j1`, and the sources' `Elab.async false`.

| Replay | Wall seconds | Peak RSS KiB | Exit | Fresh object SHA-256 |
|---|---:|---:|---:|---|
| Main | 9.33 | 3,947,376 | 0 | `8c2e58c8fa580d05c42a68e275644e6e90be236d864fef51079b60c7b1abf599` |
| Checks | 3.44 | 3,338,072 | 0 | `c2a93acb4f8406550443eff29ec09539d7850d377c25b4471c9fbda48c449c5e` |

Both fresh objects are byte-identical to root's author objects. The main log is clean; checks emitted exactly six requested reports, all using only `propext`, `Classical.choice`, and `Quot.sound`, or subsets. No warnings or errors occurred. The checks retain the independent-exponent Gamma identity, complete support cast and the full final endpoint with no supplied calibrated rank or packing. No `sorry`, `admit`, `native_decide`, `unsafe`, or declared axiom occurs in the new sources. All 23 source/object/toolchain inputs pinned before replay were unchanged afterwards.

Local replay evidence in `/tmp/current-rank-calibration2011-controller-peer/`:

| File | SHA-256 |
|---|---|
| `inputs.json` | `ee9f3c6aca80f915ee396f06396093ca5fa308d040d95538acc5df345d9f0993` |
| `result.json` | `c9a85fb100367237bc023d3a06bf1b5a5478fd4ad9de3e798c86fa8cbb66d164` |
| `main.log` | `21115fd4a99919e657aa53c2bab1694aea24459add14cf1abc997ff7621ad4d1` |
| `checks.log` | `a29a1178642b119884e813fb00cca623c867b1b1ec2f78fa362df144c46c70b2` |

The `/tmp` paths are local verification evidence, not durable proof prerequisites. Only this new peer receipt was added to the repository; no frozen source, central document or git state was edited.
