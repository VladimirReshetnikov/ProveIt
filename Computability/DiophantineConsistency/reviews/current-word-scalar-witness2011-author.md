# CurrentWordScalarWitness2011 author receipt

I authored and fully read the new module and focused checks. Both final bounded fresh builds pass. This is an author self-review, not an independent review. The result constructs only the stated scalar witnesses from the actual words; it does not claim a 31-variable source solution, complete high-mask acceptance, controller existence, or a full polynomial zero.

## Frozen bindings

| File under `Lean/DiophantineConsistency/` | Lines / bytes | SHA256 |
| --- | ---: | --- |
| `CurrentWordScalarWitness2011.lean` | 156 / 7111 | `8a644c7eb65bff5016d28a992e2db477bb5341b33fa31e92f1a086a0d0e4879e` |
| `CurrentWordScalarWitness2011Checks.lean` | 80 / 3396 | `1c47209fca1a79e346e7ce2b4559cf20095c62ced1974ab26346a23a892bdbb0` |

The two direct imports are frozen `CurrentWordTopBounds2011` (`7f8cf6688ef8f0152cbafd388957635a0f8a10e7e72de73fc52af87871217a1f`) and root-authored `CurrentWordLowMask2011` (`cc217428c511731eb99169a46d65ca2cf2f14cc7d17fa83f6fc68fc5497a70f4`). I authored TopBounds and earlier word/clause/kernel dependencies. No existing module was changed.

## Constructed objects and proof scope

For nonzero cell count N, actual tile assignment a, independent Boolean dummy/marker maps, and any natural whole-cell stride s, the definitions retain:

- `q = radix^(N*2011)`;
- `C = word radix (CurrentWordConstruction2011.word a dummy marker)`;
- `F = word radix digits` from the actual carry normalization;
- `w = 2^(47*(2011*s))`;
- `alpha = q-C-F`;
- `z = ((K+w)*C)/(q-1)+1`.

`strong_slack` uses the established bounds on those same source and normalized words. Both are below `P = radix^(N*2011-1)`; `q=P*radix` and `9≤radix` give `3*(2*C+F)<q`. No desired slack inequality or alpha positivity is supplied. Natural subtraction then gives positive alpha and the exact balance `C+F+alpha=q`, and both natural and signed identities `q-F-alpha=C`.

For transport, `F<q-1` and the constructed congruence imply `((K+w)*C)%(q-1)=F`. `Nat.mod_add_div` gives the exact quotient identity `((K+w)*C)=F+(z-1)*(q-1)`. The successor definition proves z positive even if the quotient is zero. Passing to integers yields the literal printed unit factor `(K+w)*C+(q-F)-z*(q-1)=1`. It is deliberately not a zero residual.

`scalar_witness` assumes only the constructed carry Facts, Boolean controls, and `a 0=0`; it concludes all scalar facts and the actual whole low-mask test `(C-1) &&& (lowPort*repunit width N+1)=0`. It does not require horizontal or temporal matching, a canonical marker, high-mask acceptance, a supplied quotient, or a machine premise. `exists_scalar_witness` obtains the carry Facts itself, so its input has no normalization premise. All positivity claims are proved, including C from the origin Start and F from the actual positive clause.

Focused checks cover zero and nonzero quotients, the incorrect unincremented quotient, a congruent but noncanonical representative rejected by the strict bound, the factor being nonzero, the radix threshold, `N=1` with seventeen whole periods and arbitrary Boolean controls, and substitution of the signed recovered C into the displayed factor. The constant-Start check does not pretend to supply a matching tableau.

## Fresh validation

The final main and checks were read in full before their successful direct serial compilations. Commands used `lake env lean -M6000 -j1`, source-level `Elab.async false`, and new matching `.olean` paths only. Existing frozen prerequisites were imported, not rebuilt; no complete fresh dependency replay is claimed.

- Main: PASS, 4.91 seconds, peak 3282776 KB, no Lean diagnostics.
- Checks: PASS, 3.37 seconds, peak 3249468 KB; nine axiom reports, no warnings. Reports contain only `propext`, `Classical.choice`, `Quot.sound`, or the applicable subset; quotient positivity reports no axioms.

| Artifact | SHA256 |
| --- | --- |
| Main object | `5789a6252546bb394ccf0d84239cde81023d83ebd6d106eac24f23a3c672ed2b` |
| Checks object | `62fe8bfa9089343a7c4e62ee9eb247b362731719c35503a22ee88b8201665487` |
| `/tmp/current-word-scalar-witness2011-main-stage3.log` | `2acd9640f0e1284028b8691a95467ff8ba640fb59dba8d3588d3c6dafba94174` |
| `/tmp/current-word-scalar-witness2011-checks-stage1.log` | `c7d9edd833f7d7fc7217c1ea64a593074765a8b74c8327267ae03adfc6a4949c` |

Initial development failures were missing explicit nonzero instances on the word aliases, a tactic's quotient nonnegativity inference, and the final cast/definition rewrite shape. These were fixed using the required nonzero cell-count interface, direct successor positivity, and explicit alias/radix rewrites. No mathematical target was weakened, no desired conclusion was added as an assumption, and failed builds are not counted as passes. No `sorry`, new axiom, external proof oracle, or incoming executable was used.
