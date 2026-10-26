# Two mixed-carrier thirteen-variable equations: Lean author receipt

Author: `/root/circuit_reduction`, 26 October 2026. This is author validation,
not an independent review. I authored the new witness-map module, its focused
checks and the ordinary proof; `/root/controller_certificate` separately owns
the two operation graphs and finite audit. I also authored earlier
`ThirteenCarrierSoundness`, `ThirteenCarrierComplete` and several Pell/current
word dependencies, but did not author the immediate corrected-strong parent.

## Frozen source and fresh replay

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/ThirteenLVCarrier.lean` | 412 | d64e31b377007ddd05964e29a1976c857d036d6eb919524df58c3bd8c237bd02 |
| `Lean/DiophantineConsistency/ThirteenLVCarrierChecks.lean` | 96 | 3a4301d7b4c72dbf52dc365521397219b929159a23657eaa63d6f9470ba51bdf |
| `research/thirteen-lv-carrier122/PROOF.md` | 193 | 0b4652adbdb5938ba52bf0865799acdc19dcbc13e23948ce16dc33c83cfd8386 |

I read the entire final sources and proof, including all changes before their
execution. Final commands ran serially from the repository root:

```bash
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenLVCarrier.lean -o /tmp/thirteen-lv-carrier122/DiophantineConsistency/ThirteenLVCarrier.olean
lake env bash -c 'export LEAN_PATH="/tmp/thirteen-lv-carrier122:$LEAN_PATH"; lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenLVCarrierChecks.lean -o /tmp/thirteen-lv-carrier122/DiophantineConsistency/ThirteenLVCarrierChecks.olean'
```

Both exited0. `Elab.async` is false in both files. The main log is empty; the
checks produce sixteen intended axiom reports, each using only `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, new axiom, `native_decide`, cap
raise, broad Lake build, or accepted-source edit was used.

The freshly generated main and check object hashes are respectively
`8e30253006ff5e17196eb5581fa3dfc2280495b04d3b94f76310abae64646892` and
`694a2be66159e1b3bcb79b3fa76f785e6ca42b64ae6f440e5f8c54ac02a9803d`.
Final logs are `main-stage4.log` and `checks-stage4.log` in the private directory.
Their hashes are respectively
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` and
`806103158ebe84d78eda798cc907caf067b6cda6ebf064a6dfbf68c54914f011`.

The first corrected-profile version passed before the uncorrected variant was
added. Development checks initially needed the existing namespace dependencies
visible in the private overlay and a reducible `Fin.val` comparison in the
concrete counterexample. The final optional-correction proof needed explicit
zeta reduction of the local `let d` before rewriting. These were elaboration
corrections; no mathematical premise was removed or strengthened. The final
two-profile main and checks were both freshly compiled afterward.

## Exact dependency scope

Only the two new leaf modules were freshly compiled for this packet. Existing
accepted prerequisite objects were reused. The direct parent source
`ThirteenCorrectedStrong.lean` has SHA
`57729066535acf1909d30ea5de0b4b78e1ac6f1ae11a126e1c2c4526cc546efe`;
its reused object has SHA
`9c0b942bfcb02ecbdfde0e0e691862d9935bae98617bb874ac8ea5b8334f7142`,
matching the parent's published author receipt.

For the focused check import, 277 existing namespace objects/companions were
made visible by private symlinks. Their hashes were observed before and after
the replay; all277 remained unchanged. This is an inventory of available
objects, **not** an assertion that all were imported, that their entire source
closure was freshly authenticated, or that the native/machine closure was
recompiled. No shared object was overwritten by this packet. The source,
object, toolchain/manifest, log and sixteen-axiom observations are persisted in
`thirteen-lv-carrier-lean-replay.json`, SHA
`3cb3111fbe0951e978ce7519985d1e054999e2a96cb649e322aaa78e7d183f90`.

## What the new proofs establish

The common data exclude the m coordinate. Over any commutative ring, changing
only m by `±G*(V²-L*V)` preserves the corresponding signed ordinate and gives
both complete polynomial identities; the two maps are exact inverses.

For arbitrary integer ports with beta>0 and every positive zero, the proof
derives P=1 from the relevant product and the accepted consecutive-Pell
exclusion. It derives Q=Z=1 and the signed auxiliary norm. The positive
geometric data imply c>=2; the strong norm together with positive Delta and
the positive scaled i then implies f²>=c+1 and S²>c². The auxiliary norm excludes L=0, so
`abs V ≤ L*V ≤ V²`. These bounds and `abs y < 2*abs V` derive G>=0 separately
for each carrier. The subtractive m map is proved positive on every old zero,
including G=0 and negative y, rather than only on selected private seeds.

The focused checks include literal m-slot and twelve-slot identities, unchanged
common blocks, inverse maps, the L=0 exclusion, both signed-ordinate cases,
zero transport, and an actual positive assignment whose subtractive m is
negative. The last check confirms that the zero premise is essential.

`polynomial`/`currentPolynomial` are the corrected74-operation expression;
`polynomial72`/`currentPolynomial72` are the uncorrected72-operation expression.
The new positive-zero equivalences link the former to the accepted73-operation
corrected parent and the latter to the accepted71-operation normalized parent.
The optional correction also vanishes on the entire positive zero set of
either new equation, with P=1 established separately in each direction.

Both closed consistency endpoints use exactly `CurrentWindowCarry2011.ports`
and the accepted external Lean `DiophantineConsistency.ConZFC` theorem. No
native witness condition, port replacement, target norm, or zero-equivalence
assumption is supplied to these endpoints. This remains an external Lean
equivalence, **not** a derivation in HA or an assertion that ZFC is consistent.

## Separate finite metrics and attribution

The ordinary proof states13/72/124 and13/74/122, with the latter offering a
lower-degree tradeoff. The complete live graphs, all gate leaders, exact
nonzero leading coefficients, four whole current ports and full DAG
substitution identities belong to the separately authored finite audit in
`research/thirteen-lv-carrier122`; this receipt does not substitute for that
audit and makes no Lean `totalDegree` claim.

The mixed product itself was already prospective in
`research/scaled-auxiliary118/THIRTEEN_VARIABLE_LEAD.md`. This packet completes
its whole-zero witness maps and combines it with normalization and the optional
first-norm correction. It claims neither a new underlying idea nor a global
minimum. The maintained14/65/150 page and earlier accepted packets are unchanged.
