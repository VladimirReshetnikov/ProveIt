# Whole-period rephasing: author receipt

This packet preserves the complete source function, carries, and normalized
digits when the natural cell stride changes by a whole cyclic period. It
derives the new scalar transport from equality of the actual binary rotations;
it does not equate the two ordinary temporal multipliers. This is an author
receipt, not an independent review.

## Frozen files

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentWordRephase2011.lean` | 122 | `7a1df92104c40f502cc7b62fb1ac04327ce5c842be95172a5483d511a0b99332` |
| `Lean/DiophantineConsistency/CurrentWordRephase2011Checks.lean` | 80 | `698241ca903127bd4d84bd3a855b007058d76613169b4f4e8a26d5f81a37c5d7` |

The sole direct import is `CurrentNativePacking2011`, source
`df17b8a5c2913b2ffec6d4b6fbd3fe5127aa45e76273ed88734f30da548fa92e`.
The key reused interfaces are:

| Module | Source SHA-256 |
| --- | --- |
| `NativeCyclicRotation` | `4d52b75fe4159ff1853353d012074132d7fc39458f7ea28d735a631c464b3f38` |
| `NativeBooleanRotation` | `d50110d8f2a959df7da69f23e80b4df09a1aad98ba2b66c67d2445203cf81f3e` |
| `CurrentCarryConstruction2011` | `6efd60cd1ce0f40aa48e68ec7d9c2b2c680bbdc0aa289488c268e79fa68a026a` |
| `CurrentWordConstruction2011` | `9455d6c2015906a8f76ff2be5275a95cae5340f0ca3e8dc16666ffc6bab2b5b8` |
| `CurrentWordClause2011` | `df93b7dc684693e23097e5bfdba9aa3a9121595574b6026832d2a4f3f2fd24dc` |
| `CurrentWordCopies2011` | `61e1662e3bd9a4a1409a5d47da4a017e714173ca3b2fc247a1bbb38a56546a9e` |
| `CurrentWordScalarWitness2011` | `8a644c7eb65bff5016d28a992e2db477bb5341b33fa31e92f1a086a0d0e4879e` |

The author also authored the copy and padding packets and independently
reviewed the native-packing composition. These roles do not constitute an
independent review of this new packet. Existing compiled prerequisites were
reused; this task did not rebuild or replace them.

## Exact result and premises

For `[NeZero N]`, natural strides `s,t`, and the explicit hypothesis
`(s : ZMod N) = (t : ZMod N)`, `physical_shift_eq` proves equality of the
physical shifts `2011*s` and `2011*t` in `ZMod (N*2011)` through the actual
cell-base map. `constructedWord_eq` proves equality of the complete source
functions, including the canonical shifted Start marker. That source identity
does not require Boolean dummy controls or matching, and remains valid at
`N=0`; normalization itself uses a nonzero cyclic length.

For any Boolean source, `rotation_eq` uses the actual zero-fractional-phase
rotation theorem to identify both binary rotations. The generic
`normalization_of_rotation_eq` then retains the same carry and digit functions
and every carry bound, digit bound, recurrence, decomposition, and word bound.
Its transport proof combines both `word_binaryRotation` congruences and the old
transport. Equality of ordinary factors `2^W` and `2^W'` is neither assumed nor
concluded.

`normalization_rephase` binds this argument to the actual constructed source
with Boolean dummy controls. `markedWord_rephase` transports the same actual
tile word using only the stride residue. Finally `marked_packing_rephase` and
`packing_rephase` produce the complete `CurrentNativePacking2011.Facts` at the
new stride for the SAME particular source, carries, and normalized digits.
The actual low and high masks are re-established against those same words;
the repunit and dimension identities remain unchanged.

The new positive scalar quotient is recomputed by `scalar_witness` for
`K + 2^(displacement t)`. The ordinary multiplier and quotient may differ from
their old values. No rank congruence, rank growth, forced rank exponent, safe
dummy mutation, native-source31 witness, or polynomial converse is asserted.
The modular stride equality is an explicit input to this packet.

## Fresh verification

All new source and checks were read before execution; the final main was read
again after its elaboration correction. Both files set `Elab.async false`.
The direct sequential commands were:

```sh
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordRephase2011.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordRephase2011.olean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordRephase2011Checks.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordRephase2011Checks.olean
```

Both passed. Main took 3.79 seconds, peak RSS 3,341,148 KiB; checks took
3.91 seconds, peak RSS 3,335,856 KiB. Main had no diagnostic. The checks have
one benign exponentiation-threshold notice for the symbolic exponent 94517
in the unequal-ordinary-multiplier control. All eight axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, added axiom,
or `native_decide` occurs.

Focused checks cover arbitrary numeric dummy controls at `N=1`, two full
periods at `N=3`, exact packed-source equality, same-carry normalization at
`N=1` without claiming a one-cell marked tiling, and preservation of a
particular full packing. Negative controls prove unequal ordinary multipliers
despite equal cyclic strides, and different binary rotations when strides
are not congruent at `N=2`.

The only development correction made the accepted `radix = 2^47` definition
explicit when applying the generic rotation transport identity. No theorem
statement or mathematical premise was changed. Frozen prior sources and git
state were not edited.

| Artifact | SHA-256 |
| --- | --- |
| Main `.olean` | `278d1c63dcb4e9371511ec2616f5eb977632254c7179fca1f8aacc7351179862` |
| Checks `.olean` | `18491f8a0c78cae78f7179def013c6522854a2731c7c8fd45dabca2caa43a730` |
| `/tmp/current-word-rephase-main-stage2.log` | `8acd428a7350d45fe93a4e94bffec17f9d62744c21b93711a6ece0908b9bb52b` |
| `/tmp/current-word-rephase-checks-stage1.log` | `49b5c617ee87de2d18b51b0bcfc254a7178e0f07a464a5c81986e5838b713fee` |
| `lean-toolchain` | `2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e` |
| `lake-manifest.json` | `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665` |
