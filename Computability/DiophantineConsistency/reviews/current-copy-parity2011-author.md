# Current South-copy and marker parity: author receipt

The new packet proves all nine literal South-copy equalities and the shifted
marker equality before whole-field alignment. Both files were read in full
before their fresh bounded Lean execution. Both passed on the first run; no
post-build source edits are pending.

## Frozen files

| File | Lines | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentCopyParity2011.lean` | 200 | `dc49658f1d9c448eca9ff969336cd5f64b4f64483b47b48d72f3a6bd0d928c8a` |
| `Lean/DiophantineConsistency/CurrentCopyParity2011Checks.lean` | 67 | `b4c1cb086f9cb95e2cbb2cb061aa8830c3c68d93c3357f2d7875fb1314a75dcd` |

The freshly generated main object has SHA256
`6f6688705d6fe47f5810dc9a2fa2a5c90360958f454c35912244aa7a9f3b4d95`.
Its only direct source import is `DiophantineConsistency.CurrentPhaseParity2011`.
No previously frozen module or prerequisite object was rewritten.

## Mathematical scope

The endpoint `copy_marker_equalities` takes a positive cyclic length through
`[NeZero (N * 2011)]`, a physical cell base `b` with residue zero, and the
following explicit hypotheses:

- Every digit of `c` is Boolean and vanishes off the actual periodic low support.
- The actual physical selector sum in this cell is at most one.
- The carry is at most57 and satisfies both the literal kernel carry recurrence
  and the local addition equation with `binaryRotation 47 W c`.
- Every normalized digit satisfies the complete actual high-mask test.
- The fractional phase is zero: `W % 47 = 0`.

It concludes, for every `j : Fin 9`,

```text
c (b + (942+j)) = c (b + (960+j) - W/47),
c b = c (b + 1004 - W/47).
```

All arithmetic in the arguments is cast into `ZMod (N * 2011)`. The endpoint
does not assume that `W/47` is divisible by2011. It does not assume decoded
labels, occupation, a fixed marker value, a Start bit, or machine semantics.
The one-selector and fractional-phase hypotheses are deliberately visible;
their polynomial-level discharge belongs to the separate composition.

At a South-copy field `960+j`, the bare18 source is precisely `942+j`.
The other bare sources have cell residues `1967+j` and `951+j`, respectively,
so actual support makes both zero. The proof retains the complete reflected
sum, including all coefficient collisions, and uses its proved evenness.
The existing reflected-geometry reset proves that the incoming carry is zero.
The exact high digit is1 and the target is never the global origin, so no
origin-mask subtraction affects the test. Reduction of the local equation
modulo2 leaves the current source bit plus the actual temporal digit; the
outgoing carry term vanishes because the radix is even. Zero fractional
phase identifies the temporal digit with the shifted Boolean digit. An even
sum of two Boolean digits then gives their equality, retaining both0 and1.

The marker result reuses the frozen exact marker convolution, reset/parity,
and full-mask lemmas in `CurrentPhaseParity2011`; it does not duplicate or
weaken their support binding.

## Focused checks

The checks cover both ends of the copy-mask range at arbitrary cell bases,
actual two-cell wrapped source positions, the exact endpoint residues,
and the boundary at969. At that next field the spatial source has allowed
residue960 and the high mask is0, so extending the range would change the
mathematical statement. A symbolic Boolean word is also rotated by `47*19`:
the actual temporal source at960 is941, demonstrating that fractional phase
zero does not silently impose whole-field alignment. The final elementary
check records why Booleanity is needed when converting parity to equality.

The nine exported theorem axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, new axiom, or
`native_decide` in either file.

## Fresh execution

From the repository root:

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCopyParity2011.lean \
  -o .lake/build/lib/lean/DiophantineConsistency/CurrentCopyParity2011.olean \
  > /tmp/current-copy-parity2011-main-first.log 2>&1
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCopyParity2011Checks.lean \
  > /tmp/current-copy-parity2011-checks-first.log 2>&1
```

Main: PASS,5.35seconds,3272932KB peak. Checks: PASS,3.37seconds,3242280KB
peak. The main log contains no diagnostics; the checks log contains the nine
standard axiom reports. These are fresh checks of the two new source files,
using the already available prerequisite objects; no fresh replay of their
entire dependency closure is claimed. This is an author receipt, not an
independent peer review. No commits or central-document edits were made.
