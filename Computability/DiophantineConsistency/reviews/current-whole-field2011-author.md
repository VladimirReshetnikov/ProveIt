# Current whole-field alignment: author receipt

This receipt records the complete author read and fresh kernel builds of
the two new Lean files. It is not an independent peer review. No frozen
dependency, shared documentation, umbrella import, or git commit was changed.

## Frozen files

Paths below are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentWholeField2011.lean` | 156 | `16c06800d326578b5898f2353229b574f2c0c8783bfadc362d517d34d2a5d079` |
| `Lean/DiophantineConsistency/CurrentWholeField2011Checks.lean` | 60 | `5a31aff2da1993be28dfb950d1a3761a73a3fd15b48375f74fa12779ab870c94` |

The main module imports exactly `CurrentDecodedWindow2011`,
`CurrentCopyParity2011`, `CurrentFieldOffsets2011`, `CurrentSouthShift2011`,
and `NativeFieldCycles2011`. The check file imports only the new main module.

Relevant frozen dependencies at this build:

| Module | SHA-256 |
| --- | --- |
| `CurrentDecodedWindow2011` | `fd52d069a146d13287cd7da987cc54117e19282efabba6c30c9b4a4f2a48b217` |
| `CurrentCopyParity2011` | `dc49658f1d9c448eca9ff969336cd5f64b4f64483b47b48d72f3a6bd0d928c8a` |
| `CurrentFieldOffsets2011` | `b44a1eb24d23bf9e744fee99531cab653c34029e41a3ab14386f95d72b60c683` |
| `CurrentSouthShift2011` | `256403c28ff13e2fb8585597a1931c1be8703f6726daaf3c5509cfbff5f8cf8d` |
| `NativeFieldCycles2011` | `9cac50de2b83d3b802eab615ab4340027b842abc910586d009c4847b913f8442` |
| `CurrentCellTranslation2011` | `c3e9811e9b5c60c8ed740b58277ed40569108f888347ffcbb84169ba31b5685d` |
| `CurrentOneHot2011` | `45e9cd33fb50e4fc16f524948fc2f68a4dfbd334dd64e7fda114b3c55946842c` |
| `CurrentPolynomialWindow2011` | `db64a1e9130d09d606f3262781be9a4c0d70db1a9cdb7482cd74ecc0ddf0b730` |

## Exact proved scope

Write `W = (Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat
- 47*(N*2011)`. With the original `CurrentPolynomialWindow2011.Facts`
for the same `v,x,c,carry,digits` as its only native premise,
`facts_whole_field` proves `(W/47)%2011 = 0`.
`facts_cell_aligned` combines this with the already derived fractional
phase to prove `W%94517 = 0`.

The composition is explicit:

1. The decoded literal Start has South complement510. A generic binary-word
   split at three bits proves its physical bits943 and944 are both1.
2. The actual marker and nine South-copy equalities are obtained from the
   original masks, carry recurrence, sparse support, Boolean digits and
   derived selector count. At the origin these give source ones at
   `1004-t`, `961-t`, `962-t`, where `t=W/47`.
3. `coarse_offset` leaves only remainders0,19,20. Its selector count is
   derived from the same Facts; no decoded occupation premise is used.
4. At remainder19, apply the actual South-word identity at `theta.symm b`.
   The resulting recurrence is oriented as
   `S(theta.symm b)=(2*S(b)+epsilon(b))%512`. The exceptional source bit
   is the actual physical selector941. `facts_terminal_south` makes its
   selected South word one fixed value from the literal table, without
   computing or restricting that value. The generic finite-permutation
   theorem excludes Start510, while permitting the real511 self-loop.
5. At remainder20, the two prefix bits have weighted sum at most2 because
   their translated physical cell has at most one selector. The generic
   residue theorem excludes Start510.

The final `polynomial_zero_aligned_window` takes only all14positive
variables and zero evaluation of `CurrentPolynomialWindow2011.polynomial`.
It obtains the original arithmetic window and retains exactly the same
`x,c,carry,digits` and complete `Facts`, augmenting them with alignment.
The focused checks also combine its alignment with the decoded-cell
theorem on those unchanged functions and derive actual divisibility by94517.

No occupation, unique-Start, all-marker-one, clean-clause, already-aligned
shift, upper bound on the shift, or target equivalence is assumed. This
packet does not yet prove a tiling/tableau language equivalence or Con(ZFC).
It closes the whole-field alignment step of the literal native inverse.

## Reproduction and audit

Both complete new sources were read before execution. From the repository
root, each command completed with exit0 on its first run:

```sh
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentWholeField2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWholeField2011.lean > /tmp/current-whole-field-stage1.log 2>&1
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentWholeField2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWholeField2011Checks.lean > /tmp/current-whole-field-checks-stage1.log 2>&1
```

Only one author Lean process ran at a time; both files disable asynchronous
elaboration. These commands rebuilt the new modules against the already
available frozen dependency objects, not the entire dependency closure.

The main log is empty, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log is SHA-256
`70626dc4253c9147b6f1a0ea02cadfb96d74bd0094a3508cef7e8ae832d9ce3d`.
All six printed theorem-axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, new axiom,
`native_decide`, omitted finite case, or imported executable certificate
in either new file.
