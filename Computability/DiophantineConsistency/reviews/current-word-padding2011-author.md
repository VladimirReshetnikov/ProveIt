# Constructed padding acceptance: author receipt

The new packet proves all 916 actual padding tests for the assembled current
2011-field word. It accepts arbitrary Boolean dummy and marker maps, an arbitrary
tile assignment, and any natural whole-cell stride. It does not request tile
matching, a marked origin, a high-mask test, a small whole reflected digit, or a
supplied carry solution at its existential endpoint.

This is the author's receipt, not an independent review. The same author wrote
the reused reflected-geometry and high-digit modules and separately reviewed
the constructed-word, clause, carry, and top-bound interfaces. No frozen source,
maintained equation, shared documentation, or git state was edited by this task.

## Frozen source binding

Paths below are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentWordPadding2011.lean` | 224 | `dcf9b865df831b0c7f4de2aa0e9060c88fd62d6fae2dd0497ea0aa2f36c6b6d7` |
| `Lean/DiophantineConsistency/CurrentWordPadding2011Checks.lean` | 83 | `14d194ed4f7978b01772b00f397fd3ee7bc1c4902ec70dc37b823a54746bbf09` |

The main module's sole direct import is `CurrentWordClause2011`, SHA-256
`df93b7dc684693e23097e5bfdba9aa3a9121595574b6026832d2a4f3f2fd24dc`.
Important transitive source bindings are:

| Module | SHA-256 |
| --- | --- |
| `CurrentReflectedGeometry2011` | `268ecac628932a93d79593ae0b4e1c8819817db58f27ec9613c4ad23a29d60c1` |
| `CurrentCarryConstruction2011` | `6efd60cd1ce0f40aa48e68ec7d9c2b2c680bbdc0aa289488c268e79fa68a026a` |
| `CurrentWordConstruction2011` | `9455d6c2015906a8f76ff2be5275a95cae5340f0ca3e8dc16666ffc6bab2b5b8` |
| `CurrentClause2011` | `a76daeaa24d3b3b00cfb80e2aaa3c9082740f9f8349a8d18014c912a9001c566` |
| `CurrentHighDigits2011` | `ff6eb32b735f59989d7b21ed835f4c64b5a8bed206a9a4b96a54f25016c35d02` |
| `CurrentKernel2011` | `6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55` |
| `PaddingStaircase` | `b75d9c9cf430b4e3f8b020246c75eefd9c367f740cc6b1a99bc5de4859fb4932` |

## Proof and assumption audit

For every padding position `h ≤ 916`, every active reflected source has physical
offset `h + position e - 1005 ≤ 896`. The support theorem removes negative
sources. Full position injectivity and the physical selector-prefix sum bound
therefore bound the sum of active inputs by one. Actual doubled selector
coefficients are 2 modulo 2048, and all doubled control coefficients are 0.
The complete reflected sum consequently has residue 0 or 2. The generic theorem
keeps its support and physical count assumptions explicit; the assembled-word
theorem discharges both and permits arbitrary numeric control values for this
reflected-only conclusion.

Bare 1004 always reads an unsupported residue `1007+h` here. Bare 18, bare 2020,
and the whole-cell temporal input each contribute at most one when controls
are Boolean. Thus the full raw residue modulo 2048 is at most 5. This is a
residue estimate, not an estimate that the entire raw digit is at most 5.

`normalized_padding_residue` uses the actual `Facts.decomposition` equation.
`low_carry_zero` derives the incoming zero at `h-1`, including `h=1` and `N=1`.
The outgoing carry disappears modulo 2048 because the actual radix is
`2^47`. No incoming-zero, outgoing-zero, or high-mask premise is supplied.
`bit3_clear_of_residue` uses the actual test-bit/modulo identity, so the
result remains valid for large normalized digits.

`padding_mask_pass` identifies the actual repeated high-mask digit as 8 at
every `1 ≤ h ≤ 916`; these positions cannot be the exceptional origin.
`exists_padding_normalization` first constructs a carry solution using the
accepted cyclic-carry existence theorem and then proves every padding test.
It needs neither `MarkedWord` nor horizontal or temporal matching. Conversely,
this packet does not assert the origin, copy, clause, or entire packed high mask.
It makes no controller, machine-to-equation, or consistency equivalence claim.

## Fresh verification

The complete source was read before the first execution. The final main and
checks were read in full after the development fixes. Both files set
`Elab.async false`. Final commands, from the repository root, were:

```sh
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordPadding2011.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordPadding2011.olean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordPadding2011Checks.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordPadding2011Checks.olean
```

Both freshly compiled successfully. Existing prerequisite objects were reused;
no dependency replay or cache mutation is claimed. Main took 5.03 seconds with
peak RSS 3,284,068 KiB; checks took 3.38 seconds with peak RSS 3,248,700 KiB.
The main log has no diagnostic. All 11 axiom reports contain only `propext`,
`Classical.choice`, and/or `Quot.sound`. Neither file adds `sorry`, an axiom,
or `native_decide`.

The checks cover the first and last padding fields, source bound 896,
unsupported bare-1004 wrap at `N=1` and `N=2`, non-Boolean controls for the
reflected-only theorem, all-one Boolean controls, 17 full periods at `N=1`,
zero stride, and an actual constructed normalization. Numeric controls verify
that a large digit with residue 5 passes bit 3, whereas bit 2 is not justified
by that residue bound and residue 8 fails the tested bit.

Development corrections were confined to these new files: opening the actual
binary-rotation namespace, explicitly typing quantified natural offsets,
removing an unused section instance, and fixing the order of terms in an
internal `change` expression. The wrong-order expression triggered a
definitional-equality timeout; a diagnostic increased-heartbeat run was stopped
and the final source returned to the default heartbeat limit. No theorem
assumption was strengthened to fix a build.

Final artifacts:

| Artifact | SHA-256 |
| --- | --- |
| Main `.olean` | `10a60362a1356af83ee7ff48e7fbc51c617fc63f11e5b6a4667a965695c47ae8` |
| Checks `.olean` | `c52d76f4f29b934f6947bd2349ec0546ae5018c44ded382ec6551c307eca62bd` |
| `/tmp/current-word-padding-main-stage3.log` | `d759102041a108179a86f579b24c9f6dcfff617d6e23a811a2c796f332b73014` |
| `/tmp/current-word-padding-checks-stage1.log` | `862b34beb4e54daf84155e5e6ad2c380917b503bfb425c4b641af3fa083771b6` |
