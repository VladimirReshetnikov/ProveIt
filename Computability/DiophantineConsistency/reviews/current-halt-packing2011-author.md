# Actual halt to rank-forced native packing: author receipt

Author: `complemented47_review`. Main and focused checks are frozen after
complete self-read and successful first capped builds. This is an author
receipt, not an independent review of the composed dependency closure.

| New source | SHA-256 |
|---|---|
| `CurrentHaltPacking2011.lean` (73 lines) | `6ed64c4b270ba07ababf8412dfad7ea8d69d7fbcd005f7f403f65fd34b4ead4f` |
| `CurrentHaltPacking2011Checks.lean` (44 lines) | `c35a7a53174e3975a314effb509cab12d133bb3dba9855b3b262611789ddd46e` |

The three imports are `CurrentRankCalibration2011`,
`WangTiles942ControllerDimensions`, and `DecimalMachineZFC`. I read all128
rank-calibration lines, all51 of its check lines, the entire decimal ZFC
endpoint and its actual consistency definition in `Bridge.lean` before
writing this composition. The dimension packet is my preceding frozen
work. Source paths here are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Relevant frozen prerequisite | SHA-256 |
|---|---|
| `CurrentRankCalibration2011.lean` | `0f49fd9339d50e54d391427cc20ae2cbce450f1d4186bc6e3249dc305393e4a3` |
| `CurrentRankCalibration2011Checks.lean` | `ddd1ec8fa09118206e6729559a4bcb44c9350596a63a8319b959f5492f3f898d` |
| `WangTiles942ControllerDimensions.lean` | `ffdb29e9f5048c6a47bc63dc17276d709fa0ac44d854b6115d8797c884346425` |
| `DecimalMachineZFC.lean` | `778af71680ec6aadd9858d30ace87c25012ac6b9dac02e2a483094401fc06107` |
| `Bridge.lean` | `c57457f028f0fca0279a95deb3950665bb663473adeaae32b32c5fa772b24114` |

The transparent proposition `ExistsPacking wBound` retains all the actual
objects in one existential tuple. Its dimension is N=auxiliary^(k+1), with
positive rw, rw<k, d*auxiliary<auxiliary^k, and wBound<auxiliary^rw. The
actual indexed word a has unique Start at zero and literal matching at
the original stride auxiliary^rw. The tuple then contains S, carries,
normalized digits and R,r,t, with:

- positive support size bounded by d*auxiliary and positive t;
- literal matching for the same a at the forced stride t;
- full `CurrentNativePacking2011.Facts` for a, enabled S, t, and these
  particular carries and digits;
- the actual signed printed-rank identity for that same source and
  normalized integer;
- population `sigma 2 R = 3*(width*N)+2`, R%4=3, R=2*r+1 and R>2*width*N;
- the ordinary multiplier equality `multiplier t = 2^(R-width*N)`.

`halt_constructs_packing` first obtains the actual uniquely marked word
and all size hypotheses from the frozen controller-dimension theorem.
It supplies that same a to the frozen rank calibration and retains its
original matching and uniqueness alongside the resulting packing. No
desired support, normalized representative, mask acceptance, rank fact,
or marked word is a premise. The width bound remains arbitrary.

`blank_halts_constructs_packing` simply extracts the actual halting time.
`not_conZFC_constructs_packing` uses the fully qualified
`DiophantineConsistency.ConZFC`, whose definition is
`¬ BProv ZFCax_s [] Form.fBot`, and the exact
`DecimalMachineZFC.blank_nonhalting_iff_conZFC`. Classical contradiction
turns its negation into a literal blank-machine halt. No replacement or
placeholder consistency predicate occurs. This is an external Lean
conditional theorem; it neither asserts inconsistency nor formalizes an
internal ZFC argument.

This packet constructs a native packing, not a source-system zero or
polynomial solution. Auxiliary Pell witnesses and their final composition
remain separate. The focused checks explicitly unpack the transparent
existential and recover unique Start, the same-word packing Facts, actual
rank binding, residue and multiplier equality. Other checks retain
arbitrary width cofinality from either blank halting or the actual negated
consistency predicate. None asserts that the actual machine halts.

Both modules set `Elab.async false`; I read the complete new source/checks
before running them sequentially with `lake env lean -M6000 -j1 -o
.lake/build/lib/lean/DiophantineConsistency/<name>.olean
Computability/DiophantineConsistency/Lean/DiophantineConsistency/<name>.lean`,
under `/usr/bin/time` and redirected logs. Both first attempts passed with
no diagnostics. Main:2.84seconds, peak RSS3,345,988KiB. Checks:2.94seconds,
peak RSS3,338,692KiB. All three axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. There are no new axioms, `sorry`, or
`native_decide`, and no implementation correction was needed.

| Build artifact | SHA-256 |
|---|---|
| Main object | `6697824186c4c2a9a21bf15b44f27ceed9d0a7ad14181ee41cc4ab28c4ca13cb` |
| Checks object | `e9d9a68ec0d3c9e1dfe0fd845a189d98406c614363be4609ee274f4d8333fc85` |
| `/tmp/current-halt-packing-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/current-halt-packing-checks.log` | `3fbf6d9acc1f50d73e4f9db43f176befee614ea135358cd8c7545d1f7f85d9b7` |

Only the two new source files, their new objects, this receipt and temporary
build logs were written. No frozen prerequisite, umbrella, central document,
or Git state was edited. Independent review remains separate.
