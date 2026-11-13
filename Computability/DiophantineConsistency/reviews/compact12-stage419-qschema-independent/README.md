# Independent stage-419 QSchema repair audit

The original stage 419 failed because Lean could not find
`InternalInterpretation.consistent_of_falsum_transfer`. The sole source edit
keeps the exact statement of `consistent_ZF_of_native` and replaces that call
with an inline proof. It identifies the quoted falsum codes, assumes a ZF
refutation, applies the existing `provable_falsum_native_of_ZF` transfer, and
contradicts the assumed native consistency. The source comparison checks that
no other text in the file changed.

The failed receipt reports exit 1 with that unknown-identifier error; the
retry reports exit 0 and an empty log. Both source snapshots, commands,
Lean binary, runner hashes, direct dependency lists, and all 60 recorded
dependency/companion guards were checked against the live files. The retry's
object hash is `7ab7b6088e1342086f8b8b105b5e5f886d7e927917d008481c52208f362e39e8`;
this equals the historical object hash in the cone, so object hash alone does
not distinguish the repaired producer from its earlier ancestry. The retry
receipt and repaired source hash provide the relevant producer distinction.

The new cone differs from the stage-317 cone only in QSchema's source hash and
byte count, plus added correction metadata. Its 425-module order is unchanged.
Following selected source imports, QSchema and its six in-cone descendants
are precisely stages 419 through 425. The audit checks the selected-source
dependency order; successful stage 419 does not by itself establish successful
rebuilds of stages 420–425 or a final iPRA join.

`observations/attempt01/` retains the independent finite check with exit zero
and empty stderr. This audit did not invoke Lean again and does not establish
full package-transitive, dynamic, or historical source-to-object ancestry.
