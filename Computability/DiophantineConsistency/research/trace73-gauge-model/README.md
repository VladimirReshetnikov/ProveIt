# A conditional model-natural negative-`B` zero

`Trace73GaugeModel.positive_zero_to_negative_B` works in every model `V` of
the repository's `IΣ₁`, at arbitrary natural ports `p`.  Given a tuple of ten
positive elements of `V` whose actual literal 73-row graph is zero, it
constructs another such tuple at the same ports with `B<0` in `DiffRing V`.
The theorem explicitly assumes `1≤h`, `0≤p₁+v₅`, and that the original
center is strictly larger than `step=(p₁+v₅)(h+1)+1`, all in the difference
ring.  Its implementation applies the ordered-ring gauge theorem and uses
the nonnegative-representative theorem for `DiffRing V` to recover actual
model-natural coordinates.

This is conditional on the starting zero and center inequality.  Neither
existence of such a zero nor failure of the 73-to-75 existential implication
follows.  The result is not an iPRA derivation or a binding to the maintained
14-variable PDF.

The author check `attempt02`, tool session 67118, exited 0 and is reaped.
It produced `/tmp/trace73-gaugemodel-rnchgbdr/Trace73GaugeModel.olean`, SHA-256
`f7f468617d7925be67c798ba19f82ce9c03508e41b333ff569e10eac76bae65f`.
The theorem axiom report is `[propext, Classical.choice, Quot.sound]`.  Source
SHA-256 is `3fabcd4855d35807b053f2a647a139f1fd46bbc8005866b6724846461d6ced7e`,
runner SHA-256 is `5369625f82d04877f969d32791b31dec31ecc515028d58651e9f34c36817ed50`,
and terminal record SHA-256 is `7aa6777d803be2abd7e6c69ae754933fb4ba902360de4a15ea088666a4e7826e`.
Attempt01 failed on the orientation of the representative equality and is
retained as such.

The runner pins direct imported objects and selected shared objects, and
checks first selection of both direct imports and the two selected Mathlib
objects.  Remaining inherited project, package, dynamic and source-to-object
ancestry is not fully authenticated, and no independent Lean replay is
claimed.
