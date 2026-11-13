# Independent review of fixed compact-port rank window

**PASS within recorded captured-provider scope.** The no-Lean `check.py`
checks both recorded outer and Lean child exit, the terminal and retained
source/runner/object copies, log, result, process status, all recorded direct
guards, and the generic-window object against its successful producer
receipt. The two other direct inputs, `CompactSymbolicMaskData` and
`CompactGenericPortProjections`, are pinned captured objects: this review does
not independently establish their source-to-object or full transitive
ancestry. The only reported Lean axioms are `propext`, `Classical.choice` and
`Quot.sound`. This is neither a Lean replay nor a source-only closure rebuild;
dynamic and between-sample ancestry remains inherited.

The theorem assumes an `IΣ₁` model and an actual positive 72-graph zero at
the tuple `(betaNat,K,lowNat,betaNat+highNat)`, with an arbitrary natural
`K`. It concludes that the actual graph rank `R` is positive and that
`ι(R)+1<ι(q)^4` in the model's difference ring. The tuple wrapper is defined
before it is made locally irreducible, and three separately proved
projections identify ports 0, 2 and 3 with `betaNat`, `lowNat` and
`betaNat+highNat`. The captured static mask theorem supplies the two
inequalities needed by the generic rank-window theorem. The wrapper's
irreducibility is an elaboration setting; the definition still specifies
the displayed tuple.

The theorem does not claim `q≥33`, `2R<c`, the first-index congruence, a
reverse witness map, an existential equivalence, or an iPRA endpoint. The
source header calling it a source-only draft is retained byte-for-byte; the
successful attempt02 establishes the recorded checked status. Earlier
failed attempts are not used.

Run while the captured temporary provider paths remain present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-compact-rank-window-independent/check.py
```
