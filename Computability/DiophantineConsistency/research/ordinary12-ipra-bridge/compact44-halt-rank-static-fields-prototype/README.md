# Chosen calibrated rank from a model-internal halt

`CompactHaltRankStaticFields.lean` joins the checked halt-derived compact
word with the static-mask chosen-rank theorem. Its first premise is the
**model-internal** statement that the encoded machine's run at model time
`T` is halted. From this the theorem obtains the Σ₁-definable compact row
word at the chosen dimensions. It then produces a definable Boolean selector
with the stated positive, nonwrapping support, a pulsed `PackingInput`, and
the calibrated `windowRank` congruence.

The theorem still requires four physical properties of the actual base cell
family: its cell-plus-block bound, origin block positivity, and the two
high-mask no-carry fields. It also assumes the same four properties of the
pulsed family **uniformly for every** definable Boolean selector satisfying
the listed support conditions. These are substantive remaining premises,
not consequences of the halt condition in this result. No graph zero,
retained-byte binding, completed converse or internal iPRA theorem is claimed.

The bounded single-author build, tool session `11250`, exited 0 without
warnings or `sorryAx`; the axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. The direct dependencies, all 531
selected project-overlay slots and the separately selected controller,
symbolic-kernel and static-mask root files were unchanged across the build.
Before compiling, comparisons found no conflicts among 514 halt/project
overlaps, 29 shared halt/word `BusyBeaver` and `FirstOrder` files, 338
word/controller overlaps, 339 radix/overlay overlaps, 346 static/overlay
overlaps and 11 static/controller root overlaps. The complete preflight,
dependency listing, command, source/object hashes, compiler log and terminal
receipt are in `observations/attempt01`.

This is an author-side mixed-provider build, not a paired replay or a fully
authenticated dependency closure. Package, transitive, dynamic-loading and
between-observation ancestry remain inherited.
