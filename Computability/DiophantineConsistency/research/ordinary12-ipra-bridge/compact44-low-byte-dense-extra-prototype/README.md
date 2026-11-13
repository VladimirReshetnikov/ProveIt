# Three additional dense MC window regions

`CompactLowByteDenseExtra.extra_dense_byte` proves in Lean that the symbolic
MC byte window equals the existing periodic `denseWindow ((8*j)%67)` rule
on each of `[8233,8308)`, `[8401,8468)`, and `[8484,8635)`. These three
disjoint intervals contain 293 indices. Both adjacent 67-bit digits in each
window lie in the checked support and are not the special index, so the
earlier generic dense arithmetic lemma applies without expanding the mask.

A separate external checker compares the same Python-transcribed periodic
rule against those 293 bytes of the pinned retained parent `MC.bin.gz` and
reports zero mismatches. The successful checker source SHA-256 is
`b30e8f6d397db99ee9f81ac2494e9e92cbb8367d654d39598c5d076ac8f170b4`,
and its output SHA-256 is
`f2b853c419e830d5b2df1be2ebb6b24b23651b9f3277a44f22892cfec64f4b66`.
This is external provenance, not a Lean theorem about the file, gzip, or
equivalence of Python and Lean syntax.

The bounded mixed-provider author run `observations/attempt01` exited 0 in
3.070 seconds without warnings or `sorryAx`. Source SHA-256:
`128a3526ac948d3b9cfdc68ff117f773c1be727f3202008af342efc55519dcbf`;
object SHA-256:
`2754ab0971f602067d726d9f2b5117f8aed0d26027cf5ef7ca810914b3ec15e1`.
Direct dependency/companion guards and the separately inventoried generic
byte-window provider remained unchanged at the recorded points. This is a
single author-side check, not a paired replay or complete
symbolic/package/dynamic ancestry audit. Lean's reported `[propext,
Classical.choice, Quot.sound]` are metatheory dependencies, not iPRA axioms.

Together with the earlier disjoint prefix, dense, gap and tail results,
the symbolic coverage is now 73,617 of 73,759 byte indices. The remaining
142 indices lie in 12 short intervals; the separate results still need a
global Lean recipe and reconstruction proof. A parent-file, supplement,
PDF or iPRA equality is not established here.
