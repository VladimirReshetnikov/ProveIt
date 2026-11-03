# Model halt supplies a calibrated compact packing

`CompactHaltRankNoHigh.lean` proves in Lean that, in **every model of IΣ₁**,
the model-internal halt condition for the encoded machine at time `T`
implies the existence of a model-Σ₁-definable Boolean selector `δ` and a
full symbolic compact `PackingInput` for the corresponding pulsed cell
word, with the specified controller support and calibrated `windowRank`
congruence. The parameter `c` is an arbitrary model element. The chosen
length and stride are the powers defined by `haltLength T` and
`haltStride T`.

No physical high-mask, product, block-size, low-mask, or scalar-bound
premises remain in this theorem: it obtains the actual marked word from the
model-internal halt, derives the chosen geometry and `0 < haltStride T`,
uses the all-index ordinary high-mask theorem for both base and each
definable Boolean pulse, and transfers ordinary high safety to the special
origin field. It retains the selector's stated positive/nonwrapping support
in the conclusion and supplies the prior theorem's universal perturbation
obligation for **every** admissible definable Boolean selector.

This is a significant model-level construction, but it is **not** yet an
actual positive zero of the 12-variable graph, a proof of the converse
end-to-end, a binding of all retained coefficient bytes or displayed PDF,
or a Lean proof that the equivalence is derivable in iPRA. Those remain
separate tasks.

The first bounded attempt failed on one local definitional-equality
elaboration; its exact source and compiler output are retained in
`observations/attempt01`. The corrected single-author run, tool session
`55886`, exited 0 without warnings or `sorryAx`. The named axiom report
lists only `propext`, `Classical.choice`, and `Quot.sound`. Direct dependency
guards, all 531 selected project-overlay slots, and selected controller,
symbolic-kernel and static-mask root inventories were unchanged. Before
compilation the runner compared the full recorded provider overlaps,
including 514 halt/project, 29 halt/word shared-root, 338 word/controller,
339 radix/overlay, 346 static/overlay and 11 static/controller root entries;
all matched. The complete comparisons, inventories, source/object hashes,
command, dependency list, log and receipt are in `observations/attempt02`.

This is a mixed-provider author-side build, not a paired replay or a fully
authenticated dependency closure. Package, transitive, dynamic-loading and
between-observation ancestry remain inherited.
