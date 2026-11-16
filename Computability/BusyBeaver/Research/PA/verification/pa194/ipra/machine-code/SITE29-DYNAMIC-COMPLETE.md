# Site 29: increment with a model-length spare suffix

`PA194Site29DynamicComplete.complete` is the literal physical path-29-to-30
step, proved for each PRA model, an arbitrary model-valued suffix count, all
register values, the spare value, and the source-frame padding. Its
single suffix premise states that physical slot 10 is
`repeatOutput(count, 0)`: `count` identical one-valued trailing blocks with a
blank far end. The output increments logical register 6, preserves the other
register values and spare, and changes that suffix to
`repeatOutput(succ count, 0)`. The complete nested clock is in the theorem.
The model-length carry and return proofs use model open induction, so the count
can be nonstandard. The theorem does not cover arbitrary varied trailing blocks
or nonblank far ends.

The physical step composes `PA194Site29DynamicSelectedReturn`, the three
successive register/header returns, `PA194Site29DynamicReturnPath30`, and
`PA194Site29DynamicOutput`. The existing startup suffix satisfies the premise
at count 26 by `PA194OneSpareSeed26.modelSeed26` (separate seed checker).
This theorem does not yet compose the source controller, prove an unbounded
physical-machine simulation, or establish either consistency implication.

Replay into a fresh output directory with `check-site29-dynamic-complete.sh`.
Its positional arguments are printed by its usage. Supply the successful
`check-one-spare-file-roundtrip.sh` output as `DYNAMIC_CODE_STAGE` in place
of the old carry-code stage; it contains the same three carry-code objects and
the new model-length roundtrip. The remaining stages are those used by
`check-site29-complete.sh`. The checker compiles all dynamic source modules and
the existing start-interface sources, checks every reported axiom set for
`sorryAx`, rejects machine-object fallbacks and overlapping machine roots, and
audits that input objects did not change. It retains staged object inputs and
does not rebuild their entire transitive source closure.
