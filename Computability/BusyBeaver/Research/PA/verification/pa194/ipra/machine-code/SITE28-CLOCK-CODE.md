# Primitive-recursive clock for dynamic site 28

`PA194Site28DynamicClock.exactClock` gives one explicit model-valued clock for
the dynamic physical site-28 increment. `PA194Site28ClockCode.modelClock`
proves that its thirteen-input primitive-recursive code evaluates to that
clock in every PRA model. The step retains the structured repeated-one suffix
condition documented in `SITE28-DYNAMIC-COMPLETE.md`.

`check-site28-clock-code.sh` rebuilds both modules against the documented
staged physical roots and audits the selected input-object receipt and axiom
reports. Independent and repository-source staged replays passed. The retained
machine stages and general foundations are not rebuilt transitively; this
clock alone is not a coded complete loop or a consistency implication.
