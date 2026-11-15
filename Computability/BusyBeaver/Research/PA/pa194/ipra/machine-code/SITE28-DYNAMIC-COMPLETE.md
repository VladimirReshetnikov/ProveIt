# Site 28: increment with a model-length spare suffix

`PA194Site28DynamicComplete.complete` proves the literal physical
path-28-to-29 step in every PRA model, for arbitrary model-valued count,
source-frame padding and register values. Its suffix premise is
`args 10 = repeatOutput(count,0)`: a model-valued count of identical
one-valued blocks and a blank far end. The output increments logical register
8, preserves the remaining registers, and replaces the suffix with
`repeatOutput(succ count,0)`. Its named exact clock is a nested composition
of the existing root and return clocks and the model-length carry clock.
The count can be nonstandard because that carry theorem uses model open
induction. The theorem does not cover arbitrary varied blocks or nonblank
far ends, and does not itself prove a controller bridge, unbounded simulation,
or either consistency implication.

The successful all-model-count carry/return stage is an input to
`check-site28-dynamic-complete.sh`; use its output as `DYNAMIC_CODE_STAGE`,
with the remaining stages as in `check-site28-complete.sh`. The wrapper
rebuilds the four existing site-28 source modules and the two dynamic source
modules, checks axiom reports, rejects overlapping or fallback machine objects,
and audits unchanged inputs. This is an incremental replay using retained
stages, not a fresh rebuild of their full transitive source closure.
