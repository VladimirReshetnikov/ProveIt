# Native iPRA physical-loop sentence

`PA194ActualPhysicalOrbitSentence.nativeIPRA` proves a universally closed
primitive-recursive equality in native `standardTheory`, the native iPRA
theory used in this development. Its input has nine source registers, an
independent controller tail, padding parameter, suffix count, and spare value.
The left side runs the literal encoded PA194 stepper for an explicit PR
cumulative clock from the coded site-27 frame. The right side is the coded
site-27 frame after `r0` iterations: the source register 0 is `r0−r0`,
registers 6 and 8 have each grown by `r0`, the gap by `r0`, and the count of
one-valued trailing blocks by `2*r0`. Other registers and the independent
controller tail are retained. The suffix beyond those blocks is blank.

`PA194ActualPhysicalOrbitCode.completeLoop` is the model-level frame equality
used for the sentence. `modelSentence` proves it in every PRA model,
`classicalPRA` obtains the classical formal proof by completeness, and
`nativeIPRA` transfers this universally closed equality to native iPRA. All
four theorems' axiom audits report `[propext, Classical.choice, Quot.sound]`,
without `sorryAx`. The native theorem handles this particular physical loop;
it does not yet provide the site-31 physical exit, a full source-machine
simulation, or either consistency implication.

`check-actual-physical-native.sh` extends the independently passed
`check-actual-physical-orbit.sh` source replay by building the two additional
sources above in the same temporary output and auditing all four printed
axiom reports. Its 26 arguments are exactly those in the invocation documented
in `ACTUAL-PHYSICAL-ORBIT.md`. The staged replay exited 0; see
`/tmp/pa194-actual-physical-native-check.log`. The selected physical machine
and foundation objects are retained prebuilt inputs; pinned object, overlap,
and unchanged-input audits do not authenticate their full transitive source
closure.
