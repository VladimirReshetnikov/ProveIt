# Blank-tape startup followed by the first two source branches

`PA194SeedZeroThenPositive.seededZeroThenPositive` composes the checked 58,154-step blank-tape startup with the model-uniform physical site-25 zero branch and site-27 positive branch. It states the result as three nested literal-stepper applications, with the exact startup, first-branch and second-branch clocks, and the complete source-file suffix retained. The resulting state-24 root has the source path 28 and the source file in which logical register 0 has been decremented from 2 to 1.

The proof checks both seed branch hypotheses, `e 8 = 0` and `e 0 = 1+1`. Startup has a 47-zero block immediately after the first path bit. The actual six-bit site-25 path is `100000`; five zeros belong to that path, leaving a 42-zero run. Accordingly the general two-step theorem is instantiated with `k = 39`, since its initial zero run has length `k+3`. The proof uses model-uniform zero-run successor identities for this alignment; it does not assume a blank suffix.

`check-seed-zero-then-positive.sh` recompiles the two preceding site-25 modules, the general two-step theorem and this seed theorem against the pinned site-27 coherent baseline. It checks the four source hashes, required axiom reports, absence of `sorryAx`, and baseline objects before and after. Its arguments match `check-zero-then-positive.sh`; the seed source must be beside the composition source. The baseline manifest and object receipt do not establish its original provenance: the underlying coherent builds and general foundations must be reproduced or otherwise trusted.

This is an all-model nested physical-stepper result. It is not yet a native iPRA sentence, an arbitrary-length simulation, or either direction of the desired consistency equivalence.
