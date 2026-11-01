# GG translation of the successor-induction body

`IPRAInductionGGBody` proves in Foundation's intuitionistic Hilbert calculus
that the actual `succInd` body translates to an equivalent body built using
intuitionistic implications and the translated matrix. The exact `x+1`
step and substitutions are retained. This does not yet close free parameters
or prove the translated closed induction axiom belongs to a native iPRA
theory. External transitive package/Foundation ancestry is inherited.

Run `python3 Computability/DiophantineConsistency/reviews/ipra-induction-gg-body-replay/replay.py`.

Author and independent peer PASS with identical source, object and full-log hashes for both modules.
