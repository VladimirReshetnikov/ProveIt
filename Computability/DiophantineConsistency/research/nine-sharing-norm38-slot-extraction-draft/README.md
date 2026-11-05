# Uncompiled norm38 slot-to-static extraction draft

`Norm38SlotExtraction.lean` drafts the missing first extraction step from a
zero of the literal 38-witness seed to the generated static assignment's
`gatesHold` and `fiveNorms` predicates. It assumes a model of IΣ₁, a natural
witness vector, and explicit equalities between each integer coefficient cast
and its model-natural port representative. Its input is `Fin.cons 1 w`;
the distinguished coordinate is 0 and the 38 witness coordinates follow it.

The file contains 29 concrete slot identities: the 24 signed-pair component
residuals of the 19 materialized gates and the five graph norm residuals. The
proposed `each_slot_zero` derives a zero for each literal residual from the
separately drafted sum-of-squares theorem. The proposed `seed_zero_static`
then attempts to assemble all 60 gate equations (including definitionally
computed inline gates) and the five norm equations, in the `NormAssignment38`
order N0, N1, Na, Nt, scaled_Ns. `slots.json` records every source gate,
component, node index and slot.

**No Lean file in this packet has been compiled.** In particular, the 29
individual `simp`/`ring` scripts, list indexing, cast rewriting and final
conjunction assembly may require repair or splitting to fit resource limits.
The imported `SharingNormSquares` and `NormAssignment38` sources were later
compiled in the separately recorded `nine-sharing-seed38-weighted-retry`
run; their use by this new extraction source has not been checked. This
source makes no claim of a checked model bridge or iPRA endpoint.

`generate.py` pins the source graph and 38-seed JSON. `check.py` compares all
29 generated slot names and node indices against those inputs, checks the
norm-order assembly, and reruns the separate external free-ring comparison in
`reviews/nine-sharing-norm38-model-bridge-draft-independent/`. This is a
source and external symbolic check, not Lean parsing or proof validation. Run
`python3 -I -S -B check.py`; no Lean process is used.

Even if this stage compiles, the source-to-static topological graph theorem,
actual fixed-port casts, Delta scaling and cancellation, forward witness
construction, degree, Jones instantiation and consistency endpoint remain
separate work.
