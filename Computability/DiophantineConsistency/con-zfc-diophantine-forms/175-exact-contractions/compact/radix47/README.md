# Smaller complete coefficient tuple for the new compact equations

Two separate **whole complemented-label radix47** specializations of the
85-operation, degree-232 equations, still in ten strictly positive integer
variables. The largest fixed port has 415,904 bits; all four raw integers
total 207,214 bytes, compared with 295,388 bytes for the radix67 tuple.
Every port changes together. The new b² weight and its proof are inherited
from the parent directory's current construction.

The native coefficient reduction is prior work, not newly claimed here.
`PROOF.md` checks the exact native handoff and constructive controller for
this specialization. Its retained proof includes the complete changed
carry/controller argument; this is not the conditional47 layout.

```sh
python3 -B build.py --check
python3 -B verify.py
```

The coefficient recipe is complete in `coefficient_recipe.tex`. The
retained decoder checks all 943 tiles, 3297 coefficients, 51 target
identities and the actual arithmetic controller. The graph paths are in
`equations/`, with metadata paths relative to this radix47 directory.

This does not establish an end-to-end new proof-assistant formalization.
Its ordinary equivalence theorem composes with the named retained native
and syntactic-refutation calibrations, as explained in the proof.
