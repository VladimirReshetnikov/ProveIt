# Candidate: 26 variables, degree eight, 126 circuit operations

This candidate deletes `scaledIndexVariable` from the 27-variable graph and substitutes the existing `cSquareVariable * i`. It removes the corresponding residual, square operation and sum operation. `generate.py` pins the parent and verifies topology and liveness. `verify_substitution.py` checks by exact integer-polynomial arithmetic that all 17 remaining parent residuals agree after substitution and that the removed residual becomes zero. `verify_degree.py` checks all 17 child residual degrees and verifies exact degree 8 with a port-independent leading monomial. The graph SHA-256 is `d8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5`.

The witness maps delete the scaled-index coordinate or insert the positive
product `cSquareVariable * i`. The AQ28→AQ27→AQ26 [author-only Lean extension](../../reviews/aq26-author-trial-v2/README.md)
compiled the model transports and native endpoints; its [independent artifact
audit](../../reviews/aq26-author-independent-audit/README.md) passed. This is a
historical hybrid, not a matched peer or current-source result; the Foundation
wrapper's outer exit and inherited package-transitive and dynamic ancestry
remain qualified. A [standard-theory client](../ipra-standard-aq26/README.md)
also completed one separately audited author-only run in a single overlay.
The finite degree check is not a Lean degree theorem, and no minimum is claimed.

## Base-10 display

The [equation PDF](equation8-26.pdf) and its TeX source give the complete
126-operation circuit. The generator takes the pinned graph,
the displayed residual definitions and the existing base-10 fixed-constant
block. It retains 26 distinct positive-integer unknowns. The display validator
checks 39 definitions against exact sparse integer polynomials, all 17 square
terms and all 126 circuit lines, plus negative controls; the separate literal
checker binds the gate list to the AQ26 Lean draft. These finite checks do not
substitute for a Lean proof of degree or for a matched replay. The displayed
client status refers to the [single-overlay author result](../../reviews/ipra-standard-aq26-combined-author-trial/README.md).
An [independent presentation audit](../../reviews/equation8-26-independent-audit/README.md)
checked the formula, circuit, aliases and reproducible PDF. It retains the
manual transcription boundary for the fixed TeX decoder and rank recipe.

Run `python3 build_display.py` in this directory. It regenerates TeX, runs the
finite display check, builds the PDF twice in clean temporary directories,
rejects TeX warnings and requires byte-identical builds. With the installed
TeX Live 2022 toolchain the resulting PDF SHA-256 is
`47a78ee00d5868e383e4de6e7ea2ad829e8a85385f5b9486837c1450a2af5310`.
Substitution and degree checks and `../adaptive-aq28-27-proof/verify_literals.py`
were also run; none of these scripts alone establishes the internal theorem.
