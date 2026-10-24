# A secondary 13-integer degree reduction

The equation in `equation.json` has 13 unrestricted integer unknowns, exact
total degree 1072, and 195 live binary additions/subtractions/multiplications.
It lowers the incoming CRT1088 construction's degree by 16 without changing
its dimension, whole coefficient tuple, or operation count.

The new mechanism is the existential replacement

    v^2 Pair(G,T,t)=Pos(p1,p2,p3)

by

    Pair(v^2 G,T,t)=Pos(p1,p2,p3).

Both express exactly `v!=0 and G>0 and T>0`, but the second has smaller degree
when T has substantially larger degree than v^2G. `PROOF.md` supplies the
unbounded argument, including compatibility with the parent's radical norm.
This is a degree-only improvement, not a global simplicity optimum.

## Standalone reproduction

Python 3.10 or later and its standard library suffice. From this directory:

    python3 build_reanchored.py
    python3 verify_reanchored.py
    python3 -O verify_reanchored.py

The builder rewrites only the new `equation.json`. The checker authenticates
all retained inherited files, rebuilds the literal graph, verifies the exact
weighted degree and leading coefficient, authenticates the fixed numerical
coefficients, and performs finite transcription diagnostics. It writes only
the new `AUDIT.json`. No network, repository checkout, or absolute source path
is needed. `section.tex` is a short LaTeX supplement for the main report.

## Complete retained dependencies

`upstream/con-zfc-root-fusion-2026-10-24/` is the complete unmodified extracted
parent package, including its LaTeX/PDF proofs, exact coefficient payloads,
finite coefficient recipe, machine/tile data, ordinary calibration references,
and inherited license/notice files. `SOURCE_PINS.json` binds its original ZIP
identity and its complete manifest. It is retained for mathematical evidence
and reproducibility; the supported commands for this new reduction are the
three commands above.

The interpretation as Con(ZFC) inherits the parent's ordinary native/Pell and
K215 calibration theorems. No new end-to-end Lean/Rocq certificate or encoded
object-language ZFC proof is claimed. The new universal statement is the
existence-preserving arithmetic reduction, together with the explicit degree
and circuit measurements. Finite tests do not prove unsolvability.

## Attribution

The new guard placement, proof, literal adapter, and checks were prepared by
the AI research collaboration for Vladimir Reshetnikov. They use the repository's
MIT No Attribution license in `LICENSE`. The complete parent package retains
its own notices under its root and `licenses/` directories. Existing guard,
Pell, radical-norm, and coefficient-calibration results remain attributed there.
