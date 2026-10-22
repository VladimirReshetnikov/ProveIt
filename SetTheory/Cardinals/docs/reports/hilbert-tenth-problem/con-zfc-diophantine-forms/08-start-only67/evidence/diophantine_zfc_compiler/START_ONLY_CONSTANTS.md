# Separate start-only specialization

This is an alternative to the fixed-input recipe in `CONSTANTS.md`, not an
in-place change to it. The machine, 4366 underlying tiles, local predicate,
window-enumeration bound and all compiler formulas remain exactly the same.
Only the ordering of the first two allowed windows changes.

## Exact window order and target ports

Let S be the original Start window. Let

    F_forbidden=(7,7,7,7,7,7,7,7,7),
    7=tile(0,q0).

Enumerate S first, F_forbidden second, and then all other allowed windows in
lexicographic order. The count k is unchanged because the underlying set of
windows is unchanged. However the selector coefficients depend on the ordering,
so DC and Kconstant must be redefined using this new ordering. Do not mix the
fixed-input Kconstant with this start-only polynomial.

The resulting compiler has the same explicit bounded formulas from the annex,
with this replacement window sequence. Its source has no input-loader numeral
and identifies C=Z. The four actual target ports are

    Bm1=B-1,
    Kconstant=DC+B DR,
    MC=B-1-sum_(e in E,e!=1) R^e-2R^e_star,
    MF=M_F^src=M_F^native+B-1.

The target MF is the shifted source mask, not the native field mask.
`start_only_constants.py:emitted_start_only_ports` enforces these bindings.
The corresponding bounded expression graph is `start_only_expression_dag.json`.

## Why forbidding the new window1 does not exclude genuine computations

F_forbidden is locally valid. It has no boundaries or initialization phases,
and its central q0/read0 instruction is the explicit stationary nonhalting
self-loop. The neighboring heads also stay and send no incoming head to the
center. Its exact centered update therefore preserves the center tile7.

F_forbidden never appears in a canonical initialized run. On the first row,
q0 occurs only in the phase-Q tile, index4, carrying symbol1, not in any ordinary
tile7. The first transition goes to q1. Every transition from any state other
than q0 has target other than q0: this includes malformed self-loops, all prefix
states, all simulated states (indices>=4), and the absorbing halt. Therefore
no ordinary tile carrying q0 ever occurs on a later canonical row. A fortiori
the all-tile7 window never occurs. This argument is independent of the K215
halting question and is checked over all 4340 relevant transitions.

## Why only Start is needed

In the half-binomial mask proof, with C=Z, the low mask still enforces an origin
Start through the condition on C-1. It forbids selector1 everywhere. The center
bands, four anchors and copy tests recover a valid periodic plane containing
Start. The finite-rectangle proof in `CONSTANTS.md`, Section3a, already uses only
this Start occurrence: its adjacent initialized Q, horizontal periodicity,
boundary propagation and vertical periodicity locate a finite initialized
rectangle. Exact updates and no-escape give a genuine finite halting run.
The fixed normalization erases every unary input, so any such run is equivalent
to blank-input K215 halting. Neither an End marker, uniqueness of Start, nor
an input-distance equation is required for this soundness implication.

For completeness, use the same canonical u=3 initialized halting tableau with
independently large power-of-five width and height. It contains one Start and
contains no F_forbidden, so the low mask is satisfied with C=Z. The genuine old
End window is now just an ordinary allowed selector and is not forbidden.
The existing five-adic Boolean dummy adjustment still works: it changes no
window selector, and the optional high-monomial correction is recomputed from
the new coefficients. It keeps the unique canonical Start, so the exceptional
origin tests and other low field bits in the half-binomial mask proof remain
valid. All ordinary raw field bounds and strict positivity margins are unchanged.

## Scope and reproducibility

    python start_only_constants.py --receipt start_only_audit.json \
        --symbolic-spec start_only_expression_dag.json

This checks the forbidden window, its canonical exclusion, and the exact
source-mask port binding. It imports only the newly written, separately audited
`explicit_constants.py`, not an upstream checker. The original fixed-input
files remain unchanged and reproducible.

These files specify and justify the separate compiler/semantics adapter.
The algebraic elimination that produces the final start-only equation is a
separate artifact and must be audited independently. No claim of global
minimality, decimal coefficient expansion, or new proof-assistant formalization
is made here.
