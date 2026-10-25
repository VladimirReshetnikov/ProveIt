# Pell doubling and a single product-square test

`equation_85.json` is the principal new polynomial: ten strictly positive
integer unknowns, exact degree 328, and 85 binary arithmetic operations.
The companion `equation_84.json` saves one more operation at exact degree
436. Both retain the whole four-integer coefficient tuple of the pinned
89-operation/degree-288 source.

The displayed formula and full new unbounded proof are in `PROOF.md`.
The structural identity is

    a=Delta U^2 E, F0=1+a, G=E F0,
    Fsq=1+4aF0=(1+2a)^2,
    Q=Delta(Fsq-1)=4 Delta^2 U^2 G.

Because Q is a multiple of G, the auxiliary quantities Q-1 and QV^2-1
are both coprime to G. One product-square equation consequently forces
G to be square. Splitting its coprime factors recovers the first Pell
root and a seed root; their Pell double provides the accepted strong
pair. This removes the two-root norm without adding unknowns.

These are operation/degree tradeoffs, not a claim of global minimality
or a smaller variable count. The ordinary consistency equivalence uses
the explicitly retained whole indexed native/source calibration. No
new end-to-end Lean proof object or consistency proof is supplied.

The incoming eleven-integer product-square construction is credited in
the proof and retained for comparison. The new ingredient is the use of
Pell doubling to make Q automatically divisible by G, removing its
earlier A-times-main-radicand saturation. Neither the product-square
idea nor the classical doubling identity is claimed as historically new.

Run `python3 verify.py` to reproduce the finite checks. The verifier
needs only Python's standard library. It can save a receipt with
`--output path.json`. All four literal coefficients and their exact
identities are included. The retained provenance identifies the parent
commit and ordinary proof interfaces.

Each circuit row is `[name, operation, left_operand, right_operand]`.
An integer operand is a fixed literal; a string names an input, fixed
port, or preceding row. The `N` output is the single final polynomial.
There are no division, square-root, exponentiation, or hidden
existential operations in the literal evaluator.
