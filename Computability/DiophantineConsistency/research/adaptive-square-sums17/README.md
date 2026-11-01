# Seventeen-variable degree-20 positive-rank witness

Starting from the sixteen-variable degree-24 equation, introduce a positive
coordinate `rankVariable` for the signed rank `R`. Use it in the main and
auxiliary residuals and add `(rankVariable−R)²` as an eighth squared residual.
The graph has 17 positive variables and 99 live unshifted binary operations.
Its eight residual degrees are 10, 10, 8, 10, 10, 4, 3 and 4. The top
homogeneous part is a sum of squares of the degree-10 residuals; the strong
residual has a degree-10 monomial `g²Y⁴eta⁴` with coefficient 1. A nonzero sum
of squares of real polynomials cannot vanish identically, so the exact output
degree is **20**, including after fixing the ports and positive shift.
`verify_degree.py` checks the sparse residuals and leading witness. This is an
integer-polynomial certificate, not a Lean degree theorem or minimality claim.

`AdaptiveRankWitness17` binds the literal definitionally to a one-hole
sixteen-variable context plus the squared rank constraint. It proves that
zeros project to the parent in every IΣ₁ model. For the reverse direction it
constructs a positive rank witness: projection to the 13-variable equation,
the transport bound and the signed-residue theorem prove that the actual rank
has a positive natural representation at the fixed ports. Its
`current_no_zero_iff` gives the resulting shifted no-zero equivalence. The
general arbitrary-port theorem retains an explicit positive-rank representation
hypothesis. `verify_literal.py` checks all 17 variable aliases, four ports and
99 Lean literal gates against the pinned graph. Normal Python and `python -O`
pass.

Two focused [Lean model replays](../../reviews/adaptive-square-sums17-model-replay/README.md)
match on the same historical parent. Transitive project, package and dynamic
ancestry remains inherited. The native iPRA endpoint for this expression is
separate work and is not established by the model receipt.

The separate [equation20.tex](../../equation20.tex) and
[equation20.pdf](../../equation20.pdf) show all 17 distinct positive unknowns,
eight squared residuals, the full base-10 fixed integer and 99 gates.
`verify_display20.py` parses all 28 displayed definitions and circuit rows,
checks the sum wiring and copied constants, and rejects two formula mutations;
it is a limited TeX parser. Normal Python and `python -O` pass. Two `pdflatex`
runs produced identical PDF SHA-256
`0530872703643dbb5b1f90679b4cb4ed3b80e41949f5f217b9fca173d1b33f88`;
both pages were visually inspected. The page states the model proof and the
pending native-iPRA endpoint separately.
