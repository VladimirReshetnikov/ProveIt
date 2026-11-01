# Direct positive square witness: degree 30, 90 operations

The earlier 91-operation, fourteen-variable candidate used the positive
coordinate `squareVariable` to represent `V²+1`. Here it represents `V²`
directly, removing the `-1` operation. The fifth squared residual enforces
`squareVariable = V²`. The resulting pinned graph has 14 positive variables and
90 live unshifted binary operations (49 multiplications, 22 additions and 19
subtractions). Its five residual degrees remain 15, 13, 8, 10, 12, so the
polynomial has exact degree 30 after fixing the actual ports and after positive
shift. `verify_degree.py` checks the sparse residuals and the nonzero leading
coefficient; this is not a Lean degree theorem or a minimality claim.

The direct variable must be positive. `AdaptiveSquareWitnessDirect14` proves
that the signed ordinate has positive magnitude at every positive 13-variable
zero under the stated fixed-port bounds: the actual signed-residue theorem
places that magnitude at a nonzero residue. It then constructs the direct
positive square witness. `current_no_zero_iff` proves both zero-existence
transfers at the actual fixed ports in every IΣ₁ model. The corresponding
arbitrary-port theorem retains an explicit positivity hypothesis; it is not
claimed unconditionally. `verify_literal.py` compares all variable aliases,
ports and 90 Lean literal gates against the pinned graph.

Two focused model replays match; see
[the replay receipt](../../reviews/adaptive-square-sums14-direct-model-replay/README.md).
They reuse the same historical provider and inherit transitive project,
package and dynamic ancestry. A native iPRA endpoint for this direct variant is
still to be proved and replayed; the model equivalence alone does not establish
that endpoint.

The separate [equation30-direct.tex](../../equation30-direct.tex) and
[equation30-direct.pdf](../../equation30-direct.pdf) present the direct-square
variant, its 14 distinct positive unknowns, the complete base-10 fixed integer,
and all 90 gates. `verify_display30_direct.py` parses 25 displayed definitions,
checks the five-square wiring and all circuit rows against the pinned graph,
confirms the copied fixed constants and rejects two formula mutations. It is a
limited parser, not a general TeX interpreter. Normal Python and `python -O`
pass. Two `pdflatex` runs produced identical PDF SHA-256
`d6b24e6b070a9f4e26dadcc01567fafdd512d1d69a4d1db86260da36b6489049`;
both pages were visually inspected. The page separates the checked model
result from the pending native-iPRA endpoint.
