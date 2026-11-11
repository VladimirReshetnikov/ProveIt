# Positive74 three-residual quadratic screen

This read-only search starts from the SHA-pinned, Lean-checked 74-live-gate positive-coordinate circuit. For each of the ten triples of its five residuals, it tests forms

`Q = r² + s² + t² + b r s + c r t + d s t`, with `b,c,d ∈ {−1,0,1}`.

For `A = 4−b²` and `D = 8−2(b²+c²+d²)+2bcd`, it keeps the 23 forms with `D > 0`. The script checks, as exact integer polynomials for each form,

`4 A Q = A(2r+bs+ct)² + (A s+(2d−bc)t)² + 2D t²`.

Since `A > 0` and `D > 0`, `Q` is nonnegative over the integers and vanishes precisely when all three residuals vanish. Replacing their three squares by `Q` and leaving the other two squares gives an equation with the same zero set for all integer inputs and ports. It need not give the same polynomial.

Three deterministic samples modulo the checked prime 1,000,000,007 prefilter exact identities. For each triple/form, the script tries an existing wire, a one-gate expression, or a two-gate expression whose first gate uses existing source wires or integer literals −4 through 8, and whose second uses an existing wire or the first result twice. It includes both subtraction orders and permits noncommutative operands. It enumerates all three commutative addition-tree shapes joining `Q` to the other two residual squares, merges common nodes, and counts output-live gates. All tested target vectors are nonzero in all three samples, so excluding sample-zero wires as divisors cannot remove an exact multiplication match in this finite screen.

The control checks that the original first three squares already form the expected existing wire, that three addition-tree shapes are present, and that adding `(r+1)−1` to a residual raises the live count from 74 to 76. The recorded result tests 230 triple/form combinations, 1,053 sample-matching recipes and 3,159 output trees; none uses fewer than 74 live gates. Modular matches can be false positives, and any prospective hit would require an independent exact symbolic identity check. This bounded screen neither proves global minimality nor binds external JSON, TeX or PDF bytes to Lean. No Lean run is performed.

Run from the repository root: `python3 -I -S -B Computability/DiophantineConsistency/research/nine-sharing-sign14-positive74-triple-quadratic-search/search.py`. The program prints its deterministic receipt; it does not modify any files.

Independent review passed: [`reviews/nine-sharing-sign14-positive74-triple-quadratic-search-independent/`](../../reviews/nine-sharing-sign14-positive74-triple-quadratic-search-independent/). It reproduced the receipt and checked the positive-definite certificate and finite recipe/tree scope. The inflation control checks the expected existing-wire result, not a full rerun of the search on the inflated graph.
