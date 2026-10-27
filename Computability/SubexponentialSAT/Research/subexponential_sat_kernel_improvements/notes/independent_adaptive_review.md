# Independent review of adaptive integral mode separation

## Verdict

The finite Smith-weight dominance theorem in `analytic_notes.md` is correct
under its stated scalar finite-chain-ring hypothesis. The inspected
`adaptive_modes.py` implements the described minimum-valuation elimination
without requesting additional precision after the input matrix is supplied.
The separation preserves the source/target locality required by the packet
recursion. Its guarantee is a smaller or equal abstract weighted tuple
inventory for the same actual block, not a universal wall-clock speedup and
not a new unrestricted SAT logarithmic exponent.

## 1. Algebraic hypothesis

The scalar ring is `R_p=(Z/2^p)[U]/f(U)`, with `f` monic and irreducible
modulo two. Every nonzero element has the form `2^e u`, where `u` is a unit
and `e<p`. Thus all ideals are powers of `(2)`, and this is a finite chain
ring. The code explicitly checks irreducibility modulo two. Its valuation is
the minimum binary valuation of the canonical coordinates, capped at `p`.

The theorem must be applied to the scalar crossing matrix `W`. It does not
apply without further argument to arbitrary matrices over
`R_p[V]/(V^ell)`: this larger ring has additional ideals and is generally not
a chain ring. Scalar mode coefficients can nevertheless act on tensor entries
in that larger ring, so the restriction is compatible with the source
algorithm and its nilpotent coordinate.

## 2. Elimination and working precision

Select a nonzero residual pivot of minimum valuation `e`. The entire residual
is divisible coordinatewise by `2^e`. Dividing its pivot row and pivot entry
at precision `p-e` gives a unit normalized pivot. Inverting that unit and
forming the normalized source row is valid. A canonical lift of this row to
precision `p` has an arbitrary ambiguity divisible by `2^(p-e)`. Every entry
of the target column is divisible by `2^e`, so the ambiguity disappears in
the rank-one product modulo `2^p`.

The source pivot coordinate is exactly one. Subtracting the target column
times the normalized source row therefore zeros the pivot column, and the
normalization zeros the pivot row. Previous zero rows and columns stay zero.
All residual entries remain divisible by `2^e`, so successive pivot
valuations cannot decrease.

These operations can equivalently be expressed as integral elementary row
and column operations, plus permutations and unit diagonal scaling. The
remaining block is exactly the Schur residual used in the program. Thus the
nondecreasing pivot valuations are the Smith valuations of the matrix modulo
`2^p`. Recording each removed outer product in original coordinates gives
an exact reconstruction.

The separator only receives and operates on the matrix modulo `2^p`. The
separate Cauchy-kernel constructor does use extra precision before dividing
the known interpolation denominator. These are distinct operations; the
no-extra-precision statement applies to separation, not to constructing the
original integral kernel from rational formulas.

## 3. Why arbitrary integral weighted modes are dominated

For each `q<=p`, the reduction of the Smith diagonal has

`r_A(q)=#{j:lambda_j<q}`

nonzero cyclic image summands. This is the minimum number of generators of
its image module, and equals its residue-field socle dimension. More
generally, for a finite module over a finite chain ring, the elementary
divisor decomposition is a direct sum of nonzero cyclic modules, and both
the minimal number of generators and the socle dimension count those
summands.

If `A=BC` has inner dimension `r`, then `im(A)` is a submodule of `im(B)`.
The inclusion injects their socles. Since `im(B)` has at most `r` generators,
the preceding equality proves `r_A(q)<=r`. This establishes the required
inner-rank lower bound. The submodule generator monotonicity used here is a
special feature of this finite-chain-ring setting; it should not be stated
for arbitrary rings.

Now suppose an arbitrary exact integral separation has terms certified
divisible by powers `2^(w_j)`, with positive `w_j`. Modulo `2^q`, terms with
`w_j>=q` disappear, leaving a factorization with at most
`#{j:w_j<q}` columns. Consequently

`#{j:lambda_j<q} <= #{j:w_j<q}`.

After sorting, `lambda_j>=w_j` for every adaptive mode index. Otherwise
choosing `q=lambda_j+1` would put at least `j` adaptive weights and fewer
than `j` comparator weights below `q`. The comparator has at least as many
nonzero modes by taking `q=p`.

Map each adaptive exponent tuple to the first equally indexed comparator
coordinates, with zeros in remaining coordinates. Its comparator weighted
sum is no larger. This injects the new budgeted inventory into the old one.
The injection preserves ordinary total degree as well. The theorem therefore
compares against a restricted padded basis even after zero modes are
discarded and all common source valuation is moved to its target.

This argument proves an abstract inventory dominance statement. It does not
exclude cancellations or additional problem-specific pruning in a full
solver, and does not say that polynomial elimination overhead is free.

## 4. Locality and recursive compatibility

The algorithm is run separately on one actual packet crossing orientation.
All its rows belong to one target group and all its columns to one source
group. Each recorded source vector defines a linear form on those same
columns; each target vector changes only coefficients on those same rows.
No port, edge, packet, or tensor vertex is added. The new packet tensor has
the same port set and degree as before, so the old child graph and
fresh-side-degree invariant remain applicable.

The chosen basis may depend on the interpolation value and working
precision. This does not obstruct interpolation: the exact evaluation is
preserved modulo that precision at every value. Newly generated tensor
entries are then frozen as canonical creation-time representatives, following
the existing rule. No cross-value polynomial dependence of the chosen basis
is needed.

For an `m` by `n` block, elimination uses
`O(m n min(m,n))` scalar-ring operations and stores `O(mn)` ring elements,
including the final mode vectors. Matrix entries, precisions, extension
degree and packet length are polynomially bounded in the root parameter, so
this remains polynomial preparation time and space in the relevant interface.

## 5. Independent exact fixture

The added `check_independent_fixture.py` constructs a full Cauchy kernel over
`Q[omega]/(omega^2+omega+1)` using a separate implementation with Python
`Fraction`. It directly multiplies all polynomial factors, computes rational
inverses, and reduces the final integral coordinates modulo `2^64`. It does
not use `Ring.mul`, `Ring.inverse`, or the modular kernel constructor to build
the oracle.

The fixture uses

- packet length `L=16`, node `t=1`, interpolation value `zeta=omega`;
- real rows `(0,4,12)` and real columns `(0,8,12)`;
- target precision 64.

The modular kernel agreed exactly with the rational oracle. The adaptive
outer products reconstructed that oracle using the independent rational
pair multiplication. The resulting weights were `(5,9,15)`. Independently
enumerated exact rational determinant minors had minimum valuations
`(5,14,29)`, equal to their successive partial sums. The checker and its JSON
result are included. No duplicate exhaustive suite was needed after this
targeted independent fixture and the algebraic review.

## 6. Comparison scope

The full padded Smith profile was already in the joint-Cauchy packet. The
new contribution relative to the reviewed corpus is applying minimum-
valuation separation to actual restricted row/column blocks, proving
inventory dominance over arbitrary integral comparators on that same block,
and providing an exact executable implementation. Smith normal form itself
is classical.

The closing repository review contains fifteen packets at commit
`6d3adc45061535ebe6fa7cd3d9b37dff7dcfc22a`. The last matching-refinement
packet adds a packing/schedule coefficient of 94.7482 and no actual-port
Smith separator or new coefficient extraction method. It does not change
this novelty boundary.
