# Two multiplication savings in the complete shared macro compiler

Factoring the two actual native first coefficients lowers the best complete
fixed-table matrix polynomial from **414 = 169M + 245A** to
**412 = 167M + 245A**. Its comparison source costs **272 = 120M + 152A**,
with the same 47 equations and 75 positive witnesses. Combined with the
[shared macro controller](group_macro_automaton_sharing.md), this is a
31-operation saving from the earlier 443-operation private-path source.
The fixed macro fixture is not an instantiated universal alphabet; 412 is
not a new numerical universal bound. The established universal bounds are
unchanged.

The [helper](group_macro_factored_coefficients.py) and
[receipt](group_macro_factored_coefficients.json) apply the already proved
[native first-coefficient identity](native_pell_factored_first_coefficient.md)
to both literal cones in each of the five complete saved matrix sources.
The identity itself is not new. Its application here includes the actual
supplied-index interfaces, complete downstream sources, and paid finalizers.

## Exact local identity and its actual ports

Write X=wn2, Y=sn2, E=XY and V=kY in either the `selection__` or
`geometry__` namespace. Here k is the supplied positive auxiliary, not a
computed sum of other witnesses. The original four coefficient gates are

    E2 = E*E
    coefficient = E2+X
    V2 = V*V
    L9 = coefficient*V2.

Keep the already paid E and V gates, and replace those four gates by

    L = E*V
    next = L+k
    L9 = L*next.

Both expressions expand to

    X^2*k^2*Y^4 + X*k^2*Y^2.

This is an identity in the independent indeterminates X,Y,k over every
commutative ring. It saves exactly one multiplication and changes no
addition count in each cone. The comparison remains literally
`L9 = tau*(tau+1)`; the triangular root is unchanged. Substituting
`eta+zeta` for the supplied k would not be an all-value identity, even when
another retained equation imposes that relation at accepted zeros.

The helper authenticates the entire original producer pattern, the actual
supplied k, and the unchanged triangular comparison. It checks that the
three deleted private registers have only their intended consumers and
never escape into a comparison. Replacement names must be fresh. The
remaining source rows retain their names, operands and order. After the
two proved L9 identities, induction through those identical rows proves
all 47 residuals and the complete sum of squares identical on every
supplied tuple. This is stronger than equality of positive zero sets for
each fixed graph and flow schedule.

## Complete costs and scope

| Graph and flow | Comparison source | Full polynomial | Positive witnesses | Degree upper bound |
|---|---:|---:|---:|---:|
| Separate, dense |350 = 156M+194A|490 = 203M+287A|83|304|
| Separate, general grouped sums |304 = 132M+172A|444 = 179M+265A|83|304|
| Separate, private paths |301 = 130M+171A|441 = 177M+264A|83|304|
| Shared, dense |290 = 130M+160A|430 = 177M+253A|75|208|
| Shared, general grouped sums |272 = 120M+152A|412 = 167M+245A|75|208|

Every form keeps the paid finalizer of 47 residual subtractions, 47
squares and 46 additions: 140 = 47M+93A. All rows and supplied coordinates
are live. The receipt reports freshly propagated degree upper bounds;
this helper does not separately prove exact degree. Exact polynomial
identity preserves any independently established exact parent degree.

The ordinary input is still x with paid index `24*x+12`, and the endpoint
is still the original `diag(L_r,L_r)` matrix. Every controller edge,
positive hat, checksum, flow comparison, physical selector, history
condition, and linked geometry condition is unchanged. Both graph sizes
retain the paid margin `16+controller__radix_beta=B`. The actual native
scale and its paid power gates are unchanged within each source.

All supplied auxiliary coordinates remain strictly positive; computed
registers may be signed away from zeros. The identity gives the identical
full positive zero set and the identical native extension witnesses for
each parent form, so the parent's soundness and positive completeness
proofs transfer directly. Across the separate and shared graphs the
parent's equivalence remains existential ordinary-input language
equivalence; no cross-graph polynomial identity or full witness bijection
is asserted. This does not modify the later one-kernel/projective compiler.

## Reproducible evidence

The standard-library helper authenticates six predecessor files before
reading the saved complete parent sources. It imports or executes no
historical helper. It verifies both coefficient products using exact
three-indeterminate sparse coefficients, then proves five whole-source
polynomial identities, 235 residual identities and 2,197 common computed
register identities. It independently recounts all 2,217 paid live gates
in the five resulting polynomial sources.

Supplementary evaluation covers 60 complete integer/rational tuples,
including 20 rational cases. Ten deliberate off-zero diagnostics set
supplied k=3 while eta=zeta=1, detecting the incorrect computed-k
substitution. These are algebraic identity tests, not claimed native
Pell witnesses or accepting matrix computations. Unbounded acceptance
continues to rely on the complete parent's proof, transferred by the
all-value identity.

The CLI is a bounded source-pinned research artifact, not a maintained
general packet API. Run with assertions enabled, from any directory:

```sh
python3 /path/to/group_macro_factored_coefficients.py \
  --root /path/to/native-stream-queue \
  --expect /path/to/group_macro_factored_coefficients.json
```

The deterministic receipt records its source hash, every dependency pin,
all five complete source arrays and current ledgers. The previous ledgers
are retained only under the explicit `parent_ledgers` key. No frozen
predecessor bytes are changed.
