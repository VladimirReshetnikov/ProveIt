# Consistency bridge and concrete nine-variable specialization audit

Repository pin: `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.
This note records a source audit and the construction developed in this task.
It is not a claim to have rebuilt the entire Lean/Rocq projects.

## 1. Exact K215 endpoint

`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md`
reports the same literal 215-state dense machine in the two proof lanes,
with dense table SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.

The actual Lean source
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`
contains

```
blank_halts_iff_zfc_refutation :
  BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot
```

and its negated consistency theorem. The RHS is finite syntactic
refutability, not merely failure of a bounded proof search.

`KEndpoint.lean` composes the binary machine simulation and C222 derivation
endpoint with `c222_iff_zf_refutation`, then with
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
Its lower calibration uses ordinary first-order completeness and a
well-founded part of a bisimulation quotient; the ZF-to-ZFC comparison
uses the constructible model interpretation. It is not a supplied
primitive-recursive proof-code translator or an encoded PA/ZFC derivation.
The README explicitly distinguishes this external proof-assistant result
from an internal PA proof or proof encoded in ZFC's own syntax.

For the requested Diophantine conclusion, the relevant claim is that the
ordinary mathematical simulation/calibration argument can be performed in
ZFC, not that a Lean theorem automatically supplies a ZFC proof object.
The current report must continue making that distinction.

## 2. H10 formalization and its actual nine-unknown interface

`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean`
proves `Jones1982.nine_unknowns` for every recursively enumerable set of
positive inputs, with nine natural witnesses and an ordinary integer
polynomial. It does not assert the printed historical degree bound.
The public theorem is existential, but the underlying construction is
explicit and can be applied directly to a known normalized quartic.

The critical theorem is `Jones1982.Nine.wset_iff_nine`. Its hypotheses are:

1. `nu >= 1`;
2. an ordinary polynomial P in input x and nu natural witnesses;
3. total degree at most four;
4. `Normalized P`: P(x,0,...,0) is nonzero for every natural input x;
5. an admissible `Index nu P z u y`;
6. positive input x.

Its conclusion is an equivalence between the zero-existence predicate of
P at x and the explicit `nineValue` function at x and nine natural
witnesses. For this task set nu=32 and x=1 and take the shifted quartic32
sum of squares, independent of the dummy input x.

Relevant implementation files, under the above `Diophantine/` directory:

- `Paper1982/Coding.lean`: exponent coding, digit polynomial, and the
  coefficient multiplier `(4-|alpha|)! product(alpha_j!)`.
- `Paper1982/Master1.lean`: definitions of `Index`, `Normalized`, `Wset`.
- `Paper1982/Index.lean`: explicit bounded construction of an index.
- `Paper1982/NineReduce.lean`: packed two-witness/central-binomial criterion.
- `Paper1982/NineRatio.lean`: conversion to two square tests, one
  divisibility condition and one positive margin.
- `Paper1982/NinePoly.lean`: ordinary-polynomial interpretation and literal
  weights `a_r^2+2`.
- `Paper1982/NineMain.lean`: exact composition and public nine-unknown result.
- `Common/RefinedRelationCombiningPolynomial.lean`: explicit signed-product
  polynomial and its evaluation under substitutions.
- `Common/RefinedRelationCombining.lean`: arithmetic equivalence, including
  signed radicands, zero roots and dependent square classes.

The named directional source theorems are `Nine.reduced_of_mem`,
`Nine.mem_of_reduced`, `Nine.ratio_complete`, `Nine.ratio_sound`, and
`Nine.conds_iff_value`. The construction in this task keeps their arithmetic
conditions literally and replaces only the final radical weights.

## 3. All hypotheses of the concrete specialization

The selected existing `quartic32.json` has 32 strictly positive variables
and 23 quadratic residuals. Its SHA-256 after exact source materialization
is `149eacd479896a113d869c5b74163efa4dab2cabaca8b581a6405cc9f580ca60`.
Set P32(x,n)=sum_j r_j(n+1)^2. It has 32 natural witnesses, is independent
of x, and has degree exactly four (the tau^4 coefficient is one).

Normalization is coefficient independent: the fifth raw residual is
`E*X+E-a*X`, which equals 1 when all 32 positive coordinates equal 1.
Thus P32(x,0,...,0)>=1 for every x and every fixed port tuple.

Let rho_j be the polynomial obtained from raw residual j by replacing
each integer coefficient by its absolute value and multiplying each term
by 2^(its witness degree), leaving the four nonnegative fixed compiler
ports unevaluated. Then rho_j bounds the coefficient l1 norm after the
positive shift. Consequently

```
sum_alpha |c_alpha| <= 24 sum_j rho_j^2,
s = 2+24 sum_j rho_j^2,
z_star=2^s,
u_star=sum_{j=1}^32 (2z_star)^(5^j),
y_star=sum_{|alpha|<=4} (z_star+c_alpha)(2z_star)^(L-expo(alpha))
```

gives an admissible Index without a search. Here c_alpha is the weighted
coefficient of P32, including the slack factorial; unlisted coefficients
are zero. The first input-coordinate exponent is always zero in nonzero
coefficient records, but the baseline digit sum still includes all input
exponents. The selected coefficient recipe is one full compiler tuple;
ports are fixed integers and are never existential variables.

The independent constructor finds 508 symbolic terms in the shifted
quartic, 346 nonzero witness-coefficient records, and 20 terms in the
polynomial bound s. These match the root agent's separate implementation.

## 4. What is newly concrete

`nine/nine_section.tex` contains the complete formulas. Its nine
unknowns are exactly

```
epsilon,g0,h0,s0,w0,phi,i0,j0,n ∈ N.
```

The six coordinates g,h,s,w,i,j are supplied by adding one; epsilon, phi
and n need no shift. No symbol defined after this is an additional unknown.

The final polynomial is

```
(Theta^2-Omega^2*(a0+V0^2*a1))^2 - 4*Omega^4*V0^2*a0*a1.
```

It is the product of four signed radical factors, fully expanded as an
ordinary polynomial. With d=(JF)^2, c=(QF+J(H-C))^2 and the original Jones
margin m, take Omega=d(2m-1), Theta=dn+c-Omega(c+V0V1).

The optimized weights are

```
V0=P^2+K^2+2,
V1=(A^2+C^2+1)(A^2+E^2+1)(Gp^2+H^2+1)+1.
```

Their validity is unconditional, including assignments where the packed R
is negative or a radicand is not square. The basic identity is

```
(a^2+b^2+1)^2 - ((a^2+1)b^2+1)
  = a^4+b^4+a^2b^2+2a^2+b^2 >= 0.
```

It gives sqrt(abs((a^2-1)b^2+1)) <= a^2+b^2+1. Applying it to each Pell
factor proves the required weight bounds before any semantic conclusion.

The q=2 relation combiner has a short self-contained proof, included in
the TeX. At a zero, a signed sum r0+V0*r1 is rational. If nonzero, squaring
isolates either radical as rational; if zero, the strict root separation
forces both radicands to be zero. The roots are therefore integers even
when square classes repeat. The offset is >=c+1, forcing d|c and m>0.
The converse supplies n explicitly. This replaces the need to cite the
full general Galois-theoretic relation combiner in the new finalizer proof.

## 5. Degree, operations and verification

For L=5^33, exact total degree is

```
161844 L+484 = 18841121345758438110351562984.
```

All-nine-coordinates-equal-t specialization has leading coefficient 2^328,
independent of every fixed coefficient. The symbolic leading-term audit
treats all 348 fixed leaves as independent indeterminates, so the final
nonzero scalar leader proves uniform exactness under the authentic tuple.
No unresolved highest-degree cancellation occurs in the binary DAG.

The majorant DAG has 20,895 nodes: 20,531 live binary operations
(664 additions,22 subtractions,19,845 multiplications),348 fixed leaves,
9 unknowns and7 literal leaves. Fixed powers are fully expanded by binary
multiplication. The giant fixed integers themselves are specified by the
bounded recipes, not materialized or charged as unknowns.

Literal NinePoly weights give degree291404L+860 and20,524 operations.
The new all-integer majorants reduce that degree by44.46% for7 additions.
This is an improvement within this explicit specialization. It is not a
claim to improve the classical existence of a nine-unknown representation
or a global minimum-variable/degree theorem.

Executed checks, recorded in `nine/generated/nine_checks.json`:

- exact sparse four-factor norm identity;
- exact nonnegative majorant identity;
- exact complete-homogeneous baseline identities for nu=0,1,2,3;
- four tiny coefficient-coding checks, testing the slack-factorial rule;
-64 modular DAG-versus-separate-direct-formula checks;
-432 constructed finalizer witnesses;
- full live binary circuit and symbolic exact-degree audit for both weights.

These checks certify finite algebraic claims and source construction. They
do not decide whether a ZFC refutation exists, enumerate an unbounded
halting run, or constitute a newly kernel-checked end-to-end theorem.

## 6. Integration pointers

New source files:

- `nine/nine_compressor.py`: reproducible standard-library constructor;
- `nine/check_nine.py`: finite algebraic and exact degree checks;
- `nine/nine_section.tex`: report fragment;
- `nine/generated/constants.json`: coefficient and bounded index recipe;
- `nine/generated/index_bound_s.json`: explicit20-term index bound;
- `nine/generated/shifted_quartic.json`:508 symbolic terms;
- `nine/generated/nine_majorant_dag.json`: primary20,531-operation DAG;
- `nine/generated/nine_literal_dag.json`: baseline for comparison;
- `nine/generated/nine_checks.json`: receipts and exact degree ledger.

The API `evaluate_dag(body,fixed,variables,modulus)` returns the output and
named node residues. `fixed` maps `z_index`, `y_index`, and all names in
`constants.json` to residues. The body is independent of the particular
valid index choice and can use the root's authentic T4 coefficient evaluator.
