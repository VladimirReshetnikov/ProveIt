# Mixed arithmetic at the auxiliary producer cut

The pair

\[
 V=cTf-c-Rf^2,\qquad W=\Delta f^2
\]

requires **at least seven binary arithmetic gates**, even when additions and multiplications may be mixed arbitrarily. The paid ports are the independent variables \(\Delta,c,i,f,T,R\) and the dependent monomials \(c^2,\Delta c^2\). In particular, \(f^2\) is not supplied. Keeping the actual two-row coefficient construction

\[
 U=i(\Delta c^2),\quad Q=U^2
\]

and the actual last subtraction \(S=W-Q\), the full joint V,Q,S producer cut therefore needs **at least ten gates**. Its present **7M+3A** schedule attains that bound. This extends the previous separated-monomial result to arbitrary mixed arithmetic inside the V/W computation.

A second, unrestricted statement is that V and S jointly need **at least three additions/subtractions**, even if every monomial is supplied free and the number of multiplications is unlimited. Neither result proves a lower bound for unrestricted interleaving of the Q producers with the other outputs. The ten-gate theorem protects three literal rows, and it does not exclude altered output interfaces, extra paid ports, coordinate charts or a change to the auxiliary norm/finalizer.

The [fresh helper](complete84_auxiliary_mixed_cut.py) and [receipt](complete84_auxiliary_mixed_cut.json) authenticate the parent and earlier scout as inert files. They save both complete84 arrays and an attaining mixed schedule. No predecessor Python is executed or imported.

## Model and actual interface

Work over the polynomial ring over the rationals in the six independent variables. Constants and scalar multiples are free for the lower bounds; a binary scalar-weighted sum still costs one addition. A product of two nonconstant expressions costs one multiplication. This relaxation can only lower the cost relative to the actual paid `+`, `-`, `*` model. Free arbitrary linear combinations are allowed only inside the proofs of multiplication-only bounds, never in the addition or total-gate claims.

Actual ports are

    Delta=A, c=R10a, T=auxiliary_quotient, R=r_lhs,
    c²=c2, Delta*c²=Ac2,
    V=aux_u_rhs, Q=R16, W=scaled_f_square, S=norm_strong.

The helper checks the ten literal definitions and the two dependent paid ports. Their only external consumers are through V,Q,S. The three protected rows for the ten-gate theorem are exactly `aux_coefficient_root=i*Ac2`, `R16=aux_coefficient_root²`, and `norm_strong=scaled_f_square-R16`. All remaining seven gates can be replaced by an arbitrary mixed circuit that produces V and W. That replacement may even use i,U,Q whenever available; the proof specializes i to zero.

The local arithmetic theorem uses only the two stated paid dependencies. It does not silently add relations from valid compiler coefficients or from positive zeros.

## V needs three nonconstant products

Specialize Delta and i to zero. The available polynomial space before any multiplication is spanned by

\[
 1,c,f,T,R,c^2.
\]

Give additions and scalar operations free. With at most two useful multiplications, write their outputs as g1,g2. Each multiplication operand is a linear combination of the paid ports and earlier multiplication outputs. The output V is also such a linear combination. Its cubic homogeneous part is

\[
 G=f(cT-Rf),
\]

which is not divisible by c².

If g1 has degree at least three, any useful g2 using g1 as a nonconstant operand has larger degree than g1: the other available operands have degree at most two, so they cannot cancel g1's leading term inside that operand. Such a new top degree cannot be cancelled in the output. Multiplication by a scalar is redundant. Thus both useful products must be independent products of the original paid span. Their degrees are at most four. Any quartic terms are scalar multiples of c⁴, and every cubic term in either product is divisible by c². If quartic terms cancel, the remaining cubic part is still divisible by c². If no quartic terms occur, the same divisibility holds. Neither possibility gives G.

The remaining case has g1 of degree at most two. Products of degree at most one are redundant, so its quadratic part is a product of two linear forms, say l1*l2. For g2 to have degree three without an uncancellable quartic term, its cubic part must be

\[
 L(\alpha c^2+\beta l_1l_2).
\]

The quadratic cT−Rf is irreducible, so G has only the linear factor f, up to scalar. Hence L is proportional to f and

\[
 cT-Rf-\lambda c^2
\]

would be a product of two linear forms. Its Hessian, in variable order c,T,R,f, is

\[
 \begin{pmatrix}
 -2\lambda&1&0&0\\
 1&0&0&0\\
 0&0&0&-1\\
 0&0&-1&0
 \end{pmatrix}.
\]

Its determinant is identically one. A product of two linear forms has Hessian rank at most two, a contradiction. The helper checks this determinant as a polynomial in lambda, not by a finite set of scalar substitutions. Therefore V needs at least **three multiplications**, with no restriction on the number of additions.

## V and W jointly need four products

In any circuit, all addition-stage expressions lie in the scalar linear span of the paid ports and the multiplication outputs g1,...,gm. W=Delta*f² is not in the span of the paid ports. Its representation therefore uses at least one gj with nonzero scalar coefficient.

Set Delta=i=0. W becomes zero. Choose the largest j with a nonzero coefficient in that representation; the resulting identity expresses the specialized gj as a linear combination of the specialized paid ports and earlier multiplication outputs. Delete its multiplication and substitute this expression at every subsequent use. All additions are free in this argument. The remaining circuit still computes V, which is independent of Delta and i, using at most m−1 multiplications. The preceding three-product lower bound gives **m at least four**.

This is a symbolic specialization and linear-elimination argument. It does not assume that a particular gate becomes zero, or that its original output was a monomial.

## With two additions, at least five products are needed

V is primitive and linear in T: its coefficient c*f and constant term −c−R*f² are coprime. Thus V is irreducible. Its three monomial exponent vectors are not collinear. A circuit with only one addition would produce a monomial times a power of one binomial, so it cannot produce V. At least two additions are necessary.

Suppose exactly two additions are available. Before the first addition, all wires are monomials. Let its nonmonomial output be g. Between the additions, every wire is a monomial times a nonnegative power of g. Since V is irreducible and has no monomial factor, it must, up to scalar, be the second addition's output itself; no later nonconstant multiplication can recover V from a larger product. Hence

\[
 V=m g^r+n g^s
\]

for monomials m,n and nonnegative integers r,s. Both exponents cannot be positive, since that would make g divide V. They cannot both be zero, since V has three terms. Thus one is zero, giving V=m*g^k+n with k positive.

If k is at least two, the binomial power contributes k+1 distinct collinear monomials. The extra monomial either adds another term, changes an existing coefficient or cancels at most one term. For k=2 or3, a three-term result would be collinear; for larger k too many terms remain. Both contradict V. Therefore **k=1**, and the first binomial groups exactly two of V's three terms. The outside monomial divides their greatest common monomial divisor, which is c, f or1. Up to scalar and regrouping there are only these cases:

| Form of V | Required monomial targets, also including W | Mixed products | Minimum total products |
|---|---|---:|---:|
| Sum of three separately produced monomials | cTf, Rf², Delta*f² | 0 | 5 |
| c(Tf−1)−Rf² | Tf, Rf², Delta*f² | 1 | 5 |
| f(cT−Rf)−c | cT, Rf, Delta*f² | 1 | 5 |

W is a monomial. It cannot depend multiplicatively on either nonmonomial addition; products cannot remove a nonmonomial irreducible factor. Thus its producing cone is monomial, and all three counts are divisor-cone bounds.

In the first row, each target needs at least two products from the actual paid monomials. The only possible newly shared divisor is f² between Rf² and Delta*f², saving at most one product: 2+2+2−1=5. In the second row the corresponding count is 1+2+2−1 plus the mixed product by c. In the third it is 1+1+2 plus the mixed product by f; no new divisor can be shared. The helper checks all paid pair-products, target gcds and these three exact classifications. The paid c² and Delta*c² do not divide any of the relevant missing monomials in a way that changes the counts.

Consequently a joint V/W circuit needs at least four multiplications and two additions; in the only possible six-gate case, four multiplications and two additions, the sharper five-product bound is a contradiction. The joint lower bound is **seven gates**. The factored schedule in the last row attains **5M+2A**.

## Ten gates with the actual coefficient boundary retained

Keep U=i*Ac2, Q=U² and S=W−Q as the three protected gates. Delete them and specialize i=0 in any candidate replacement circuit. U and Q become zero; replacing their occurrences by that constant is free. The remaining circuit must still explicitly produce V and W. It therefore has at least seven gates, proving a total of **at least ten**. This permits arbitrary multiplication of sums, shared intermediates and chronological interleaving among all nonprotected gates.

An attaining mixed schedule is

    f2=f*f;
    cT=c*T; Rf=R*f; inner=cT-Rf;
    V=f*inner-c;
    U=i*Ac2; Q=U*U;
    W=Delta*f2; S=W-Q.

The full saved array replaces only the parent's five quotient rows following f2. Exact sparse expansion proves the new V is the old V; all other output cuts are unchanged. Exact expression interning verifies every unchanged downstream value and the final polynomial after that proved substitution. Every one of the **84=47M+37A** rows and all25 supplied ports remains live. The18 positive witnesses, ordinary input and degree187 are inherited by this all-ring polynomial identity. Twelve complete signed evaluations are supplemental checks, not proofs of the identity or positive compiler zero fixtures.

## An unrestricted three-addition obstruction

This separate claim does not protect any Q or S row and even supplies every monomial for free. Put

\[
 P=f^2-\Delta i^2c^4,\qquad S=\Delta P.
\]

P is primitive and linear in Delta, hence irreducible. It is not associated to V. Suppose V and S were both produced with at most two additions. As above, V must first occur at the second addition. Since V does not divide S, S cannot depend on that addition and must be a monomial times a power of the first binomial g. P occurs in S with multiplicity one; consequently g is a monomial times P, up to scalar.

The second addition expressing V must have one summand divisible by g and one monomial summand. Reduce this identity modulo P and localize c and i. Substituting

\[
 \Delta=\frac{f^2}{i^2c^4}
\]

would make V a Laurent monomial. But V remains cTf−c−Rf², with three distinct terms distinguished by T and R. This contradiction proves **at least three additions** for unrestricted joint V,Q,S production. The helper checks the exact Laurent substitution and noncollinear support. The irreducibility and gate-normal-form arguments are mathematical proofs in this note, not inferred from those finite checks.

Thus any total-nine improvement at this paid interface must use at most six multiplications and change at least one protected coefficient/final-subtraction row. Merely allowing mixed arithmetic for V and Delta*f² is insufficient. The result is not a theorem about general coordinate charts, extra source dependencies, or the whole universal84 polynomial.

## Pins and replay

| Inert dependency | SHA-256 |
|---|---|
| `complete84_scaled_strong_output.py` | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| `complete84_auxiliary_monomial_scaling.py` | `643ca33730e8b1e43088240c8f81dd72fbb6dc87506206c55ab5fda411bf2390` |
| `complete84_auxiliary_monomial_scaling.json` | `851d6339e1e8ab940f977b9177eef804fa6f45601c06f974412d0567267c4ae1` |
| `complete84_auxiliary_monomial_scaling.md` | `db05c735b61b3165897430ed78f9a2d3967beb8f3c89044e7d5a29d4a9d79ffe` |

The receipt saves the complete parent and mixed arrays, literal consumer maps, exact polynomial certificates and supplementary evaluations. JSON duplicate keys/nonfinite values are rejected; receipt comparison is recursively type-exact, and checks remain active under optimized Python.

```sh
mixed_wip=/absolute/path/to/native-stream-queue
python3 "$mixed_wip/complete84_auxiliary_mixed_cut.py" \
  --root "$mixed_wip" --expect "$mixed_wip/complete84_auxiliary_mixed_cut.json"
python3 -O "$mixed_wip/complete84_auxiliary_mixed_cut.py" \
  --root "$mixed_wip" --expect "$mixed_wip/complete84_auxiliary_mixed_cut.json"
```

Fresh normal and optimized exact replays from `/` pass. No repository or frozen predecessor file is changed.
