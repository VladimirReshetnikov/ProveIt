# A smaller complete source specification for direct proof flow

This is ordinary mathematical research conducted while Lean formalization is
paused. It changes the **whole source predicate** in package68, rather than
advertising its local witness count as a finished consistency equation. The
delivered package is unchanged. No new Lean source was edited or built.

Two changes give a precise improvement:

1. Replace the common-multiple bounded universal block by the single relation
   `M=(m+1)^t`, represented by a fixed111-witness power polynomial.
2. Use the delivered97-witness quartic local source and encode the two beta
   digits together by five quadratic equations and seven additional witnesses.
   This avoids repeated graph composition and the signed splitting of a
   degree50 product.

For the specified existing constructors, the closed representation witness
count falls from **140,639,095,370 to47,439,839** (about2965-fold). These are
representation witnesses **before the final quartic compiler**. Neither the
final quartic variable count nor its expanded polynomial or circuit size has
been computed. This is therefore not a new record against the existing
nine-variable equations.

## Carrier theorem

Let `m,t>=1`, `M=(m+1)^t`, and let all `c_i,p_i,q_i` lie in `[0,m]`. Put

\[
 A(X)=\prod_{i<t}(1+c_iX),\qquad
 C(X)=(1+X)\prod_{i<t}(1+p_iX)(1+q_iX).
\]

Both polynomials have **nonnegative integer coefficients** and constant term1.
Then

\[
 A(M)=C(M)\quad\Longleftrightarrow\quad A(X)=C(X).
\]

For the forward implication, first bound the *actual* degree of `C`. If it were
at least `t+1`, its leading coefficient would be at least1, giving
`C(M)>=M^(t+1)`. But

\[
 A(M)\le(1+mM)^t<((m+1)M)^t=M^{t+1},
\]

a contradiction. Thus both products contain at most`t` nonconstant factors.
For either polynomial`P`, the sum of its coefficients is
`P(1)<= (m+1)^t=M`. Every individual coefficient is strictly below`M`: the
constant coefficient is1, and every nonconstant product has another positive
coefficient; the constant polynomial1 also satisfies the bound since`M>=2`.
Consequently every coefficient of the signed difference`A-C` has absolute
value strictly below`M`.

If that difference were nonzero, take its least nonzero coefficient`h_r`.
Dividing its zero evaluation by`M^r` shows`M` divides`h_r`, contradicting
`0<|h_r|<M`. This proves the identity. The reverse implication is immediate.

Unique factorization in`Q[X]`, applied to the distinct linear factors`1+jX`
for`j>0`, now gives

\[
 \#\{i:c_i=j\}-\#\{i:p_i=j\}-\#\{i:q_i=j\}=\mathbf1_{j=1}
 \quad(j>0).
\]

Label0 contributes the unit1 and is deliberately ignored. Individual integer
weights need not be coprime: the checked fixture has`m=4,t=3,M=125`, and
`gcd(1+M,1+3M)=2`. Its carrier also fails the old interval-divisibility
condition. The proof uses a bounded number of factors, rather than coprimality.

## From a complete accumulator path to a refutation

Use exactly package68's single-conclusion C222 rule relation. Axiom instances
have padded premises`0,0`; label0 is the free truth formula, and target1 is
the sealed contradiction. Require natural states with

\[
 S_0=1+M,\quad S_t=1,\quad
 S_{i+1}(1+c_iM)=S_i(1+p_iM)(1+q_iM).
\]

The degenerate cases need no extra witnesses. If`t=0`, the two endpoints
contradict`M>0`. If`m=0`, every label is0, so each update says`S_{i+1}=S_i`,
again contradicting the endpoints. Thus every accepted path has`m,t>=1`
before the carrier theorem is used. The carrier is positive even in the
degenerate cases because`(m+1)^t>=1`.

Telescoping gives`A(M)=C(M)`; alternatively use the invariant
`S_i*product_{k<i}(1+c_k M)=(1+M)*product_{k<i}(1+p_k M)(1+q_k M)`,
which requires no cancellation. The carrier theorem gives the exact
nonnegative Horn flow for target1, modulo truth0.

For completeness of the flow argument, let`D` be all formulas derivable from
the axioms and truth0. If1 were outside`D`, sum the flow coordinates outside
`D`. Every valid rule has a nonpositive sum there: a conclusion outside`D`
must have at least one premise outside`D`. Their sum cannot equal the target
vector, whose sum there is1. Hence the target is derivable.

Conversely, expand any finite proof tree from its open obligation1. Choose`t`
as the number of non-truth nodes expanded and`m>=1` bounding all its labels,
then choose`M=(m+1)^t`. Let`S_i` be the product of the affine weights of all
open obligations. Expanding a node gives the displayed update with natural
states, and the final state is1. A finite CRT code supplies the beta sequence.
This proves equivalence of **existence** with the original proof relation;
it does not equate the old and new admissible carriers pointwise.

The C222-to-sealed-ZFC numerical calibration is inherited from package68 and
its pinned sources. It is an ordinary mathematical dependency, not a new
formalization supplied here. There is no K215 simulation or Jones finalizer
in this source construction.

## Explicit improved source

Retain the five outer naturals`t,x,y,m,M0`, and put`M=M0+1`. Let
`beta(x,y,i)=x mod((i+1)y+1)`. The carrier equation is
`M0+1=(m+1)^t`. There is only **one bounded universal block**:

* For every`i<t`, use package68's literal92 quadratic residuals in
  `direct/AffineProductEquation.lean`, with its97 natural witnesses and exposed
  values`S,Sp,m,M0`. Add seven witnesses
  `S,Sp,d,u,r,v,rp` and the five quadratic residuals

  ```text
  d - ((i+1)y+1)
  x - S - d*u
  S + r + 1 - d
  x - Sp - (d+y)*v
  Sp + rp + 1 - (d+y)
  ```

  Append their squares to the original sum of92 squares. The resulting local
  polynomial has104 natural witnesses and degree at most4. Since`d>=1` and
  `d+y>=1`, the equations say exactly`S=beta(i)` and`Sp=beta(i+1)`; no
  zero-modulus branch, parser premise, or extra graph-value coordinates occur.
* Use five endpoint witnesses`u0,r0,ut,rt,dt` and the sum of squares of

  ```text
  dt - ((t+1)y+1)
  x - (M0+2) - (y+1)*u0
  M0 + r0 + 2 - y
  x - 1 - dt*ut
  rt + 2 - dt
  ```

  These say exactly`beta(0)=M0+2` and`beta(t)=1`.
* Instantiate the existing literal`PowerRepresentation.rep.expression` by
  replacing its output, base and exponent variables with`M0+1,m+1,t`.
  Preserve its111 witness variables. This is ordinary polynomial
  substitution, with no existential choice or additional input-value
  variables. A conservative use of the supplied three-input`Rep.compose`
  constructor instead needs114 witnesses.
* Combine the endpoint, bounded-step and power representations by sum of
  squares, existentially close the five outer variables, and apply the
  existing explicit quartic compiler. This is a complete finite constructor
  recipe; its final large ordinary polynomial has not been materialized.

Choose the carrier first, then the accumulator path, then a CRT sequence
scale`y` and code`x`. For example, take`y` to be a sufficiently large multiple
of`1,...,t+1`; the moduli`1+(i+1)y` are then pairwise coprime and exceed the
states. Neither this sequence scale nor the bounded-universal compiler's
internal scales is identified with`M`. Removing the interval-divisibility
block for`M` does not remove the separate CRT existence argument for`y`.

## Reproducible whole-source comparison

The metadata uses the existing source definitions, without evaluating large
polynomials. For a residual with`m` witnesses and signed split size`s`, the
checked existing theorem`BoundedForallDepth.boundedForall_witnessCount` gives

```text
forallCount(m,s) = m*(4*s+11790) + 10*s+20674.
```

The count-only script parses the literal quadratic monomials in the delivered
source, validates their grammar, and propagates the exact constructor sizes.
It does not elaborate the proposed source in Lean.

| Stage | Delivered23-local constructor | Improved104-local source |
|---|---:|---:|
| Step block input witnesses |51|104|
| Step block input split size |657,188,974|108,434|
| Compiled bounded step block witnesses |140,639,062,400|47,439,718|
| Carrier block witnesses |32,940|111|
| Endpoint witnesses |25|5|
| Closed outer witnesses |5|5|
| **Closed representation witnesses** |**140,639,095,370**|**47,439,839**|

The apparent23-local advantage is lost in the literal syntax consumed by
this particular compiler: its step polynomial alone has signed split
size34,389,014, and nested beta graph constructors increase it further.
The97-local quartic alternative has step split size107,934. These are exact
sizes of the stored expression trees, not arithmetic-DAG operation counts.
They expose a practical obstruction to comparing local witness counts.
The carrier change by itself removes32,940 witnesses and adds111
(114 through conservative composition); most of the whole-source saving
comes from the explicit shared beta equations and quartic local source.

Run the independent controls with the standard library only:

```sh
python verify.py --output VERIFY.normal.json
python -O verify.py --output VERIFY.optimized.json
```

The receipts pin every source file by SHA256, test all output and premise
multisets for`1<=m<=8,1<=t<=4`, check signed-digit uniqueness, reject20 explicit
small-carrier false balances, and verify a complete noncoprime-carrier CRT
path and its new endpoint/step equations. Finite controls support the
implementation and arithmetic counts; the universal proofs are above.
