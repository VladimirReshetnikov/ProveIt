# Independent review of the isolated five-gate auxiliary norm theorem

**PASS; no correction requested.** I read the complete [proof](auxiliary_norm_five_gate_lower_bound.md), [symbolic checker](auxiliary_norm_five_gate_lower_bound.py), and [receipt](auxiliary_norm_five_gate_lower_bound.json). The sharp bound is valid for exact division-free polynomial computation over Q from three independent inputs K,V,y and fixed constants:

```
P = K*V² − (K−1)*y²
requires at least 3 multiplications and at least 2 additions/subtractions.
```

The two bounds apply separately even when arbitrarily many operations of the other kind are permitted. They therefore imply five total gates, attained by the displayed3M+2A source. This is an isolated component theorem, not a lower bound on a complete universal circuit or on other ways to represent its zero set.

## Challenge of the multiplication bound

With at most two multiplication gates, all values preceding the first are affine. The first product Q=A*B must have a nonzero quadratic part: otherwise the whole circuit has degree at most two. Between and after the two products, additions and rational scalar combinations cannot create any other nonlinear source.

If both second-product operands contain a nonzero multiple of Q, the resulting fourth-degree term is a nonzero scalar times Q2². There is no other fourth-degree quantity available to cancel it. The second product must contribute to the output, because degree three cannot be obtained from Q and affine values alone. Thus exactly one of its operands contains Q. With free affine operations allowed as a relaxation, every possible cubic output has the form

```
P=(aQ+u)v+bQ+z
 =(Q+u/a)(av+b)+(z−bu/a),  a!=0,
```

where u,v,z are affine. The divisions here are only by a nonzero rational coefficient in the proof, not division gates in the circuit. The affine factor D=av+b must have degree one. Consequently P is affine on D=0, and its highest homogeneous part is A1*B1*D1.

The actual cubic part is K(V−y)(V+y). Unique factorization over Q restricts D1 to one of those three linear directions. The resulting parallel-plane restrictions are exactly:

- K=c: `cV²+(1−c)y²`; both quadratic coefficients cannot vanish, since they sum to1.
- V=y+c: `2cKy+c²K+y²`; the y² coefficient is1.
- V=−y+c: `−2cKy+c²K+y²`; again the y² coefficient is1.

No offset c removes the quadratic part. Hence no permitted two-multiplication circuit can compute P. This also addresses zero or one multiplication, whose possible degree is at most two. The proof does not rely on a finite enumeration of circuits or offsets.

## Challenge of the addition bound

Before the only allowed addition/subtraction, every nonzero quantity is a scalar monomial. Afterwards, induction over arbitrary multiplication, squaring and reuse makes the output a scalar times a monomial times a nonnegative integer power of the one binomial produced by that gate. Zero quantities do not help compute nonzero P.

The polynomial is primitive and linear in K over Q[V,y]: its two coefficient polynomials are V²−y² and y². Any common irreducible factor would have to be y, but V²−y² is not divisible by y. Hence the gcd is1. Gauss's lemma and degree-one irreducibility over Q(V,y) prove irreducibility in Q[K,V,y]. This gcd argument does not assert that the two coefficient polynomials generate the unit ideal in the multivariate coefficient ring; that stronger assertion is unnecessary.

Irreducibility forces any monomial prefactor to be a unit and the binomial exponent to be1; exponent0 or a constant binomial produces only a monomial. But P has exactly three distinct nonzero monomials. Thus one addition/subtraction is impossible, regardless of the multiplication budget.

## Independent executable evidence and scope

The independent [checker](review_auxiliary_norm_five_gate_lower_bound.py) authenticates all three author artifacts before reading them. It uses its own standard-library sparse coefficient algebra, imports no subject module and does not invoke the author's checker or SymPy. The [receipt](review_auxiliary_norm_five_gate_lower_bound.json) verifies:

- The exact trinomial and its complete cubic factorization.
- The two-multiplication normal form after clearing its constant denominator, and the nonzero fourth-degree coefficient when both operands use Q.
- All three full affine-plane restriction identities and symbolic obstructions for every offset c.
- The primitive-coefficient argument and three-term/no-monomial-factor facts needed by the one-addition proof.
- Every row of the actual five-gate attaining source, its exact expanded output, its3M+2A ledger, and full output liveness.

The mathematical normal-form classification and UFD/Gauss steps are proof review, not claims that finite testing establishes a circuit lower bound. The executable identities supplement that argument.

The independence of K,V,y is essential. In a complete Diophantine source, K and V are computed from other paid ports, which may allow sharing outside this isolated interface. This theorem neither excludes such reuse nor handles new coordinates, extra supplied ports, division, specializations, or a different polynomial with the same positive zero set. The author's note and receipt consistently preserve those limits.

Fresh replay passed against the full frozen saved receipt:

```sh
python3 review_auxiliary_norm_five_gate_lower_bound.py \
  --source-root /path/to/artifacts \
  --expect /path/to/review_auxiliary_norm_five_gate_lower_bound.json
```

No repository or author artifact was modified, and no broader arithmetic search was performed.
