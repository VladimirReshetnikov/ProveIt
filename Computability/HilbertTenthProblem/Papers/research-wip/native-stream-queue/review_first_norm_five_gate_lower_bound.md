# Independent challenge of the five-gate first-norm bound

**PASS.** The frozen [proof](first_norm_five_gate_lower_bound.md),
[checker](first_norm_five_gate_lower_bound.py) and
[receipt](first_norm_five_gate_lower_bound.json) establish the stated
sharp component bound. At exactly the paid ports
T,X,Y,k,E=XY,Z=kY, division-free exact polynomial evaluation over the
rationals needs at least3 multiplications and at least2 additions or
subtractions. The actual complete86 component attains3M+2A in both
strong variants. No correction was requested.

The result is local to these six ports and this target polynomial.
It proves neither that the complete universal86 source is optimal nor
that an equivalent positive-zero representation needs five gates.
Additional already paid registers, coordinate changes, variable division
and changes to the represented polynomial are excluded. In particular
this is not a bound for the distinct half-binomial expression
tau*(tau+1) used by the geometry component.

## Independent multiplication argument

Set Y=1. The available nonlinear ports become duplicates E=X and Z=k,
so the remaining free values are affine in T,X,k. The target becomes

    T²−X²k²−Xk².

Giving all affine operations away for free only strengthens a prospective
two-multiplication circuit. Its first actual product Q must be quadratic.
Both operands of the second product must have nonzero Q coefficients,
and its output must contribute with a nonzero coefficient, since the
target has degree four. All later affine work can therefore be collected
as

    h*(alpha*Q+u)*(beta*Q+v)+b*Q+z,

where u,v,z are affine and h,alpha,beta are nonzero constants.
The quartic term forces the highest part of Q to be proportional to Xk.
Because Q is the product of two affine forms, unique factorization makes
their linear parts proportional to X and k in some order. Consequently
the **actual first product** has no T dependence and is

    Q=c*X*k+r*X+s*k+t, c nonzero.

One must use this actual product, not an arbitrarily renamed register
Q+T after later affine work. Such later T contributions are already
allowed in u and v. This distinction is handled correctly in the author
proof.

At X=0 the complete output's quadratic part comes only from the product
of the two second-stage linear parts. It must be T². Normalize their
nonzero T coefficients: these parts become T+a*k and T+b*k. Comparing
coefficients gives a+b=0 and ab=0; hence a²=0 and a=b=0 over the
rational field. Neither second-stage operand has a pure-k term.
Their remaining k dependence is a multiple of Xk. Their product cannot
have Xk², and the later affine combination of Q cannot supply that
cubic term. The target has coefficient−1 on Xk², a contradiction.

This also covers circuits with fewer products, which cannot attain
quartic degree at these restricted ports. The specializations are
legitimate for exact polynomial equality. They would not be legitimate
merely from equality on accepting Pell witnesses, and the theorem does
not make that broader claim.

## Independent addition argument

Every provided port is a monomial in T,X,Y,k. Before a first addition,
multiplication-only computation produces scalar monomials. If there is
at most one addition or subtraction, every final nonzero value has the
form scalar times a monomial times a nonnegative integer power of one
binomial. Reuse and squaring do not enlarge that form.

The target is a monic quadratic in T with radicand

    (kY)²*X*(XY²+1).

Its valuation at the prime X in the rational function field Q(X,Y,k)
is exactly one, because XY²+1 reduces to1 at X=0. Therefore the
radicand is not a rational square. The quadratic is irreducible over
that field, and the primitive monic polynomial is irreducible over
Q[X,Y,k,T] by Gauss's lemma.

The target has three terms and no common nonconstant monomial factor.
Irreducibility rules out a nonunit monomial prefactor or a binomial power
of exponent at least two. Exponent one would give at most two terms,
and exponent zero only a monomial. Thus at least two additions or
subtractions are required, independently of the multiplication count.
The two separate lower bounds sum to five operations and match the
literal attaining source.

## Independent source and algebra checks

The [review helper](review_first_norm_five_gate_lower_bound.py) authenticates
all three author files and the actual complete86 parent trio. It imports
no author or parent Python module. It independently reads both complete
source receipts, checks the E=XY and Z=kY producers, evaluates all five
literal component gates and verifies their3M+2A ledger and liveness.

The helper uses SymPy rather than the author's sparse-polynomial library.
It independently expands the unrestricted two-product normal form,
extracts the k²,Tk,T² and Xk² coefficients, verifies the normalized
quadratic obstruction and forces the cubic coefficient to zero. It
checks the odd X-valuation, the three-term support and, as a separate
algebra check, the rational polynomial's exact irreducible factorization.
The [receipt](review_first_norm_five_gate_lower_bound.json) records those
results and all source pins.

These calculations check the algebra used by the argument. The proof
about every straight-line program is the normal-form classification
and factorization reasoning above; no finite circuit search or sampled
assignment is substituted for it. No accepting universal Pell tuple is
constructed or needed.

Pinned author hashes, in Python/JSON/Markdown order, are
2eecbcfa6d48872f8522cdb839517232a2208cfc9f9466f5780c3d0584ddb077,
e66759e01ae27cb41abe419a3875180c68467363c3c249943bbc8c589552fee4,
and3f7580635b63b6cc7bda27b23022db99c85fdc4341c34ea1fb5d55f42e00c2fc.
A portable fresh replay, using an environment with SymPy, is

```sh
/tmp/diophantine-research-venv/bin/python review_first_norm_five_gate_lower_bound.py \
  --root /path/to/native-stream-queue \
  --author /path/to/first_norm_five_gate_lower_bound.py \
  --expect review_first_norm_five_gate_lower_bound.json
```

The author files and repository were left unchanged by this review.
