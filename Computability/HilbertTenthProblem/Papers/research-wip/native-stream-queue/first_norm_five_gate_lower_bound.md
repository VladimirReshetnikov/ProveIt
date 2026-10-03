# The first norm needs five gates at its actual dependent paid ports

The current complete86 first norm is already an optimal exact local
polynomial computation at the following six paid ports:

    T, X, Y, k, E=X*Y, Z=k*Y.

Only T,X,Y,k are algebraically independent. The two additional monomials
E and Z are available without further charge to this component. Its target is

    P=T²−(EZ)(EZ+k)=T²−X²Y⁴k²−XY²k².

Every division-free straight-line program over Q using these ports, fixed
rational constants, and binary addition, subtraction and multiplication
requires **at least3M and at least2A**. Each separate lower bound permits
arbitrarily many operations of the other kind. The existing five-gate source
attains them:

    T2=T*T
    L=E*Z
    next=L+k
    product=L*next
    P=T2−product.

The dependencies E=XY and Z=kY are included in this result. This is stronger
than treating E,Z,k as formally independent and hoping that the bound
survives their specialization. It remains a **component bound**: other
already paid registers of the full universal source, different coordinates,
or a different polynomial having the same positive zero set are not allowed
here. The complete universal86 bound is not proved optimal.

## At least three multiplications, with the actual dependencies

Suppose there were a program with at most two multiplications. Substitute
Y=1. The available ports reduce to T,X,k and duplicate copies E=X,Z=k.
The restricted target is

    R=T²−X²k²−Xk².                                  (1)

Allow every affine combination for free; this only relaxes the model for a
multiplication lower bound. Before the first product all values are affine.
Let its output be Q=A*B, with A,B affine in T,X,k. Q must have degree two,
and both inputs of the second product must contain nonzero multiples of Q,
since otherwise the entire output would have degree at most three.
The second product must contribute to the final output. Consequently the
complete output has the form

    h*(alpha*Q+u)*(beta*Q+v)+b*Q+z,                 (2)

where h,alpha,beta are nonzero rational constants, b is constant, and u,v,z
are affine. Arbitrarily many earlier or later additions are absorbed here.

The quartic part of (2) is h*alpha*beta*Q2². The quartic part of (1) is
−X²k². Unique factorization therefore makes Q2 proportional to Xk.
Since Q is a single product of affine forms, their linear parts must be
proportional to X and k in some order. In particular **Q contains no T**:

    Q=q*X*k+r*X+s*k+t,       q!=0.                  (3)

The coefficients in (3) satisfy additional affine-product relations, but
we do not need them. Allowing arbitrary q,r,s,t enlarges the possible family.

Now restrict X=0. Q becomes s*k+t, which is affine. The term bQ+z in (2)
is affine too, whereas the target becomes T². Thus the product of the
linear parts of the two second-product operands must be a nonzero multiple
of T² in Q[T,k]. Unique factorization forces **each linear part to be a
nonzero multiple of T**, with no k term.

Write the k coefficients of u and v as u_k and v_k. The conclusion is

    alpha*s+u_k=0,       beta*s+v_k=0.               (4)

It can also be derived without another UFD step: the vanished k² and Tk
coefficients give AB=0 and A*v_T+B*u_T=0, while h*u_T*v_T=1. Therefore
u_T,v_T are nonzero and A=B=0, where A=alpha*s+u_k and B=beta*s+v_k.

Returning to all X,T,k, each second-product operand now has the form

    constant*X*k + constant*X + constant*T + constant.

Their product has no cubic Xk² monomial. Neither bQ nor z can provide one.
Explicitly that coefficient in (2) is

    h*q*(alpha*(beta*s+v_k)+beta*(alpha*s+u_k))=0

by (4). Its coefficient in the actual target (1) is−1, a contradiction.
Hence at least three multiplication gates are necessary. Zero or one
multiplication cannot reach degree four and are covered as well.

This specialization does not assume anything about a Pell zero. Exact
polynomial computation on all positive integer T,X,Y,k would also force the
same identity, since that integer grid is Zariski dense. The proof then
uses algebraic specializations legitimately. A circuit required to agree
only on complete universal zeros is outside this theorem.

## At least two additions or subtractions

All six supplied ports are monomials in the independent variables T,X,Y,k.
With no addition/subtraction every nonzero value remains a scalar monomial.
After the only possible addition/subtraction, every later product is a
scalar times a monomial times a nonnegative integer power of that one
binomial. This induction allows arbitrary multiplication, squaring and reuse.

The target P is irreducible in Q[X,Y,k,T]. Regard it as a monic quadratic in T:

    P=T²−R0,        R0=(kY)²*X*(XY²+1).

In the rational function field Q(X,Y,k), R0 has X-valuation exactly one:
XY²+1 is not divisible by X, and kY has valuation zero. A rational square
has even valuation at every prime, so R0 is not a square. A quadratic
T²−R0 is therefore irreducible over that field. Monicity and Gauss's lemma
then give irreducibility over Q[X,Y,k,T].

P has three nonzero monomials and no nonconstant monomial factor. The
one-addition output form cannot equal it: irreducibility would force the
monomial prefactor to be a unit and the binomial exponent to be one, giving
at most two terms. Exponent zero or a constant binomial gives a monomial
and fails too. This proves the separate lower bound of two additions or
subtractions, regardless of the number of multiplications.

Together the bounds give five paid gates. The displayed source attains3M+2A.
Fixed negative signs and arbitrary rational constants do not change either
obstruction; divisions by variable polynomials are excluded.

## Literal-source and symbolic evidence

The [checker](first_norm_five_gate_lower_bound.py) authenticates the
[complete86 source, receipt and proof](complete86_factored_first_root.md)
before reading the actual two complete sources. Both normalized and ordinary
strong forms contain exactly the five displayed instructions and the actual
E=XY,Z=kY producer definitions. The checker expands the full component in
T,X,Y,k, verifies3M+2A and liveness, and records both attaining sources in
its [receipt](first_norm_five_gate_lower_bound.json).

A separate symbolic calculation in the same checker expands the fully
general two-product form (2), checks all three quadratic coefficients at
X=0 and its entire cubic Xk² coefficient, and verifies the contradiction
after the forced substitutions (4). It also checks the actual quartic
part, radicand and odd X-valuation. All calculations use a small
standard-library sparse polynomial implementation. No finite sample of
circuits or variable values replaces the general classifications above.

The result identifies a concrete boundary for further optimization: exact
rescheduling inside these six ports cannot reduce the current first norm.
Cross-factor registers and same-zero-set transformations remain available.
No historical module is executed, no accepting Pell tuple is materialized,
and no literature-priority claim is made.

Reproduce with ordinary Python3:

```sh
python3 first_norm_five_gate_lower_bound.py \
  --root /path/to/native-stream-queue \
  --expect first_norm_five_gate_lower_bound.json
```

`--output` writes the deterministic receipt. Saved comparisons preserve exact
JSON types. The proof and source remain separately reviewable.
