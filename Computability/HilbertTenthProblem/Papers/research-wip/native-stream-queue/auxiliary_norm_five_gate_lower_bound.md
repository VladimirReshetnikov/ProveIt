# The isolated auxiliary norm needs exactly five arithmetic gates

For three independent supplied ports K,V,y, the polynomial

    P(K,V,y)=K*V²−(K−1)*y²

requires **at least three multiplications and at least two additions or
subtractions** in every division-free arithmetic straight-line program over
the rationals. Fixed constants and reuse are free; each binary multiplication,
addition or subtraction costs one. The familiar evaluation

    V2=V*V
    y2=y*y
    difference=V2−y2
    weighted=K*difference
    P=weighted+y2

attains both lower bounds: **5=3M+2A**. The bounds permit arbitrarily many
operations of the other kind: this is stronger than an enumeration of a few
five-gate templates.

This is an **isolated component theorem**. The complete86 universal circuit
uses this factor with computed K=Delta²*i²*c⁴ and V=of−c, alongside other
paid arithmetic ports. The theorem does not lower-bound that complete DAG,
the combined coefficient/auxiliary block, circuits that can use those other
ports, changed supplied coordinates, or polynomials merely having the same
positive zero set. It explains why further savings should involve such
additional structure rather than a cheaper exact evaluation of this
three-input polynomial alone. It does not claim literature priority.

## At least three multiplications

Assume a circuit uses at most two multiplications, allowing arbitrarily many
additions and subtractions and arbitrary rational constants. All quantities
before its first multiplication are affine polynomials. Write its result as
Q=A*B, with A,B affine. Since P has degree three, Q must have degree two;
otherwise a second multiplication still produces degree at most two.

Between multiplication gates every available value has the form aQ+u,
where a is a constant and u is affine. If both operands of the second
multiplication have nonzero Q coefficients, their product has a nonzero
degree-four term proportional to Q2², where Q2 is the degree-two part of Q.
No subsequent additions of Q or affine quantities can cancel this term.
The second product must actually contribute to P, since the first product
and additions alone cannot produce degree three. Consequently exactly one
operand of the second multiplication has a Q term; the other is affine.
Absorbing the final nonzero scalar into the operands, P has the form

    P=(aQ+u)*v+bQ+z,       a!=0,

with u,v,z affine and a,b constants. Rearrangement gives

    P=(Q+u/a)*(a*v+b)+(z−b*u/a).

Thus there must be an affine polynomial D of degree one such that P
restricted to the hyperplane D=0 is affine. The highest homogeneous parts
also satisfy

    P3=A1*B1*D1=K*(V−y)*(V+y).

The three displayed factors are pairwise nonproportional linear factors.
Unique factorization over Q shows that D1 is proportional to K, V−y, or
V+y. After harmless nonzero scalar normalization, the hyperplane D=0 must
therefore be one of the following, for some constant c:

| Hyperplane | Restriction of P | Unavoidable quadratic part |
|---|---|---|
| K=c | cV²+(1−c)y² | c and1−c cannot both vanish |
| V=y+c | 2cKy+c²K+y² | coefficient of y² is1 |
| V=−y+c | −2cKy+c²K+y² | coefficient of y² is1 |

None of these restrictions is affine, for any c. This contradiction proves
that two multiplications cannot suffice. The argument also covers circuits
with zero or one multiplication, whose output has degree at most two.

The proof allows constants and all affine combinations without charging
them in this part. It is therefore a lower bound even under a relaxation of
the stated arithmetic model. Division is excluded: dividing by a polynomial
would invalidate the polynomial normal form.

## At least two additions or subtractions

With no additions or subtractions, every computed nonzero polynomial is a
constant times a monomial. With exactly one such gate, its two inputs are
monomials (including constants), and every later value is a constant times
a monomial times a nonnegative power of that single binomial. This follows
by induction over all subsequent multiplication gates, including squares
and reuse. The output has the form

    constant * monomial * (monomial1 ± monomial2)^e.

The target P is irreducible in Q[K,V,y]. Indeed, viewed as a polynomial in K
with coefficient ring Q[V,y], it is linear and primitive:

    P=(V²−y²)K+y²,    gcd(V²−y²,y²)=1.

Over the fraction field Q(V,y), its degree-one polynomial is irreducible;
Gauss's lemma then gives irreducibility over Q[K,V,y]. Since P has degree
three and is neither a monomial nor a binomial, the one-addition output
form is impossible. More explicitly, irreducibility would force the
monomial factor to be a unit and e=1, leaving at most two nonzero monomials;
P has the three distinct nonzero monomials KV²,−Ky²,y². Cases e=0 or a
constant binomial give only a monomial and also fail.

Hence at least two additions/subtractions are necessary. Allowing a free
choice of signs or rational constants does not weaken this conclusion.
Together with the multiplication bound, this proves a total of at least
five paid arithmetic operations, attained by the literal circuit above.

## Symbolic audit and scope

The [checker](auxiliary_norm_five_gate_lower_bound.py) and
[receipt](auxiliary_norm_five_gate_lower_bound.json) verify the actual cubic
part, both circuit-normal-form identities, all three affine-plane
restrictions, and their nonvanishing quadratic coefficient ideals. They
independently check the primitive coefficient gcd and irreducibility and
expand the entire attaining circuit. Coefficient ideals are checked
symbolically in the free affine offset c; no finite sampling of offsets or
arithmetic circuits substitutes for the quantified arguments above.

The receipt contains the actual five-gate circuit and both sharp ledgers.
The proof uses no facts about accepted programs, Pell ranks, native masks,
positivity of a computed V, or first-norm sign. In the complete universal
source, K and V are not independent supplied witnesses, so this component
optimality is deliberately not promoted to a global circuit lower bound.

Reproduce with Python and SymPy:

    /path/to/sympy-python auxiliary_norm_five_gate_lower_bound.py \
      --expect auxiliary_norm_five_gate_lower_bound.json

`--output` writes the deterministic receipt; saved comparisons preserve
exact JSON types. No historical module, network, archive, repository or
Git state is read or changed by this symbolic audit.
