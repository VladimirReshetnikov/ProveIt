# Independent review of the independent-k degree certificate

The external algebraic certificate supports **exact total degree 99** for the
84-row candidate when the fixed integer beta is at least 3; the other fixed
ports may be arbitrary integers. The proposed compact symbolic beta satisfies
that condition. This is a polynomial-degree statement, not a zero-map or
consistency equivalence.

The two leading cancellations are valid formal ring identities. With
`Z=b*ell+D` and `D=b*(k+r−k*Bt)−Bt`, the `b²*ell²` terms in the first
residual cancel, leaving a degree bound 17. With
`Dstar=U*a*c+E`, `E=U*X+H*shift`, and `Delta=a²+H`, the leading
`U²*a²*c²` terms cancel in the main residual, giving bound 30. The other
two factor bounds are 30 and 22, so the product output has degree at most
`17+30+30+22=99`.

The independent checker does not reuse the author's top-20 jet algorithm.
It tracks only the leading coefficient in t at each noncancelling graph
node, over the polynomial ring in all four symbolic ports, and explicitly
uses the two factored identities at their cancellation points. It fails
rather than guessing if any other leading terms cancel. After substituting
every witness by t, it obtains these leading terms:

| Factor | Degree in t | Leading coefficient |
| --- | ---: | --- |
| First | 17 | `−2*beta^10*(beta−2)` |
| Main | 30 | `8*beta^21` |
| Auxiliary | 30 | `beta^14` |
| Strong | 22 | `beta^12` |

Their product is `−16*beta^57*(beta−2)` at t^99. It is independent of the
other three ports and is nonzero for integer beta≥3, including the symbolic
`2^(67*8807)−1`. Thus the ray gives the lower bound matching the global
upper bound. The author's symbolic-port jet proof is also sound in its stated
scope: at each product, a term discarded more than 20 degrees below its
input's syntactic bound cannot re-enter the retained top window by combining
with a term above the other input's bound.

The parent transcript becomes the child after `k=eta+zeta`; the inverse
`zeta=k−eta` is an invertible integral homogeneous linear substitution, so
the two unrestricted integer polynomials have the same degree. This does not
prove the natural-domain converse: the child's `k≥eta` condition, a possible
replacement witness, and the full consistency proof remain open.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-independent-k-degree99-independent/check.py
```

The check pins the original graph and certificate, reproduces its receipt,
checks the relevant source rows and the independent leading-form computation,
and verifies the parent transcript. It does not run Lean or validate graph
zeros, providers, axioms, PDF linkage, or global minimality.
