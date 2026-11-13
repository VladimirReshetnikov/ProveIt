# Exact degree 99 of the independent-k graph at compact beta

The pinned 84-row independent-k candidate has **exact total degree 99** in
its 13 witness variables whenever its fixed integer first port beta is at
least 3; the other three fixed integer ports are arbitrary. This includes
every symbolic compact tuple, whose beta is `2^(67*8807)−1>2`, without
expanding that integer. This is an external exact polynomial certificate,
not a Lean proof or an unrestricted natural-zero equivalence to the parent.
In particular the candidate still requires the unproved `k≥eta` zero
forcing or a different witness map before it can support a consistency
claim.

## Global upper bound

Treat all witness variables as degree 1 and fixed ports as degree 0. The
literal graph gives degree bounds

```
deg(b)≤1, deg(X)≤2, deg(Y)≤4, deg(U)≤6,
deg(k)≤1, deg(c)≤5, deg(a)≤6, deg(H)≤6,
deg(ell)≤11, deg(Bt)≤3, deg(shift)≤7.
```

The syntactic first/main residual bounds 24 and 34 lose leading terms by
exact free-ring identities. Write

```
D = b*(k+r−k*Bt)−Bt,     Z=b*ell+D,
E = U*X+H*shift,           Dstar=U*a*c+E,
Delta=a²+H.
```

Then the two actual residuals satisfy

```
A0 = 2*b*ell*D + D² − b²*(1+ell*k),
A1 = 2*(U*a*c)*E + E² − U²*(1+H*c²).
```

Here deg(D)≤5 and deg(E)≤13, so deg(A0)≤17 and deg(A1)≤30.
The remaining auxiliary and strong factors have bounds 30 and 22. The output
`(1+A0)*(1+A1)*Fa*Fs−1` therefore has total degree at most
`17+30+30+22=99`. The checker verifies the graph rows, degree arithmetic and
both identities using exact sparse polynomials, not point evaluation.

## Matching lower bound, including the compact tuple

Substitute **every witness variable by t**, keeping all four ports symbolic.
The exact coefficient of t^99 is

```
−16*beta^57*(beta−2).
```

It is independent of the remaining port values and nonzero for every integer
beta≥3. Thus this single ray has degree 99 for every such specialization,
including the compact beta, proving the matching total-degree lower bound.
The checker computes the top 20 coefficients at every graph gate over the
integer polynomial ring in all four formal ports. Truncation is exact in that
window by induction: a discarded input coefficient cannot combine with a
coefficient above the other input's syntactic degree bound to enter the
retained output window. For two **small special-port controls only**, it also
expands the entire ray polynomial independently; those controls are not the
compact-port proof.

The 85-row eta/zeta-natural parent has the same exact degree 99 at those
ports. Its graph is the 84 graph after `k=eta+zeta`, and the inverse
`zeta=k−eta` is an invertible integral homogeneous linear substitution.
Such a change and its inverse preserve total polynomial degree over the
integer coefficient ring. This algebraic degree statement uses unrestricted
integer variables and does **not** remove the separate natural-witness
inequality needed for the zero map.

The receipt records source hashes and the symbolic leading coefficient. No
Lean build, source/provider or axiom validation, decimal/PDF binding, exact
global minimum, or 84-row consistency endpoint is claimed. From
`Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta84-independent-k-degree99/check.py | cmp - research/ordinary13-eta-zeta84-independent-k-degree99/receipt.json
```
