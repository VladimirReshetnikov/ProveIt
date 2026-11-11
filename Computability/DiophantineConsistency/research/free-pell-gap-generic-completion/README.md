# Generic strong and relaxed-auxiliary completion

This is an ordinary mathematical completion lemma for the 64-gate
free-Pell-gap candidate of `../current14-carrier64-free-pell-gap-toy-zero/`.
It does not construct an actual-port first/main seed or full zero, prove a
Lean theorem, or establish unrestricted existential nonequivalence.

Suppose positive integer data for the candidate have already supplied a
positive rank R, positive c, and a positive main trace D with

```
A>=3, c>=2, Delta=A²−1, D²−Delta*c²=1.
```

Then one can choose positive f,i,T,t such that the literal
`S=Delta*i*c²` and `V=f²*(c*T−R)−c` satisfy

```
f²−Delta*(i*c²)²=1,
V²−(S²−1)*t=1,
V²+t is not a square.
```

Thus, **if separately supplied** positive scalar, first-Pell and main-Pell
coordinates make the first, main and transport factors 1, this lemma
completes all remaining factors of the free-gap candidate and blocks its
natural same-other-coordinates reverse map. It makes no claim that every
candidate zero has transport factor 1: the relaxed auxiliary factor need
not retain the old mod-4 sign exclusion.

Choose an even positive power

```
f+L*sqrt(Delta)=(D+c*sqrt(Delta))^(2h)
```

whose ordinate L is divisible by c². Such an h exists by taking the order
of the norm-one unit modulo c². Set `i=L/c²` and `S=Delta*L`. Positivity
and the strong norm are immediate. Positive Pell classification writes the
main unit as a power of `A+sqrt(Delta)`; its even power therefore has
`f=±1 mod A`, so `gcd(A,f)=1`. Also `f²=1 mod c`, and

```
S²−1 = −(Delta+1) = −A² mod f².
```

Thus `S²−1`, c and f² are pairwise coprime. CRT gives an infinite positive
arithmetic progression satisfying

```
V = 1 mod (S²−1),  V = −R mod c,  V = −c mod f².
```

For any V>1 in this progression,

```
t=(V²−1)/(S²−1),
T=(V+c+f²*R)/(c*f²)
```

are positive integers and satisfy the literal V expression and the relaxed
auxiliary equality. If `V²+t` were a square y², then
`(S*V)²−(S²−1)*y²=1`. Positive solutions are powers of the fundamental
unit `S+sqrt(S²−1)`, so at most logarithmically many V coordinates lie
below a bound. The CRT progression has positive linear density. Therefore
some positive V in it gives a nonsquare `V²+t`, as required.

The checker pins the original gate source and verifies three exact small
instances, including coprimality, CRT reconstruction, all integer divisions,
and nonsquareness. It is a control, not a proof of the unbounded Pell
classification, an actual-port seed, or a model/endpoint theorem.

```
python3 -I -S -B research/free-pell-gap-generic-completion/check.py > /tmp/free-pell-gap-generic.json
cmp /tmp/free-pell-gap-generic.json research/free-pell-gap-generic-completion/result.json
```

Independent external review is recorded in
`../../reviews/free-pell-gap-generic-completion-independent/`.
