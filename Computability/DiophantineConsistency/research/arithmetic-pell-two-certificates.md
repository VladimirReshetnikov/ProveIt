# The final relaxed-norm divisibility from two coefficient certificates

27 October 2026. This argument is now proved in
[ArithmeticPellIndexDivisibility](../Lean/DiophantineConsistency/ArithmeticPellIndexDivisibility.lean),
with [independent acceptance](../reviews/arithmetic-pell-index-divisibility-root.md).
Every quantity below may be an arbitrary internal element of an IΣ1 model.

Fix A=a+2 and D=delta(a), so A*A=1+D. Write X(j),Y(j) for the actual
represented Pell coordinates. The existing certificate convention is

```text
Bez(x,y,g) := ∃u v w z, g+x*u+y*v=x*w+y*z.
```

Every common divisor of x,y divides g, including divisor0. This is the
already proved actual `bez_divisor`, not an appeal to standard-Nat gcd.

## Exact quotient induction supplies the index certificate

At every internal j, one of these exact natural quotient shapes holds:

```text
X(j)=1+D*u, Y(j)=A*j+D*v,
or
X(j)=A+D*u, Y(j)=j+D*v.
```

At0 the first shape has u=v=0. The actual successor recurrence swaps the
shapes using these nonnegative coefficients:

```text
first → second: u'=A*u+A*j+D*v, v'=u+j+A*v;
second → first: u'=1+A*u+j+D*v, v'=u+A*v.
```

The disjunction is Sigma1, so genuine internal successor induction applies.
There is no need to identify a shape by a separately represented parity
test. In the second shape, j+D*v=Y(j). In the first, multiplying Y(j)
by A and using A*A=1+D gives

```text
j+D*(j+A*v)=A*Y(j).
```

Thus `Bez(Y(j),D,j)` holds in either case, with explicit natural
coefficients. This works at index0 too.

## Composition and two scaled certificates

Suppose p|m and Y(p)*Y(p)|D*Y(m). We seek Y(p)|m. The p=0 case forces
m=0 and is immediate. Otherwise set c=Y(p)>0 and F=X(p)>1. Only after
deriving F≥2 define B=F−2. The norm and actual composition theorem give

```text
delta(B)=D*c*c,
m=p*k,
Y(m,a)=c*Y(k,B).
```

The supplied square divisibility has an actual quotient v. Substitute the
composition identity and cancel the proved positive c to get
`D*Y(k,B)=c*v`. Hence c divides both D*Y(k,B) and delta(B).

First multiply `Bez(Y(k,B),delta(B),k)` by D, absorbing D into the second
coefficients. This gives

```text
Bez(D*Y(k,B),delta(B),D*k),
```

so c|D*k. Now multiply `Bez(c,D,p)` by k, absorbing k into the first
coefficients. It gives `Bez(c,D*k,p*k)`. Since c divides both c and D*k,
we obtain c|p*k=m. Neither scaling transformation cancels its scale, so
both remain valid when k=0.

## Applying this to the actual relaxed norm

The independently accepted IntegralSolution theorem already obtains the
same positive m with p|m and R=D*Y(m), where R=i*c*c. Thus c*c divides
D*Y(m), with witness i, and the argument above gives c|m. Combining the
results proves the actual relaxed auxiliary norm implication with both
divisibilities, for additive and justified truncated norm inputs.

This replaces the external proof guide's cubic-congruence/power-cancellation
step for the conclusion needed here. It does not assert that stronger
congruence theorem. Later target-index recovery, signed carrier alignment,
cofinal witness construction and the final HA equivalence remain separate.
