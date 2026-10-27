# Common discriminant without a squarefree decomposition

27 October 2026. ROOT's paper derivation for the remaining internal relaxed
Pell norm. This is a proposed formalization route, not a Lean theorem or a
completed integrality certificate. It supplements the frozen
[known-unit plan](arithmetic-pell-known-unit-next-plan.md).

Suppose positive natural quantities satisfy

```text
A² = 1 + D,        R² = D*(f²-1),        R = i*c².
```

Set g=gcd(R,D), R=g*t and D=g*d. Positivity gives g,d,t>0;
the normalized factors t,d are coprime. Cancelling g in the norm gives
g*t²=d*(f²-1). Thus d divides g*t². Coprimality of d and t² implies
d divides g. Write g=d*s. Cancellation now yields

```text
D = d²*s,        R = d*s*t,        f² = 1+s*t².
```

In particular s>0, and both (A,d) and (f,t) solve x²=1+s*y².
The known positive unit (A,d) bounds a search for a least positive unit
(F,v). The proposed internal known-unit classification then gives indices
e,n for the same represented sequence with base F:

```text
A=x_F(e), d=v*y_F(e), f=x_F(n), t=v*y_F(n), F²=1+s*v².
```

Writing S=y_F(e) and T=(F²-1)*S gives exactly

```text
D = (F²-1)*S²,        R = T*y_F(n),        D = T*S.
```

These are the common-unit identities used in steps3–4 of the external
`PellRelaxedMain.relaxed_aux` proof. They follow without requiring s to be
squarefree or invoking a general Pell existence theorem. The already known
solution supplies the finite search bound. Since d>0, e>0; the separate
ordinate growth theorem gives S<A, as required by the later size argument.

The remaining formal obligations are real: construct an internal gcd and
its exact quotient/coprimality laws; cancel positive factors; prove the
known-unit classification by bounded search and descent; and establish
sequence composition, strong divisibility, the large-c estimate and the
final cubic-modulus congruence. No standard-Nat gcd fact can silently
replace those model-uniform statements. This algebra only replaces the
squarefree/fundamental-unit setup of the external proof; it does not prove
the full relaxed norm, c|m, carrier index recovery, or the HA endpoint.
