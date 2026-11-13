# Independent check of the all-even-index same-data obstruction

The pinned proof's cancellation, uniform growth inequality, descent to an even A-Pell subgroup and both-sign auxiliary obstruction are mathematically consistent with the actual graph factors. No concrete error was found. Its conclusion is unconditional **within the stated even-index same-data setting**: it does not exhibit a two-norm zero, rule out different first/main data, establish an existential separation, or provide a Lean/iPRA theorem. The uniform cancellation-and-growth argument was suggested during this review and then incorporated by the packet author, so this is a separate verification of a collaboratively developed proof, not an independently discovered one.

For the essential step, write `Delta=d*t²` with squarefree `d>1`, classify positive integer-coordinate norm-one Pell solutions by the least positive unit `epsilon`, and write

```text
A+t*sqrt(d) = epsilon^r,    f+u*sqrt(d) = epsilon^h,
I=d*t*u,                    U_(r*m)=t*c.
```

This is the standard integer-coordinate classification; it is not a claim about an arbitrary half-integral generator of the full quadratic integer ring. The actual graph gives `c | I`, which alone suffices here. Let `D0=gcd(c,d*t)`. As `d*t | Delta` and the main Pell transition gives `c≡m*A^(m-1) mod Delta`, coprimality of A and Delta yields `D0=gcd(m,d*t)≤m`. Gcd cancellation shows `c/D0 | U_h`; since it also divides `U_(r*m)`, Pell strong divisibility makes it divide `U_g` for `g=gcd(h,r*m)`.

If g were proper, `U_g≤U_(r*m/2)`. But for `n=m/2≥1`, the A-Pell recurrence gives `x_n(A)≥n*A`; the unit norm gives `A>t`. Hence `2*x_n(A)≥m*A>m*t≥D0*t`. Doubling the ordinate then gives

```text
c/D0 = 2*x_n(A)*U_(r*n)/(t*D0) > U_(r*n),
```

contradicting its positive divisibility into `U_g`. This strict argument includes `m=2`. Thus `r*m | h`, and `j=h/r` is even. Consequently `f=x_j(A)` is odd and greater than one. The previously independently reviewed anti-diagonal argument, applied directly at this even j, rules out both auxiliary root signs. It does not require the stronger, generally false assertion `c² | y_j(A)`.

The independent checker compares the shared two-norm fields and actual parent unit-factor rows, checks the mod-4 factor extraction, discovers nine small integer-coordinate Pell units by finite search, and tests bounded strong-divisibility and uniform-growth instances with no coprimality restriction. It also checks the former `(A,m)=(3,2)` kernel-gcd complement and a nonfundamental main-unit example. These controls support the ordinary-integer proof; they do not establish general Pell classification, Lean elaboration or model/provider provenance. The earlier independent review of the both-sign anti-diagonal step is pinned separately.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-parent-even-index-unconditional-independent/check.py | cmp - reviews/ordinary13-parent-even-index-unconditional-independent/receipt.json
```

No Lean, build, staging, axiom inspection or model transfer was run.
