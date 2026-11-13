# Independent review of the q² partial tuple's all-strong obstruction

This source-level review examined the [author's universal argument](../../research/p64-qcube75-q2-all-strong-obstruction/README.md)
for the one specified q²-scale first/main/transport tuple. The argument rules
out a simultaneous strong-norm and auxiliary-unit completion for that tuple;
it does **not** rule out different first/main tuples, all graph zeros, or an
existence equivalence. No Lean theorem was produced.

The squarefree factorization of `D`, evenness of `c`, `gcd(c,D)=1`, and the
main Pell norm were independently recomputed. From `I=i*c²` and
`I²=D*(f²−1)`, squarefreeness gives `D|I`; writing `I=D*L` and using the
coprimality gives `c²|L` and `f²−D*L²=1`. Thus `f>1` is odd and has an odd
prime divisor `p` that divides neither `D` nor `c`.

The Pell descent for `D=n²−1` and `I²−1` is valid as described in the
[specific-witness review](../p64-qcube75-q2-strong-choice-independent/README.md).
For a prime `p|f`, the norm-one element `alpha=n+sqrt(D)` satisfies
`alpha^(2N)=−1` for the appropriate strong Pell index `N`; because `2N` is
even and `p` is odd, its multiplicative order is divisible by four. This
uses a finite field containing `sqrt(D)`, so it covers both split and
nonsplit `D` modulo `p`; `p∤D` makes the square root nonzero.

The odd auxiliary Pell index gives the indicated signed Chebyshev relation,
including either sign of `V`. If `u=alpha^j` and `v=alpha^322`, equality of
the relevant coefficients gives `u−u⁻¹=±(v−v⁻¹)`. Factoring in the field
shows `u` must be one of `v`, `−v`, `v⁻¹`, or `−v⁻¹`. Their exponents are
all even modulo the order because both 322 and half the order are even;
an odd `j` cannot give one of them. This confirms the sign and parity
reasoning at source level.

The [independent checker](check.py) reconstructs the finite input facts by
Pell doubling. It also tests the coefficient-parity claim in 97 split and
127 nonsplit small-field orbits of order divisible by four, and checks 26,208
Chebyshev recurrence steps over the sampled small fields. These finite tests
support but do not replace the general argument. The retained
[result](result.json) pins the author packet. Run with:

```sh
nice -n 19 ionice -c 3 timeout 60s python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube75-q2-all-strong-independent/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `f49a0126c9cca8647055cfe56d2903b17dcabd6c096f96664bec916df506a78d` |
| `result.json` | `a185a6a8d3e087bf4baaf695578c082ebbe9448559819c9267c55dcfb48e020e` |
