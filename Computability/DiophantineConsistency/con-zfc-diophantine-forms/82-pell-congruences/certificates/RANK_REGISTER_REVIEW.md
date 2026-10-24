# Independent review of the retained-rank endpoint

This is an internal mathematical review performed independently of its
constructor. It is not external peer review or a proof-assistant certificate.

The delivered `transport/degree20_20_rank_register.json` was checked against
the eighteen-variable formula. Its twenty variables and eight residuals are
exactly the two-register lift with the monic defining rows

```
R_register - R_native = 0
E - X*Y = 0.
```

Forgetting `R_register,E` gives a polynomial zero-set bijection with the
eighteen-variable equation; conversely their unique values restore all
abbreviations and residuals. The six original rows are unchanged under
that substitution, and all variables remain unrestricted integers.

In serialized order the residual degrees are

```
5, 6, 6, 4, 10, 10, 10, 8.
```

The auxiliary residual's degree-ten homogeneous part is

```
-8*r^2*c^5*y_gap*f*T + 8*r^2*c^4*y_gap*f^2*R_register.
```

No other residual contains both `r` and `y_gap`. The coefficient of

```
r^4*c^8*y_gap^2*f^4*R_register^2
```

in the single sum-of-squares polynomial is therefore exactly 64. This
proves degree twenty without a generic-parameter assumption or any
large-coefficient specialization. No mathematical, domain, or inverse-map
defect was found in the reviewed endpoint.
