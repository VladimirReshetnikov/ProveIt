# Partial obstruction to freeing the main auxiliary coordinate

In the 76Y graph, put `r=k−R−1` and `U=Y²`. The main carrier contains
`U*gamma−r`. Replacing positive `gamma` by an independent positive witness
`h`, and using `h` directly there, removes four gates: `k−R`, its `−1`,
`U*gamma`, and the final subtraction. The resulting **experimental graph**
has 14 positive inputs and 72 live operations (41 multiplications, 18
additions, 13 subtractions). This arithmetic count is not a claim of a
zero-existence equivalence or an iPRA endpoint.

## Why the forward coordinate is plausibly positive

Assume an original positive zero supplies the oriented natural main root
`g` and the zero-specific estimate `c≥2(a+2)` from the independent-`y`
argument. The main-root alignment and `r=k−R−1` give

```
U*(g−(X+a*c)) = H*(U*gamma−r).
```

Here `U>0`, `H>0`, `Y≥1`, `a=Y*(X+1)`, and `X≥0`, so
`c≥2(a+2)>X`. The root equation gives

```
g² − (X+a*c)²
 = (2*a+2)*c² + 2*a*c*(c−X) + (c²−X²) + 1 > 0.
```

Because both `g` and `X+a*c` are nonnegative, `g>X+a*c`. The alignment
then implies `h=U*gamma−r>0`. [`check_forward.py`](check_forward.py)
checks the displayed polynomial identity exactly and the sign on 120
bounded natural examples; three of those happen to give integral `h` in
the alignment. This remains a paper argument using the cited zero-specific
bound and *oriented* root equation, not a checked Lean composition or a
claim that the examples are graph zeros. The converse still requires the
divisibility and positivity needed to recover `gamma`.

The obvious inverse requires a positive model-natural `gamma` satisfying

```
U*gamma = h+r.
```

The following exact partial assignment shows that the main, strong and
transport residuals alone do **not** force even its divisibility condition:

```
beta=1, J=3, q=4, F=alpha=z=w=s=1,
K0=1, MC=MF=0, Y=64, U=4096, X=4,
eta=4, zeta=6, k=10, c=644, R=150,
a=320, H=1283, Delta=103683, h=4096, r=−141.
```

Transport is zero. The scalar main root `g=207367` satisfies
`g²=1+Delta*c²` and `g=X+a*c+H`; hence the free main carrier equals `U*g`
and its main residual is zero. The verifier constructs positive strong
witnesses as follows: let `f+c_n*sqrt(Delta)=(g+c*sqrt(Delta))^644` and
`i=Delta*c_n/c²`. Exact arithmetic checks that `c² | c_n`, that `i>0`, and
that `(i*c²)²=Delta*(f²−1)`, so the strong residual is zero. The values of
`f` and `i` have 12,018 and 12,007 bits respectively.

Nevertheless `h+r=3955`, which is positive but strictly below `U=4096`; no
natural `gamma` can satisfy the displayed inverse. The verifier evaluates
the **actual modified 72-row graph** on a complete positive tuple with
`T=t=y=1`, checks `M=W=Lt=0`, and checks that the output is not zero.

This is **not a full graph zero or an existence-equivalence counterexample**.
Indeed, with `P=X*Y²=16384`, the first-unit condition would require
`t²=1+P*(P+1)*k²=26845184001`, strictly between `163844²` and `163845²`.
The auxiliary unit condition is not satisfied by the exhibited tuple either.
Those remaining zero constraints may eliminate this obstruction or permit a
different witness normalization. The example proves only that transport,
main and strong residuals, positivity, and the q-cube coordinate relations
alone cannot justify the direct gamma inverse.

[`check.py`](check.py) pins the 76Y graph, constructs the 72-row DAG, checks
all gate/input liveness, verifies the displayed exact arithmetic and Pell
construction, evaluates the full modified graph at the stated tuple, and
checks the nonsquare first-norm target. It limits Pell operands to 20,000
bits and graph values to 200,000 bits. The [result](result.json) records
its hashes and bounded observations. No Lean process was run. Reproduce:

```sh
nice -n 19 ionice -c 3 python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube72-free-main-obstruction/check.py
nice -n 19 ionice -c 3 python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube72-free-main-obstruction/check_forward.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `3e6e3fa65c5ad32886f165811556736733118cf31550c5c2071f031fa64ad4de` |
| `result.json` | `65175e0ed6945fa2a09bd6c23d4e25df38301a1b831d93ab1fcabfbf0e535bee` |
| `check_forward.py` | `e6d01af0a9770c4ac1e21b38a550660638993421a51c0199355fe4b62047a6fb` |
| `forward-result.json` | `094a204ef4f8c63da56ab9ddab3eb1c76ecafa405a272525ca613e44f67e92c2` |
