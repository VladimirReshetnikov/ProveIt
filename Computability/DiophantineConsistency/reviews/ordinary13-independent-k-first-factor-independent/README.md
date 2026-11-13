# Independent review of the independent-k first-factor audit

This review checks `research/ordinary13-independent-k-first-factor-audit/` against the exact 84-row candidate. The deterministic checker pins its inputs, reproduces the author's receipt, checks the relevant graph wiring and independent integer-polynomial identities, and evaluates bounded controls. Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-first-factor-independent/check.py | cmp - reviews/ordinary13-independent-k-first-factor-independent/receipt.json
```

All reasoning below concerns ordinary nonnegative integer inputs and positive integer beta; it is not a Lean theorem or a proof of an all-model bridge.

Write `b = J*beta > 0`, `q = b+1`, `F = n_F+1`, `alpha = n_alpha+1`, `d = X+K0`, `C = q-F-alpha`, `B = C*d-F`, and `ell = X*Y^2*k`. The actual first graph residual is

```text
Z = b*(ell+k+r-k*B)-B,
A0 = Z^2-b^2*(1+ell*(ell+k)).
```

If `k>0` and `C≤0`, then `B<0` and `Z>b*(ell+k)>0`. Yet `(ell+k)^2 - (1+ell*(ell+k)) = ell*k+k^2-1≥0`; hence `A0>0`. Thus `A0=0` implies `F+alpha<q`. This uses no inequality between eta and k.

If `k=0`, `A0=0` is equivalent to `B=b*(r-1)` or `B=b*(r+1)`. If `B≥0`, then `C>0` because otherwise `B=C*d-F<0`. The only negative branch is `r=0, B=-b`; it is equivalently

```text
(q-F)*(d+1) = alpha*d+1.
```

This is the exact negative-B exception, not a classification of all graph zeros. The displayed partial family `J=1, F=beta, alpha=1, X=0, k=r=0` realizes it for any natural eta and positive `s`, with `B=-beta`, `Z=beta`, and `A0=0`.

For this particular family, `q=beta+1≥2`, `a=Y>0`, `U=a*q²`, `H=3+4*a`, `R=q*(q²-1)+MC+q*MF`, and

```text
Dstar = U*a*eta + H*(U*gamma+R+1),
Delta = (a+2)^2-1.
```

The graph's main residual is `A1=Dstar²-U²*(1+Delta*eta²)`. The checker verifies the exact identity

```text
H*(R+1)-2*U*q
 = 2*a*q*(q²-2) + 3*q*(q²-1) + H*(MC+q*MF+1),
```

whose right side is positive for these natural values. Consequently `Dstar>U*(a+2)*eta` when `1≤eta≤q`, and `(a+2)²*eta²≥1+Delta*eta²`; hence `A1>0`, confirming the author's scoped exclusion. The same inequality also shows `A1>0` at `eta=0`: then `Dstar>2*U*q>U` and the comparison radicand is 1. Thus this one partial family is excluded for the slightly wider interval `0≤eta≤q`.

Furthermore, for these standard integer inputs the exact graph output plus 1 is a product containing the integer factor `1+A1≥2`. It cannot equal 1, so the full output is nonzero for this same family and interval, independently of the other factors' signs. This is not an exclusion of other exceptional inputs, nor an internal model-theoretic factor-extraction argument.

The finite checks are controls, not the proof of the quantified inequalities. The review does not establish a Lean elaboration, arbitrary-model interpretation, general `k=0` elimination, replacement witness, or the requested iPRA consistency equivalence.
