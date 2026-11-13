# Positive 84 ↔ 87/36: q³ first-carrier unscaling audit

This bounded audit compares the exact two positive-input JSON graphs and
identifies model-source interfaces. It does not prove a Lean graph map,
all-model equivalence, provider closure or iPRA endpoint. The witnesses agree
except at position 7: the 84 graph uses s and defines `Y=q³*s`, whereas the
87/36 graph uses Y directly; position 8 is r in both. Both use the same four
port positions.

Write `b=J*beta`, `q=1+b`, `h=q³`, `m=X*Y²`, `k=eta+zeta`,
`ell=m*k`, and `B=(q-F-alpha)*(X+K0*q)-F*q`. Signed differences in these
formulas are in the model's difference ring. With `Y=h*s` and
`r_old=r_new-s`, the exact first expressions and residuals satisfy

```
Z_new = b*(ell+k+r_new-k*B)-B,
Z_old = h*b*(ell+k+r_old-k*B)+Y*b-h*B = h*Z_new,
A_new = Z_new²-b²*(1+ell*(ell+k)),
A_old = Z_old²-(h*b)²*(1+ell*(ell+k)) = h²*A_new.
```

The receipt checks the entire graph row delta and proves these identities in
a free integer polynomial ring, without finite-sample inference. The main,
auxiliary and strong residual rows are identical and their dependency graphs
exclude r. Both outputs are sums of their four residual squares; the total
outputs are **not** pointwise equal, because the old first square is scaled
by `h⁴=q¹²`. Their common vanishing follows only after using the ordered
integral-domain and positive-scale facts.

## From positive 87/36 to positive 84

A first residual zero gives `Z_old²=(h*b)²*n` for the model-natural
`n=1+ell*(ell+k)`. Because beta and J are positive, b and h are positive.
`Ordinary13QCube93ArithmeticDraft.positive_quotient_of_signed_norm` has the
matching fact-level *shape*: set its signed t to `ell+k+r_old-k*B`, its
signed bt to B, and its natural y to the actual old Y. Its conclusion is a
positive model-natural s with `Y=h*s`. This draft uses signed square
divisibility, the explicit identity
`(1+b)³-b*(b²+3b+3)=1` to cancel b from `h∣Y*b`, and signed-to-natural
divisibility reflection. The 13/93 draft is unelaborated, and applying it here
still needs the exact 87/36 literal first-norm binding, represented natural
beta, and matching casts; it is not a theorem about this graph automatically.

Set `r_new=r_old+s>0` and keep all other coordinates, with Y replaced by s.
The identities above give the new first residual zero after cancellation of
positive h², and the unchanged non-first residuals vanish. Both source and
target positive tuples and the exact model ring/natural casts still require
Lean proofs.

## From positive 84 to positive 87/36

The naive predecessor `r_old=r_new-s` is not known positive: the receipt
records the isolated scalar values `r_new=1,s=2` as a counterexample to that
positivity inference, **not** as a graph zero. A fresh first-root branch avoids
relying on the original sign or on this predecessor.

From the actual 84 first residual, use natural signed magnitude and positive
b to obtain a same-model tau with `|Z_new|=b*tau` and
`tau²=1+m*(m+1)*k²=1+ell*(ell+k)`. Here
`ArithmeticAdaptiveQuotients2011.scaled_quotient` and the fact-level signed
magnitude adapters have the relevant conditional signatures. Since `m>0` and
`k≥2`, the norm gives `tau<ell+k`. If the signed B were nonpositive, the
actual positive r would give `Z_new>b*(ell+k)`, contradicting the norm;
thus B is positive. The first-root equation also gives signed `b∣B`, and
signed-to-natural divisibility reflection supplies natural `P=B=b*t` with
`t>0`. Each comparison, cast, representation and quotient requires its own
actual-graph model proof; it must not be inferred from a standard-integer
zero.

The 84 main residual and positive U similarly yield a same-model natural
main root d. The source-only `FirstMainLargeKDraft.first_main_large_k` or
`EtaNaturalNormLargeKDraft.large_first_ordinate` proposes
`k≥8*m+4` from these exact first/main norms, positive X/Y and the required
eta/zeta hypotheses. These drafts are unelaborated and require the 84 graph
field bindings and compatible model providers.

There is a shorter candidate proof of the specific root margin than the
standard packet's `tau-ell>k/4`: `P73Converse.lean` contains the **private**
source lemma `tau_gt`, which states in the difference ring that

```
tau²=1+ell*(ell+k), tau≥0, 3*s≤k, 0≤s≤ell
    imply ell+s<tau.
```

For the present inputs, `Y=q³*s≥s`, `m=X*Y²≥Y`, `k≥8*m+4≥3*s`, and
`ell=m*k≥s`; their model proofs and casts must be supplied. Since the source
lemma is private, it is not an importable interface: an independently
attributed adaptation and its Lean/provider validation are still required.
Its argument is elementary: assuming `tau≤ell+s` and squaring gives a
contradiction because `ell*(k-2s)≥ell*s≥s²`, with the final `+1` strict.
No nonstandard finite enumeration is involved.

With `delta=tau-(ell+s)>0`, choose the *new old-graph* first coordinate

```
r_old = k*(P-1)+t+delta > 0.
```

Then `r_old+s=k*(P-1)+t+(tau-ell)`, so the fact-level
`CarrierWitnessFactsDraft.positive_target_root` proposes the new unscaled
root `+b*tau`; the old scaled root is `+h*b*tau`. The old first residual
vanishes and the other three are independent of r. This is an existential
root switch, not a pointwise inverse. The helper's natural-P, t and tau
premises must be produced from this 84 zero, not assumed from the unrelated
81/83 graph.

The sources and proposed lemmas cited here do not authenticate their compiled
providers, their transitive axioms, the exact compact port selection or the
physical equation/PDF. Both all-model positive-zero directions and the
subsequent 87/36 endpoint chain remain open.

From `Computability/DiophantineConsistency` reproduce the receipt:

```
python3 -I -S -B research/ordinary13-positive84-to87-unscale-model-audit/check.py
```
