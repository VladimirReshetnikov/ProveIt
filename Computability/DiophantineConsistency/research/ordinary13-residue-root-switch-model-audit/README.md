# Existential first-root switch for the compact 13-variable graphs

A positive first-root coordinate can be recovered **without proving that the
original r is positive** and without an upper bound on K0. The argument applies
locally to the pinned 13/89 and 13/88 mixed graphs and to their pointwise-equal
13/88 and 13/87 zeta-fold variants. It is an existential zero map; it does not
claim that `r=0` is impossible. The surrounding J/X/gamma forcing, compact
port conditions, parent calibration and iPRA obligations remain separate.

## Fact-level argument

Work in the repository's ordered natural IΣ₁ model V and its signed difference
ring. Let b>0, ell>0, k>=2 and natural r=0. Let P and Z be signed values with

```
Z = b*(ell+k-k*P)-P,
Z² = b²*(1+ell*(ell+k)).
```

These are the actual first-expression and first-residual equations in all
four pinned graphs. The second equality implies a model-natural tau>0 with
`|Z|=b*tau` and `tau²=1+ell*(ell+k)`, using signed magnitude and the
existing model square-divisibility/scaled-quotient machinery. The two exact
identities

```
tau²-ell² = 1+ell*k > 0,
(ell+k)²-tau² = ell*k+k²-1 > 0
```

give `ell<tau<ell+k`.

If P<=0 then `Z>=b*(ell+k)>0`, contradicting the upper norm bound. Thus P>0.
The norm gives `b | Z`, and the displayed Z equation gives `b | P` in the
signed ring. Positivity of P and b yields a positive model-natural quotient
`t=P/b>=1`, after reflecting the signed quotient into the natural cone. If
Z>=0, then Z=b*tau and cancellation gives

```
tau = ell+k-k*P-t <= ell-1,
```

contradicting tau>ell. Therefore `Z=-b*tau`. Keep all other inputs fixed and
replace r by the model-natural `r'=2*tau>0`. The actual source row for Z is
linear in r with coefficient b, so `Z'=Z+2*b*tau=-Z`. Its square and the
first norm residual are unchanged. The checker confirms that none of the
other three residuals depends on r; consequently the full output remains
zero. If the original r was already positive, retain it. This gives an
existential positive-r witness, not a same-coordinate equivalence or a proof
that r was forced positive.

The proof of this local statement requires only the displayed b, ell, k and
norm facts; it does not assume K0 is nonnegative or satisfy `K0+1<=q²`.
In applying it to these graphs, one must separately obtain b>0, ell>0 and
k>=2 from the other shifted/forced inputs and beta representation. The
existing graph-level J/X/gamma arguments can carry additional K0 and compact
rank bounds; the conditional root switch does not remove those assumptions.

## Source and model boundary

The checked graph dependencies include the exact Z and norm rows, the four
square-sum wiring and absence of r from the main, auxiliary and strong
residuals. The checker proves in a free polynomial ring the difference
identity

```
(Z+2*b*tau)²-Z² = 4*b*tau*(Z+b*tau),
```

and verifies the two Pell-bound identities above. The independently reviewed
[earlier unit-product root-switch argument](../ordinary13-natural-unit-product89/)
uses the same mathematics over standard integers.

The source tree contains `ArithmeticAdaptiveQuotients2011.scaled_quotient`,
`ModelRelationCombining.sq_dvd_sq`, and the natural-cone/order lemmas in
`ModelDifferenceRing`; the checker pins their source signatures. A new client
must still bind the actual graph's signed Z to a model magnitude, obtain and
reflect the positive quotient t, formalize the sign and predecessor updates,
and prove the output evaluation after the witness change. These source
matches are not a Lean elaboration, provider audit or model-to-iPRA theorem.
The separately proposed gamma model bridge, compact port identification,
82↔84↔87/51 parent transfers and endpoint proof remain open with their own
provenance limits.

From `Computability/DiophantineConsistency`, run
`python3 -I -S -B research/ordinary13-residue-root-switch-model-audit/check.py`
to reproduce [result.json](result.json). It checks graph/source hashes and
finite polynomial identities only; it does not execute Lean.
