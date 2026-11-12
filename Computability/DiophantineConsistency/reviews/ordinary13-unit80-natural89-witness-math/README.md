# Positive 80 and natural 89: witness replacement in intended models

The selected `ordinary13-unit-product80` and
`ordinary13-natural-unit-product89` graphs are a different chain from the
later square-sum residue-89 candidate. The first has 13 strictly positive
inputs; the second has 13 natural inputs. Exact source-row inspection shows
that the latter substitutes f, r, y directly and shifts the remaining ten
positive inputs by one, with the `kbase`/`r0` cancellation. Both graphs use
the same four port expressions. The row identity is an all-ring polynomial
identity; going from zero existence to a positive valuation additionally
needs the facts below. The existing independent result is external, and no
Lean/iPRA theorem is asserted here.

Work in an ordered natural IΣ₁ model and its difference ring, with the beta
port represented by a positive model natural. The other three ports may be
signed in this local argument. From the ten shifts, `J,w,s,eta,zeta>0`, so
`b=J*beta>0`, `q=1+b≥2`, `X=q*w>0`, `Y=q³*s>0`, `k=eta+zeta≥2`,
`m=X*Y²>0` and `ell=m*k>0`. Also `a=XY+Y` is model natural and
`Delta=a²+4a+3≥3`.

The four factors multiply to one at a graph zero. To conclude each is +1
inside every model, the argument needs the model signed-pair product/magnitude
and mod-four exclusions, not an external integer-only assertion. The first
exclusion uses the graph's exact scale b and `Y=q³s`; the other three match
the generic signed-factor patterns. The separately proposed eta-natural
unit bridge performs analogous work for a different literal; a new 89
client must bind these exact selected rows before invoking it. The finite
mod-four checks in this packet are sanity checks, not a model proof.

With the resulting factor equations, **f and y are forced**, so no witness
replacement is needed for these two natural coordinates:

* The strong equation is `(i*c²)² = Delta*(f²−1)` in the difference ring.
  At `f=0`, its right side is strictly negative while its left side is a
  square; `Delta>0` gives a contradiction. Hence natural `f>0`.
* At `y=0`, the auxiliary equation gives `Delta*(f²−1)*V²=1` in the
  difference ring. Thus the represented natural `Delta` divides one there.
  Reflecting signed divisibility to the natural model and using `Delta≥3`
  rules this out. This argument in fact does not require the previously
  derived `f>0`; it does require the signed-to-natural divisibility theorem.
  Hence natural `y>0`.

For a hypothetical signed-domain variant, replacing f or y by its model
magnitude would preserve their squares because each appears only in its own
squaring row. The selected 89 graph already has natural f and y; that sign
change cannot repair a zero value. It is their forced positivity that matters.

The **r coordinate admits an existential root switch**; it need not be
assumed positive in the input. If r>0, retain the valuation. If r=0, let P be
the exact graph's signed `Bt` and Z its first root. The first factor gives

```
Z = b*(ell+k−k*P)−P,     Z²=b²*(1+ell*(ell+k)).
```

If `P≤0`, the first equality gives `Z≥b*(ell+k)>0`, contradicting the norm
because `(ell+k)²−(1+ell*(ell+k))=ell*k+k²−1>0`. Thus P>0. The signed
magnitude and positive scaled-quotient facts give a model natural tau with
`Z=±b*tau` and `tau²=1+ell*(ell+k)`, hence
`ell<tau<ell+k`. In particular `b∣Z` in the difference ring; the root
equation then gives `b∣P`. Positivity represents P as a model natural, and
signed-to-natural divisibility reflection gives `P=b*t` with natural `t≥1`.
If the positive root were chosen, cancellation of positive b would give
`tau=ell+k−k*P−t≤ell−1`, contradicting `tau>ell`. Hence `Z=−b*tau`.
Replace r by the natural `2*tau>0`. The graph's sole direct r-use is in the
first root, and the update changes `Z` to `−Z`; the first square is unchanged
and F1, Fa and Fs are independent of r. Thus all four +1 factors and the
product output are preserved. This is a **different positive witness**, not
a proof that the original r was forced positive. No K0 sign or upper bound is
needed for this local switch once b, k and the exact first norm are given.

The candidate source interfaces for the nontrivial model steps are
`ReducedNormSigned.natural_magnitude_square`,
`ArithmeticAdaptiveQuotients2011.scaled_quotient`, and
`Trace75IntegralTransport.natural_dvd_of_signed`. The separate source drafts
`ResidueRootSwitchExtractDraft.positive_replacement` and
`ResidueRootSwitchArithmeticDraft.switch_from_zero` propose this fact-level
construction. Their graph clients concern other literals; a selected-89
client must still bind the current signed P/Z, prove its factor units,
perform the r update, preserve its exact four factors, transport all ten
predecessors, and check the all-model/provider/axiom chain. The eta-positive
or gamma sources from a different graph are not needed for this local map.

Two scoped controls show why shortcuts need care:

* The checker evaluates an actual natural-89 valuation with beta=1,
  K0=−1540 and `r=0` for which `q=2`, `X=2`, `Y=24`, `k=2`,
  `ell=2304`, `P=1537`, `Z=−2305`, and the **first norm holds**. Setting
  r=1 breaks that norm, while setting r=4610 flips Z and preserves all four
  factors. Its full graph output is `87155654354552641`, so it is **not a
  graph zero** and says nothing about the fixed compact K0.
* At the fact level, allowing `Delta=−1`, `c=i=1`, `f=y=0` and signed
  ordinate 1 satisfies both strong and auxiliary equations. This is not a
  selected-graph valuation: it shows why the graph-derived positive Delta
  premise cannot be omitted from those positivity arguments.

From this directory run `python3 -I -S -B check.py | cmp - receipt.json`.
The receipt pins both exact graphs, selected source interfaces and the
partial controls. It proves no model theorem, compact-port provenance, parent
endpoint, or physical PDF binding.
