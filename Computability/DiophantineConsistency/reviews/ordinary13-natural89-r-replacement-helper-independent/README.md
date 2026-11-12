# Independent review: natural-89 r-switch helper and k bound

This review is intentionally limited to the fact-level root-switch helper,
its signs/divisibility, and the `b>0`, `k≥2` inputs used by
`research/ordinary13-natural89-r-replacement-model-draft/`. A separate review
covers the graph evaluation and preservation of all four factors. The pinned
source and author receipt are unelaborated; neither review establishes a
model theorem or an endpoint.

At r=0 the helper assumes a model natural `b>0`, natural `ell`, `k≥2`,
and signed P,Z with

```
Z = b*(ell+k−k*P)−P,    Z²=b²*(1+ell*(ell+k)).
```

If `P≤0`, then `Z≥b*(ell+k)>0`; the squared norm is too small because
`(ell+k)²−(1+ell*(ell+k))=ell*k+k²−1>0`. Thus `P>0`.
The helper represents that positive signed P by a positive model natural,
uses signed magnitude plus `scaled_quotient` to obtain natural tau with
`Z=±b*tau` and `tau²=1+ell*(ell+k)`, and derives `tau>ell`. This gives
signed `b∣Z`; the exact root equation gives signed `b∣P`. Only after P has a
natural representative does `natural_dvd_of_signed` supply `P=b*t` in the
natural model, with t positive.

The positive sign would give `tau=ell+k−k*P−t≤ell−1` since `P,t≥1`,
contradicting `tau>ell`. Thus `Z=−b*tau`; taking `r′=2*tau>0` changes the
first root by `2*b*tau` and flips its sign. The inspected source
certificates use the correct signs: `hz-hw` for signed `b∣P`,
`hs-hz+hpcast` for the excluded positive branch, and `2*hneg-hz` for the
root flip. P may initially be signed; no K0 bound or `ForcedEta` premise is
used in this helper.

The actual replacement client sets `ell=m*k`, obtains b>0 from the prototype
J-positive source and the compact beta lower bound, and normalizes the prior
first norm via `(m*k)*(m*k+k)=m*(m+1)*k²`. The forward eta increment makes
the prototype eta coordinate at least 1; the existing zeta coordinate is
`v10+1≥1`, hence the helper's `k≥2`. It does not need the separate reverse
eta map or an all-model `ForcedEta` assumption. The helper itself only needs
`ell≥0`, not the stronger `ell>0` sometimes used in external expositions.

The checker includes two **fact-level controls, not graph zeros**: with
`b=1, ell=0, k=1, P=0`, the displayed norm holds and P is not positive, so
the helper's proof cannot simply omit k≥2 under its present weak assumptions;
with `b=1, ell=0, k=2, P=1`, tau=1, the root switch works. It also checks
27,456 bounded signed-root instances and the exact helper input source. These
finite tests are not a proof in nonstandard models.

No mathematical sign or stated-interface defect was found in this narrow
review. The positivity, signed magnitude, scaled quotient, signed-to-natural
divisibility, graph binding and actual Lean tactics/providers remain
unelaborated. The parent bridge, all-model zero maps and physical/PDF or
iPRA endpoint remain separate. Reproduce the pinned receipt from this
directory with `python3 -I -S -B check.py | cmp - receipt.json`.
