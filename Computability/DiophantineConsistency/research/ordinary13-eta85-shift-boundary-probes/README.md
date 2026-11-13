# Two additional 84-row shift probes for the eta/zeta parent

These are **exploratory candidates**, not established reductions. Starting from the pinned exact 85-row parent `ordinary13-eta-zero-graph-adapter-audit/prototype.json`, `F-probe.json` deletes `F=n_F+1` and uses `n_F` in its place. `alpha-probe.json` does the analogous operation for `alpha=n_alpha+1`. Each has 13 natural inputs and 84 graph operations. An ordered expression-tree identity checks that the parent output at any integer ports and natural valuation equals the corresponding probe output when the one changed input is incremented by one. Thus every parent zero maps forward; reverse existential zero preservation is open. No new equivalence, Lean theorem or iPRA endpoint is claimed.

At the signed ports `(-1,0,1,0)`, the shared natural valuation

```text
(1,0,0,1,0,0,0,0,0,0,0,1,0)
```

is an actual full zero of each probe: its first/main/strong residuals are zero and its auxiliary factor is one. The parent at that *same* valuation has output 9. This shows that simply assuming the new unshifted coordinate is positive is invalid for arbitrary signed ports, and that same-valuation equality does not hold. It does **not** refute a reverse map that changes witnesses, and does not give a zero or counterexample at the fixed compact positive ports.

## A smaller remaining case for the F probe

There is a partial standard-integer exclusion for a potential F-probe zero with F=0. Assume the first and main residuals both vanish and the represented ports satisfy

```text
beta>0, J>0, K0>0, 0<MC<beta, 0≤MF<2*beta.
```

The actual graph has `q=1+beta*J≥2`, `Y=q³s>0`, `k=eta+n_zeta+1≥1`, `ell=X*Y²*k≥0`, `C=q−alpha`, `B=C*(X+K0)` and `b=beta*J>0`. If C<0 then B<0 and the first root

```text
Z=b*(ell+k+r−k*B)−B
```

is strictly greater than `b*(ell+k)`. This contradicts the first norm since `(ell+k)²−(1+ell*(ell+k))=ell*k+k²−1≥0`.

If C=0, then B=0. Cancel b² in the first norm and subtract the right side:

```text
(ell+k+r)²−(1+ell*(ell+k))
  = ell*k+k²−1+2*r*(ell+k)+r² = 0.
```

All displayed terms are nonnegative, forcing k=1, r=0 and ell=0; Y>0 then gives X=0. The exact graph rank becomes

```text
R=q²*(q²−1)+J*(MC+q*MF).
```

At k=1 the main root has the form `U*(...)+H*(U*gamma+R)`, where `U=q⁵s` and `H=3+4Y≡3 (mod q³)`. The main norm gives `q⁵ | H*R`, so standard integer gcd cancellation gives `q⁴ | R`. Write `W=J*(MC+q*MF)`. The bounds give `0≤W<(q−1)*(1+2q)<2q²`, and the rank congruence is `R≡W−q² (mod q⁴)`. Hence `W=q²`. As `gcd(J,q)=1`, this entails `q|MC`, contradicting `0<MC<beta≤q−1`. Thus F=0, C≤0 is impossible under those explicit assumptions and both norm equations.

The remaining F=0, C>0 case is not resolved, nor is any alpha=0 reverse map. The argument also does not itself extract the two norm equations from a product zero or formalize the port assumptions in a model. A proof of those steps is necessary before either probe could replace the parent.

## Reproduction

The candidate generator writes the two inert JSON files; the read-only checker verifies the parent-to-child expression-tree identities and both exact signed-port full zeros. It also runs bounded controls for the rank-divisibility exclusion; those finite controls are not the proof above. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-eta85-shift-boundary-probes/check.py | cmp - research/ordinary13-eta85-shift-boundary-probes/receipt.json
```

No Lean process, build, provider validation, or parent-child zero equivalence was performed.
