# Targeted audit and proposed corrections

## Pin and scope

Repository reference: `3338e535ef54ad8f6be56bdce8b3d084a2924465`. The source inventory records blob identifiers so that a later moving `main` need not be mistaken for the reviewed text. The incoming directory was inventoried and relevant available article scope excerpts were consulted. This is not an exhaustive proof audit of all incoming archives.

## Actual notation repair

In the Hurwitz–polylogarithm transport proof in `05-real-positive-kernel.tex`:

- Change “with q=n” to “with x=n” (the referenced formula in `05-real-orders.tex`, label `subunit:eq:hurwitz`, uses x as its positive scalar argument).
- Change “boundedness of h” to “boundedness of q”. The defined regularized kernel is `q(t)=1/(1-exp(-t))-1/t`, with `1/2<q(t)<1`.

These are notation repairs, not a refutation of the identity. Deduplicate them against other incoming audit notes at integration time. No claim of first discovery is made.

## Status changes supported by this delivery

The final open-problem remark in the local-radius section should distinguish the now-proved all-radius region `a>=8,b>0` and the explicit finite-b transfer region from the remaining cases. The old local theorem remains valid and correctly scoped; it is not replaced by a claim that every local sign is global.

The Cartesian-motion section's `b=infinity` theorem is inherited. The present result adds a quantitative theorem for finite b, with uniform derivative control, rather than rediscovering the exact limit.

## Scope distinctions to preserve

Strict decrease of theta, increase of rho*cos(theta), and decrease of cos(theta)/rho are different claims. The main theorem concerns the third.

The prior fractional bifurcation work is local in radius, even when a coefficient-sign classification is global along an order-parameter threshold. The present two all-radius regimes do not disprove or subsume those local turning points.

The new positive measure has a squared resolvent. It must not be substituted into the signed first-resolvent theorem without changing the moments and kernel.

The binomial transform is not a sharper replacement for the existing Euler algorithm. An infinite convergent identity is not a finite arithmetic reduction or an S6/S8 proof.

No new fatal flaw in the inspected local-radius proof was established by this audit.
