# Independent source review: 84 scalar rank window

The own-zero guard supplies the `F+alpha<q` premise, with positive J, F and
alpha from the valuation. The source's explicit bounds `MC<beta` and
`MF<2*beta` and identity `q=beta*J+1` match the scalar-window interface. Its
natural rank expression agrees after the justified `q−1=J*beta` rewrite.
The stated result is **24≤R**, the scalar upper window, and `R+1<q⁴`; it
does not state the 26 lower bound needed by the later exact-index interface.

An additional mathematical observation, not proved by this draft: the same
positive F/alpha and guard-gap hypotheses give q≥3, q−F≥2 and q−1≥2. Hence
the rank factor is at least 5 and q²−1 at least 8, so R≥40. The finite
checker includes a scalar/guard example with R=40; it is not a full graph
zero. A separate model proof of this stronger bound and Lean elaboration are
still needed.

The checker pins the interfaces, replays the author and independent rank
reviews, and tests a finite scalar grid. This is source and finite review
only, with no provider, physical-file or iPRA endpoint claim.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-rank-window-draft-independent/check.py > /tmp/rank-window84-independent.json
cmp /tmp/rank-window84-independent.json reviews/ordinary14-84-rank-window-draft-independent/result.json
```
