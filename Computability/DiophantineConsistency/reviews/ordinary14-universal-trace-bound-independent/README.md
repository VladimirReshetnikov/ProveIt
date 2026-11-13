# Independent review: universal trace bound and 73-gate probe

For `X,Y,N≥1`, the stated Pell norm and recurrence give the lower/upper
ordinate bounds. Their ratio gives `c/k≥L^N/2`; direct expansion shows
`X(2A−1)²−2P(X+1)²>0`, so `L>(X+1)²/X≥4`. The strict interval upper bound
then gives `Y+1>2^(R−2)` and hence `Y≥2^(R−2)` by integrality. Thus
`2^R≤4Y<4Y(X+1)+3=H`; together with `0<X<H`, the **unscaled** trace
congruence identifies X and `2^R`. The proof assumes the exact Pell indices
and ratio interval; it does not derive them from the proposed graph.

The 73-row candidate is the literal parent graph with its X=q*w row removed
and positive input X substituted. With positive beta and inputs its
first-factor negative-Pell exclusion still applies: `Y=q³s≥8`, so
`m=XY²≥2`. The three other restricted unit factors retain their modulo-four
exclusions, making the guard factor one at a product zero. This is not a
proof that the probe is equivalent to the parent: the map back still needs
`q | X`, and the submitted q=3 control checks only the stated Pell/trace facts,
not the whole graph or authenticated compact ports.

For the fixed-port degree upper bound, `deg F0≤20`, `deg F1≤28` after
cancelling the common `(Uac)²` term, `deg Fa≤28`, `deg Fs≤22` and
`deg guard≤2`, giving 100. The independent checker verifies source delta,
topology/liveness, port hashes and a distinct modular weighted ray, and
recomputes finite Pell and toy controls. These checks and the external
argument do not establish a Lean degree theorem, iPRA endpoint, full probe
zero or global minimum.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-universal-trace-bound-independent/check.py > /tmp/universal-trace-independent.json
cmp /tmp/universal-trace-independent.json reviews/ordinary14-universal-trace-bound-independent/result.json
```
