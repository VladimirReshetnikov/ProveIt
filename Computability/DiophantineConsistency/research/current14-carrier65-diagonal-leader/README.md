# External diagonal leading-coefficient certificate

`verify.py` reads the SHA-pinned inert 65-gate graph and calculates the
coefficient of the highest possible power of `t` after substituting every one
of the fourteen inputs by `t`, keeping all four ports formal. Coefficients
are exact sparse integer polynomials in `(beta, K, mu, omega)`. The main-norm
cancellation identity is independently expanded and checked in five formal
variables; the leading-term propagation then uses that identity at the Q
node. Any complete cancellation of a tracked highest coefficient causes the
script to fail instead of silently dropping lower-degree terms.

The resulting factors are:

| Factor | Degree bound in `t` | Coefficient at that degree |
| --- | ---: | --- |
| P | 22 | `-4 * beta^14` |
| Q | 18 | `16 * beta^11` |
| U | 62 | `64 * beta^34` |
| W | 2 | `-2` |
| Z | 46 | `-16 * beta^28` |
| whole output | 150 | `-131072 * beta^87` |

Thus, as an external exact-arithmetic calculation, the diagonal polynomial has
degree 150 whenever beta is nonzero, independently of the other ports. The
fixed degree bound 150 and the displayed coefficient are symbolic identities;
the nonzero-beta condition is necessary for this particular leading witness.
The script should be run with `python3 -I -S -B verify.py` from this directory
or with its full path. It imports only the Python standard library.

This packet is not a Lean proof, a proof of `totalDegree` for the maintained
Lean polynomial, or a formal TeX/PDF byte binding. The separately audited
Lean circuit-evaluator bridge supplies an in-Lean connection between the
transcribed graph and `Carrier65.value`; this Python computation has not been
connected to that theorem inside Lean. The [independent external review](../../reviews/current14-carrier65-diagonal-leader-independent/)
passed, including a separate symbolic reconstruction and full integer
polynomial samples.
