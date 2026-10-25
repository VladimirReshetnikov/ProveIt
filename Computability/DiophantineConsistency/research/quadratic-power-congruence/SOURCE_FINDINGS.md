# The existing best quartic already retains shared moduli

This is a negative size finding from inert inspection of the accepted
Round15 source and its principal integer442/projected.json. No incoming
executable or projector was run for this inspection.

The complete source has five T-definition rows, at indices 221, 236, 241,
256 and 262. Their names are base0.T through base4.T. Eighteen requests
use these shared moduli: in particular later requests reuse the bases q
and q+1 rather than introducing a modulus for each exponent.

All five named T coordinates survive in the existing principal projection:

| Source name | Projected coordinate |
| --- | ---: |
| base0.T | 176 |
| base1.T | 186 |
| base2.T | 188 |
| base3.T | 198 |
| base4.T | 200 |

None of the source helper names at coordinates 269, 270, 286, 287, 292,
308, 309, 314, 315 or 175 survives there. Thus the accepted projection
already removes those product/square construction gates while retaining
the shared modulus. Explicitly fusing its quadratic definition does not
establish a new variable saving. The alternative u=n*r presentation gives
each quotient a helper of its own and sacrifices this sharing if applied
indiscriminately.

The exact local lemma remains available, including for differently shared
future sources. There is no current measured gain and no reason to rerun
the existing compiler solely for this rewrite. The shared-cap construction
remains the stronger active source-reduction lead.
