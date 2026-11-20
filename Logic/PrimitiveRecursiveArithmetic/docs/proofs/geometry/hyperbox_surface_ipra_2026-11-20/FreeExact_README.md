# Exact unrestricted maxima

Load `Get["FreeExact.wl"]` and evaluate `HyperboxFreeExact[{1,1,2}]`.
The input is an ordered list of at least two positive exact real algebraic side lengths.
The resulting association gives the fixed-source farthest point from the origin and its distance, unrestricted maximizing endpoints and their distance, both squared lengths, and the exact strict-improvement Boolean. Reflect a fixed-source answer in the coordinates of any chosen upper endpoint to use a different corner.

The implementation uses exact polynomial optimization over every inequivalent pair of distinct facet charts. There is no antipodality constraint. A common facet can be dropped because even its largest chord is shorter than the distance between opposite box vertices. Different-axis chart pairs can both be reflected to lower facets. Opposite-facet pairs can be oriented lower to upper. Permuting axes of equal lengths removes duplicates.

For each simple word the developed facets give closed ridge gates. A gate must admit a parameter in the segment from target to source image. Its scalar inequalities have the form `a*t+b>=0`, including `0<=t<=1`. Zero slope imposes `b>=0`. For a lower-bound row `(a,b)` with `a>0` in any gate and upper-bound row `(c,d)` with `c<0` in the same or a later gate, ordered feasibility is exactly `a*d-b*c>=0`. Requiring this for all such pairs is sufficient by choosing the running largest lower bound. This eliminates all gate times and handles lines in gate hyperplanes, ties, and endpoints on several facets. If the word is visible, the variable being maximized cannot exceed its squared developed length. At the maximum over that chart these inequalities select the actual shortest distance.

Rectangles, hypercubes, boxes with one short side and all other sides equal, and prisms with equal base sides use the proved closed forms over the ranges stated in the paper. For base dimension at least five this covers every height at least the common base side. For example, the exact four-dimensional rod is returned immediately by `HyperboxFreeExact[{1,1,1,5}]`. Other dimensions and aspect ratios use exact real semialgebraic optimization. The number of words, polynomial sign conditions and variables grows rapidly; very large instances may be impractical. `FreeExactTests.wls` supplies smoke tests, including one that calls the general optimization machinery on a rectangle.

A Wolfram kernel was unavailable during preparation. The source and tests were inspected and their delimiters checked. The Wolfram programs were not run here.
