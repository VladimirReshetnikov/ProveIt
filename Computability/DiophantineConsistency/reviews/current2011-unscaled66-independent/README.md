# Independent audit: current2011 unscaled 66-row graph

The read-only `check.py` exited 0 and produced `result.json`. It independently checked the frozen parent/candidate graph hashes, shared 51-row prefix, exact remaining arithmetic rows, topological validity and backward liveness. All 66 candidate operations and all 14 witness and four integer-port inputs are live: 38 multiplications, 16 additions, and 12 subtractions. Its abstract-cut integer-polynomial calculation proves the exact identity

`parent65 = Delta * candidate66`.

Here `Delta = a² + 4a + 3 = (a+1)(a+3)`. For the recorded strictly positive beta and strictly positive integer witnesses, `q = beta*J+1`, `Y = s*q³`, `X = w*q`, and `a = (X+1)*Y` are positive, so Delta is strictly positive. Thus the two graphs have exactly the same zeros **on that positive-witness domain**. The factor identity holds over all integers, but cancellation cannot be claimed for all integer assignments because Delta can vanish when `a = -1` or `-3`.

The exact total-degree check is independent of the 106 certificate's leading forms. A syntactic upper bound, tightened for the one required cancellation, gives 138. Specifically, with `H = 4a+3` and `Delta = a²+H`, the checked main norm has the expansion

`N1 = X² + 2*X*a*c + 2*gamma*H*(X+a*c) + gamma²*H² - H*c²`,

whose term degrees are at most 18; propagating this bound through the literal graph gives the upper bound 138. For a lower bound the checker substitutes `t` for **each** of the 14 witnesses, interprets all four recorded fixed-port bytes as their nonnegative integers, and evaluates the full graph as a univariate polynomial modulo 1,000,000,007. The coefficient of `t^138` is 47,829,043 modulo that prime. It is nonzero, so the specialized integer polynomial has degree at least 138. Together these prove exact degree 138 for those recorded fixed integers. The port files' compressed and uncompressed hashes and lengths are checked.

Scope: this is an external exact graph/degree audit and does not establish a Lean theorem, an internal iPRA derivation, a fresh provider rebuild, or a machine proof that the fixed port bytes equal an independently defined Lean tuple or the PDF. The identity is with the pinned parent graph; any theorem about that parent retains its own assumptions and provenance. No Lean process was run.

SHA-256: `check.py` `3711076090091ca56e263c3cddcd296211c07f21c89217bff355a5674b0d518f`; `result.json` `bd00331300777a1c33327ae4d42d9d9376029fb1338c5ef9f87cc65879282d21`.
