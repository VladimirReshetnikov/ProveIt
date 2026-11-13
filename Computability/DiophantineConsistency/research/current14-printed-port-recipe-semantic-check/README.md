# External check of the four printed Carrier65 port recipes

The four integers obtained by the restricted interpretation below agree exactly with independent evaluations of the pinned historical Lean **source recipes** for `linePorts` and with the four compressed coefficient payloads of the displayed Carrier65 graph. The check reconstructs K from the page's decimal seed and tile formulas; it does not assume the printed tile order or the equality of K and its reference value.

This is a finite Python/source comparison. It is **not** a TeX parser or verified semantics for TeX, a Lean evaluation, an authenticated re-elaboration of the historical endpoint, or a PDF interpretation. The receipt assumes the human-readable formula-to-Python interpretation described here, the pinned source definitions and the recorded historical theorems relating the named kernel recipe to `lineK`. Those source and provider limitations remain separate from equality of the computed integers.

## What is evaluated

`printed-recipes.texfrag` is an exact snapshot of the page section from “The four fixed integers” through the action decoder; the checker requires that exact section in the pinned `equation.tex`. It extracts and concatenates all 12 decimal lines from the page, verifying that no non-decimal material other than the specified formatting remains in that seed block. The result has 715 digits.

The Python code manually implements the printed formulas. It decodes all 430 actions using the stated 636-bit mask, cumulative discovery and mixed-radix products, base-16 flags, and modular target rule. It evaluates the two target sets and all nine indexed tile-table cases. It checks there are exactly 942 distinct assigned indices and the printed first target. It then computes each selector weight and evaluates the printed floor-based rank formula for all 941 non-start indices. It verifies that the 942 ranks form a permutation, then independently compares the ordered `(index, weight)` rows with all 941 rows in the pinned Lean physical-order certificate and compares the Start tuple with the source definition.

For the printed `K`, the script expands the finite geometric sums in `2*Lambda*Phi(1/rho)` into integer powers of rho and evaluates them exactly. Every resulting exponent is nonnegative, making the rational cancellation explicit for this instance. It independently evaluates the pinned `KernelRecipe.lean` using its parsed physical-order rows and its four parsed control-sum signatures. The two K integers agree exactly; the source's `rawWord_recipe`, together with the separately recorded `lineK_eq`, is the historical source route to line port 1, not a new Lean proof in this packet.

For beta, mu and omega, the script separately evaluates the printed finite sums and the `CurrentMaskData2011` source representation: beta as `rho^2011−1`, the low mask by its indexed support, and the high mask as the little-endian radix digit list plus beta. It checks the relevant source text and computes the two routes independently; all four displayed ports are positive. The historical `linePorts` source is checked for the order `(beta, lineK, lowPort, highPort+beta)` and its `linePorts_recipes` declaration. No source theorem is replaced with a Python equality claim.

Finally the four computed integers are compared byte-for-byte against the gzip payloads referenced by the pinned displayed graph, with metadata, raw/gzip hashes, lengths and bit lengths verified. The checked binary sizes are 94,517 bits for beta and mu, 94,941 for K, and 94,518 for omega. Their big-endian SHA-256 values are in `receipt.json`; those hashes identify these exact computed bytes, while their interpretation as Lean objects depends on the historical source/provider evidence.

## Boundary of the check

The snapshot and manual evaluator do not prove that arbitrary TeX has the meaning assigned by this code; in particular, TeX macro expansion and rendered glyphs are not interpreted. The tile/action and formula translations require mathematical review, despite the exact source anchoring and independent source-data comparisons. `equation.pdf` is not parsed or rendered here. The historical `lineK_eq`, `rawWord_recipe`, `linePorts_recipes` and quoted-iPRA endpoint are referenced by pinned sources and prior records, not rerun; their compiled-object provenance and the incomplete coherent replay remain as previously documented. A formal page-byte theorem would still need a specified faithful restricted parser, checked numeric recipe semantics and a page/byte association.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/current14-printed-port-recipe-semantic-check/check.py | cmp - research/current14-printed-port-recipe-semantic-check/receipt.json
```

No Lean, build, staging, axiom report or model transfer was performed.
