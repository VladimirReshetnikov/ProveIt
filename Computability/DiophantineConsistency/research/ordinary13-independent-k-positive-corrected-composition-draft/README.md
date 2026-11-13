# Independent-k positive-coordinate composition with rank-orientation alternative

This isolated source-only composition points the existing [child k-positivity composition](../ordinary13-independent-k-positive-composition-draft/README.md) to the [separate rank-orientation alternative](../ordinary13-independent-k-rank-orientation-repair/README.md). The entire source delta consists of that imported module and its namespace references, plus the composition's own namespace and axiom-query names. The original composition and rank sources remain unchanged. Its intended statement is that an actual zero of the exact fixed compact child has positive independent k; no eta≤k statement follows.

The rank alternative replaces a likely reversed `linear_combination` orientation, but neither the corrected helper nor this composition has been elaborated. The checker verifies the exact delta, the module-to-file and namespace declaration names, all three referenced rank declarations, and both prior receipts. It does not check Lean imports, tactics, instances or source/provider compatibility. The conditional graph unit extraction, compact tuple casts, first/main norm bindings, model-rank argument and every transitive provider are still unverified. No axiom set, full zero-map, PDF binding or iPRA endpoint is claimed.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-independent-k-positive-corrected-composition-draft/check.py | cmp - research/ordinary13-independent-k-positive-corrected-composition-draft/receipt.json
```
