# Independent source review: pointwise 75↔78 model wrapper

The first branch invokes the proposed 75→78 map with the same integer ports,
model valuation, beta cast, positive beta and positive coordinates. The
reverse invokes the proposed 78→75 map at exactly those ports and valuation;
that map's own signature requires no additional positivity or port cast.
The theorem therefore states a pointwise comparison, not a changed-witness
existence map. Neither direction imports an extra K or mask bound.

The natural-port wrapper uses `P72Root.cast_port p 0` in the correct direction
for the beta cast and retains positive beta and coordinate assumptions. The
checker pins the source interfaces, independently replays both map review
receipts, and reproduces the author receipt.

From `Computability/DiophantineConsistency` run
`python3 -I -S -B reviews/ordinary14-78-75-model-equivalence-independent/check.py | cmp - reviews/ordinary14-78-75-model-equivalence-independent/observation.json`.
This is source/interface review only. The maps, wrapper, and tactics remain
unelaborated. Provider/Init coherence, model-halting or iPRA endpoint, and
physical-byte/PDF binding remain open. No Lean run was performed.
