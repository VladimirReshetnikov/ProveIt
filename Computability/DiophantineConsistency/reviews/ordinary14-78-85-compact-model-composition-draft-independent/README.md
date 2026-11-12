# Independent source review: compact 78/85 composition

The first source interface is an 84↔78 equivalence at natural ports. Reversing
it gives 78↔84, which composes in the stated direction with the compact
84↔85 equivalence. Both use the identical port tuple
`[beta,K,low,beta+high]`; beta positivity comes from the symbolic port-bound
interface, and K is arbitrary natural. All three graph-zero assertions use
all-positive fourteen-slot valuations.

The checker pins the component source interfaces and replays the author and
independently reviewed component receipts. This is source-interface review
only. The full chain remains unelaborated in Lean; provider compatibility,
connection to iPRA, concrete external-file binding and PDF semantics remain
open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-78-85-compact-model-composition-draft-independent/check.py > /tmp/compact-equiv7885-independent.json
cmp /tmp/compact-equiv7885-independent.json reviews/ordinary14-78-85-compact-model-composition-draft-independent/result.json
```
