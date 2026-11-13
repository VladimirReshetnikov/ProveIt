# Independent source review: quotient from the 86 own-zero

The source extracts A0 from the 86 graph's own zero, rewrites it with the
signed first-field evaluation, and feeds that equality to the q-cubed
quotient/root fact. The definitions q=1+J*beta, Q=q³, M=Q*J*beta and the
natural pair align. Positive beta and J give positive b, the Y premise is
explicit, and the radicand is positive as one plus a natural product. No
root sign or 85 graph zero is assumed.

The checker pins the interfaces, replays author and independent dependency
receipts, and tests finite first-residual examples of both signs. These are
not asserted to be full graph zeros. This is source and finite review only;
Lean elaboration, witness maps, providers, external file binding and the iPRA
endpoint remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-86-ownzero-quotient-draft-independent/check.py > /tmp/ownzero-quotient86-independent.json
cmp /tmp/ownzero-quotient86-independent.json reviews/ordinary14-86-ownzero-quotient-draft-independent/result.json
```
