# Independent source review: residue 90 to 91 transport

The 91 literal and ordered residual source are exactly the 90 sources with the added `shift_gamma=n_gamma+1` and its use in the main root; all other rows and residual ordering `A0,A1,Fam,g72` match. Thus, for arbitrary signed ports and an arbitrary valuation, the 91 graph at v is the 90 graph at v with coordinate 12 increased by one. The proposed residual identities and whole-graph evaluation have this orientation.

The no-zero proof uses that forward map to carry a 91 zero to a 90 zero. For the converse it takes a 90 zero, obtains gamma>0 from the separate symbolic compact source chain, and lowers coordinate 12 by one; the proposed `raise_lower` then restores the original valuation. No f/y forcing is used by this gamma-only transport. K is an arbitrary standard natural, and the all-model gamma forcing and preceding source imports remain unelaborated.

The source explicitly assumes `PolynomialBridge` for the 91 graph; the pinned bridge API transfers that assumption through `SameNoZero`, and the native API then states the proposed iPRA comparison. The parent bridge is not constructed here. Neither compact fixed-kernel bytes, physical PDF semantics, providers nor a completed iPRA theorem follow from this source-only conditional composition. The author's receipt reproduces; no Lean was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue90-to91-model-independent/check.py | cmp - reviews/ordinary13-residue90-to91-model-independent/result.json
python3 -I -S -B research/ordinary13-residue90-to91-model-draft/check.py | cmp - research/ordinary13-residue90-to91-model-draft/receipt.json
```
