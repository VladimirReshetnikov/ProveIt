# Independent source review: compact 78 ↔ 86 composition

The proposed composition uses the same symbolic port tuple `[beta, K, low, beta + high]` on both sides of the 85-graph interface. Its first component goes from the 78 graph to the 85 graph; its second goes from the 85 graph to the 86 graph. The first component supplies the fixed-beta port bounds, and the second uses their positive-beta component. The natural parameter `K` remains arbitrary. This is a source interface review; it does not establish Lean elaboration, an iPRA proof, or binding to the published equation.

Run `python3 -I -S -B check.py` and compare its output with `result.json`. The checker pins source and receipts and replays the author and both independent component checks. It does not run Lean.
