# Restricted three-product five-operation screen

`screen-five-three-products.py` searches the pinned 86-operation candidate JSON, SHA-256 `e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f`, for single-row replacement by five operations forming a signed sum of three products, `(x*y ± u*v) ± z*w`. Operands are earlier nodes, the 13 inputs, four symbolic fixed ports, and literals 0–4. It evaluates three deterministic samples modulo the prime `2305843009213693951` using seed `80281234`, considers each row whose removal could drop at least five live operations, and recounts the live output graph after replacement. A hash map of product signatures accelerates matching.

The saved output records 20 eligible target rows and no candidate with fewer than 86 live operations. Reproduce from the repository root:

```sh
python3 Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/screen-five-three-products.py
```

This is a restricted modular screen, not exhaustive search or a minimality proof. Product intermediates with signatures equal to an earlier node are excluded; recomputing such a node can affect liveness, so those cases are not covered. Three-sample signature collisions may produce false matches or exclude cases, and only the indicated five-operation shapes and one-row substitutions are searched. Even a reported match would require exact integer-polynomial verification and a Lean binding, including both directions of the relevant zero-set equivalence. The complete unoptimized run took substantial CPU time and may take many minutes to reproduce.
