# Equivalence under the explicit G>w restriction

`DirectMainRestricted.exists_iff_restricted` proves in every IΣ₁ model and for arbitrary natural ports that positive XQ91-zero existence is equivalent to existence of a positive direct-draft zero with the additional condition `w<G`. The forward map is `G=gamma+w`; the reverse map is `gamma=G-w`, whose strict positivity follows from that condition. Both maps and their inverse relation are checked in Lean.

This does **not** prove that every direct-draft zero satisfies `w<G`, or that a zero with `G≤w` can be replaced by one satisfying it. Consequently it is not an unrestricted model-to-halt equivalence or an internal iPRA proof-existence theorem.

Attempt 01 failed due to a missing space in Lean syntax and is retained. Attempt 02 passed with no reported warnings; source SHA-256 is `325c6a956f8a5942b0d5861111d170e2a2b6fe9ab19815c42ec69a2dfb45bbbe` and output object is `3d60d8e204f2c3dd1c6afaaee485e3b269c0222b5b70761d7fd44f67db3df7ef`. The printed axiom report lists `propext`, `Classical.choice`, and `Quot.sound`. The forward, graph and XQ91 producer objects and selected 1,291-object union were pinned and rechecked. Package, dynamic, and source-to-object ancestry remain inherited rather than freshly rebuilt; resource samples and exact pins are in the receipt, and temporary paths may disappear.
