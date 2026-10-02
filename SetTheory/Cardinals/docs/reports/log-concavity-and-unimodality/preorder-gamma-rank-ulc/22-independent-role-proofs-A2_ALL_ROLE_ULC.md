# Complete weighted two-attachment theorem

Both orientation branches are independently approved. Every preorder in the Gallai–Edmonds a=2 family, with core at most five vertices and arbitrary heterogeneous exterior populations, has a role-weighted support sequence that is ultra-log-concave with respect to its actual degree.

- Opposite attachment signs: the summaries H,T,W compress the exterior to at most two weighted vertices. All 494 structural templates are covered by the six-vertex theorem, elementary structural branches, and 56 seven-vertex rational certificates. See `A2_MIXED_ROLE_ULC.md` and `../weighted-preorder-a2-mixed-audit/AUDIT.md`.
- Equal attachment signs: 333 private-only templates compress to at most six vertices. The 257 shared-cloud templates use the exact moment formula in A,B,U,E and the cone parameterization U=xi+eta, E=2xi eta. All 257 exact rational identities are complete, including the final direct source225 certificate. See `A2_SAME_SIGN_MOMENT_CONE.md` and `../weighted-preorder-a2-same-audit/`.

The complete source catalog has 1,084 structural templates and its prior independent audit remains a dependency. The new arguments accommodate arbitrary independent positive tail/head activities and arbitrary finite cloud sizes, rather than only integer populations. Effective zero weights and missing clouds are handled by polynomial continuity; original lower-degree cases use the universal first-gap theorem with their own actual degree.

Reproduce the local exact checks with:

    python verify_a2_mixed.py
    python verify_a2_same_sign_cone.py

The separate auditors regenerated the structural coverage and did not rely on these producer-side receipts alone. This component note proves the a=2 branch; the general a=0/a=1 seven-vertex cases are now also complete in the final article and complete role ledger.
