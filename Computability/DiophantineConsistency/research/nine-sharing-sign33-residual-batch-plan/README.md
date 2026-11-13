# Sign33 residual and static-gate batch plan

This source-only inventory proposes a bounded path from the checked generic `seed_zero_iff_residuals` and the checked first q-square cut to the remaining 23 residual/static identities. It is not a Lean graph bridge, witness construction or iPRA endpoint. `check.py` reads the pinned external sign33 `seed.json`, records the 24 residuals in their exact order, their symbolic port dependencies and all full-tuple variable indices, and checks that 19 materialized cuts consist of 14 positive and 5 signed cuts; 5 norm equations are interleaved with them as shown below. Its output is an external inventory only, not a Lean certificate.

| Residual indices (zero-based) | Ordered rows | Port casts actually needed for natural-port targets |
| --- | --- | --- |
| 0–2 | q2, q3, X | β (p0) |
| 3–5 | Y, E, kY | none |
| 6–8 | ell, Delta, main_root | none |
| 9–11 | c2, Dc2, N1 | none |
| 12–14 | gap, tau, N0 | β (p0), MC (p2), MF (p3) |
| 15–17 | Nt, f2, cTminusR | K (p1), β (p0), MC (p2), MF (p3) |
| 18–20 | V, normalized_S, normalized_S2 | none |
| 21–23 | V2minusY2, Na, scaled_Ns | none |

The MF port is already `highPort+β` exactly once. All shown variable indices are zero-based `Fin 34` positions with distinguished input 0; the corresponding `Fin 33` witness index is one smaller. Materialized full-tuple positions are q2=15, q3=16, X=17, Y=18, E=19, kY=20, ell=21, Delta=22, main_root=23, c2=24, Dc2=25, gap=26, tau=27, f2=28, cTminusR=29, V=30, normalized_S=31, normalized_S2=32, and V2minusY2=33. The first four signed cuts gap/tau/cTminusR/V use positive orientation; V2minusY2 uses the negative orientation, so its natural coordinate represents y²−V².

A bounded implementation should first define a total 24-element residual interface as `firstResidual :: remainingResiduals` with an independently checked length; prove once, generically, that seed zero forces the indexed residual to vanish, using the existing list-membership theorem and no expanded numerals. Then generate explicit same-valuation ring identities from the frozen AST in the eight three-row batches above. Work over a full `v : Fin 34 → V` to avoid repeatedly reducing `Fin.cons`; use symbolic integer ports and cast them to model-natural representatives only in rows that mention them. Each batch must pin its source, exact input AST positions, provider objects and row-order checker, use bounded per-module resources and stop on the first failure. A final small client can assemble the 24 identities; no global `simp_all` over all residuals or duplication of large port numeral expansions is needed. The already checked first residual gives a model for a small direct identity, but it is not a proof of the remaining rows.

The static graph layer must independently reconstruct each materialized cut in chronological order and bind each row to the corresponding generated Lean residual; the five norm rows must be identified with the correct Carrier65 expressions. For the forward direction, 14 nonnegative cuts can use natural model expressions, while the five signed cuts use the separately checked source-zero Carrier65 representatives. The gap/tau/cT−rank/V/y²−V² expressions still need explicit ring graph-to-core identities, and `r` requires the checked bounded natural-subtraction casts rather than unrestricted subtraction. The reverse direction must replay the same fixed valuation and port casts through all rows, obtain all five original norms and invoke the source theorem; it cannot infer a source zero from the external AST comparison. Only after both directions are checked should the degree/normalization and Jones/iPRA clients be composed. These remain proof obligations, not completed results.

Pinned candidate JSON SHA-256 `a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75`; inventory checker `11bafab69512332c0ed04263a7a3274806aba2758c874e36c97d800241932c57`, result `95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8`. Run `python3 -I -S -B check.py`; no Lean run.

The [independent inventory audit](../../reviews/nine-sharing-sign33-residual-batch-plan-frontier-independent/README.md) checked all row orders, port dependencies and cut positions without replaying Lean.
