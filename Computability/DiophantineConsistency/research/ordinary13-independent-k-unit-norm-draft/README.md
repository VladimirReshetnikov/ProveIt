# Independent-k candidate: proposed unit factors and signed norms

This packet generates a fresh Lean source literal for the exact [84-row independent-k candidate](../ordinary13-eta-zeta84-independent-k-candidate/README.md) and mechanically adapts the eta/zeta-natural unit/norm source to that literal. It is an **unelaborated source proposal**, not a Lean theorem, provider or axiom replay, k-positivity proof, unconditional zero map, or iPRA endpoint. It has no dependency on a supposed relation k=eta+zeta.

`IndependentKUnitGraph.lean.src` transcribes all 84 operations, 13 natural witness slots, and four signed integer ports. Slot 9 is `n_eta`; slot 10 is `n_k`, and the exported `k` field is exactly `n_k`. In particular the literal contains no old `kbase=eta+zeta` operation. The other exported fields preserve the original first/main/auxiliary/strong residual and factor interfaces. The source generator pins the candidate JSON by SHA-256, verifies unique row names, and reproduces the literal byte for byte.

`IndependentKUnitBridge.lean.src` is an exact import/namespace/comment adaptation of the pinned parent bridge. Its proposed `factor_units` takes an actual child `InternalZero` hypothesis and concludes that each of four signed factors is +1, using the generic first-factor mod-four exclusion and the existing `FreeJ13` main, auxiliary and strong exclusions. Proposed `residuals_zero` and `signed_norms` then supply the child graph's four difference-ring residual and norm identities. Ports remain arbitrary integers; no compact-port representation, positive beta, positive k, eta bound or root orientation is assumed. The field k is now the independent child slot, so the parent bridge cannot itself be substituted for this module.

The checker independently builds ordered expression trees from the child rows and compares all four factor patterns, the output-product tree, and the parent-to-child row replacement exactly. It exhausts 1,024 values for the first-pattern residue check modulo four, and checks 300 complete graph evaluations at varied natural witnesses and signed ports. It also verifies source signatures and the exact namespace adaptation. These checks support the transcription and finite identity only. They do **not** prove the factor-extraction theorem in Lean, establish arbitrary-model soundness, check `rfl` elaboration, resolve transitive imports/providers, or supply compiled axiom information. The compact model casts, graph-specific J/X positivity, rank window, parent polynomial bridge, fixed tuple and PDF connection remain separate obligations.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-independent-k-unit-norm-draft/check.py | cmp - research/ordinary13-independent-k-unit-norm-draft/receipt.json
```
