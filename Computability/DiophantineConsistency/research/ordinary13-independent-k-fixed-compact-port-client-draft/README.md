# Fixed compact ports for the independent-k draft

`IndependentKFixedCompactPorts.lean.src` proposes a source-only binding of the exact child ports to the existing first-rank contradiction. It defines the natural tuple as `C44Short15Facts.c44`, and the child integer tuple by casting each component to ℤ. In the pinned source its components are, in order,

```text
betaNat, paramKernel rho, lowNat, betaNat + highNat.
```

The fourth component includes beta once. The source proposes definitional equality with `CompactSymbolicModelIff.p`, and separately proposes the signed-model cast of each of the four integer ports using `P72Root.cast_port`. The byte recipes, external files and displayed equation are not identified here.

The `bounds` declaration applies the existing `C44Short15Facts.port_bounds` and `K_pos` source interfaces at the chosen kernel. Its intended conclusion in an IΣ₁ model is positive beta and K0, `MC<beta`, and `MF<2*beta`. This relies on the imported retained sources and their transitive providers; no source or object was compiled in this packet. The fixed kernel choice is essential to the K0 conclusion.

`child_J_positive` proposes the exact-child J argument at the same integer tuple using `IndependentKJPositiveDraft.J_positive`. `zero_k_fact_cut` specializes the repaired `IndependentKFirstRankDiscreteDraft.zero_k_impossible` to the compact ports and the child's J, F, alpha, s, r, eta and gamma slots. It supplies the four port bounds and natural shifted positivity, while leaving the zero-k first norm, represented rank, Y factorization, main root and main norm as **explicit hypotheses**. The conditional client has no claim that an actual child zero supplies those hypotheses. It also retains J positivity explicitly; the separate `child_J_positive` declaration can provide it once the actual zero and provider obligations are established.

The `#print axioms` commands are requests for a later build, not evidence of outputs. Lean elaboration, cast and definitional-equality checks, fixed-port model provider ancestry, actual child graph extraction, full parent-child zero map and the iPRA endpoint all remain open. The checker only pins and inspects source definitions, witness/port indices and the conditional call.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-independent-k-fixed-compact-port-client-draft/check.py | cmp - research/ordinary13-independent-k-fixed-compact-port-client-draft/receipt.json
```
