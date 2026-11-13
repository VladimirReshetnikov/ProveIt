# Uncompiled forward five-norm assembly

The terminal-agreement provider mentioned as pending below has since been
[checked and independently audited](../nine-sharing-norm38-reference-terminals-check/README.md).
These two forward sources themselves remain uncompiled; their guarded
combined provider route and elaboration have not yet been established.

`Norm38ForwardFiveNorms.lean` SHA-256 `d3e4b62d337dab008f2b4b4788178de6a9af8058b756b025ff505e05230dfd4c` adapts the independently source-reviewed `forward_fiveNorms` portion of the forward bridge draft to the split provider names. It assumes the five original Carrier65 unit norms at the positively shifted input and proposes the five static norm targets for the generated witness. It uses the checked forward-gate and prefix theorems, the six-field conjunction, the exact identity `Z = delta * strong`, and the proposed static-terminal-agreement theorem. No delta division or cancellation is needed.

This is **uncompiled**; the terminal-agreement provider is itself not yet checked. The proof scripts, rewrites under the generated-prefix function, exact provider routes and requested axiom report remain unverified. It does not show that a source zero provides the original norms, prove a complete source-to-seed implication, or yield an iPRA endpoint. A guarded runner should be constructed only after every directly imported provider exists with captured source/object/log/guard records; a no-Lean source review is appropriate meanwhile.

`Norm38SourceToSeed.lean` SHA-256 `9b1a089b2d84bdea914aa629230fec9dc06d704baac1e2a2d13cf7948b593363` further adapts the independently source-reviewed source-zero-to-seed direction: it assumes the four model port casts, positive first port and a zero of the original `expressionAt p` on shifted natural inputs; it invokes the model norm theorem, checked forward gate construction, this proposed five-norm theorem and checked static-to-seed implication. This second source is also uncompiled. Neither source has a runner yet because the terminal-agreement provider is pending; no forward bridge or iPRA endpoint is asserted.
