# Uncompiled five-norm assembly draft

`Norm38FiveNorms.lean` SHA-256 `659df3272bc175cad9a3a461d01c52cc3d10a6375f16c351a0e6093a28f383d2` isolates the five-norm half of the assembly that timed out. Given the existing IΣ₁-model and all four port-cast assumptions, it proposes extracting residual slots 11, 16, 17, 27 and 28 from `each_slot_zero`, rewriting them using the separately checked slot identities, and assembling `fiveNorms` in N0/N1/Na/Nt/scaled_Ns order. The norm residuals require no delta cancellation.

Independent source review passed at `reviews/nine-sharing-norm38-five-norms-independent/`; no Lean run has occurred for this draft. Its imported `Norm38EachSlot` remains a pending diagnostic; the other three imports are among the individually checked partial-run objects. A future compile needs a guarded provider chain for both. No gatesHold proof, source-to-static reference, reverse construction or iPRA endpoint is implied.
