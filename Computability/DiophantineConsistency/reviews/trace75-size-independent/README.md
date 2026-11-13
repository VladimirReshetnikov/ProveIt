# Independent review: trace75 first-index and radix bounds

The accepted `Trace75Size.graph_rank_size` is an IΣ₁-model theorem for arbitrary natural ports `p` with `0<(p 0 : V)`, an all-positive `v : Fin 10 → V`, and a zero of the Lean trace75 `value75` at the same port casts and embedded tuple in `DiffRing V`. It concludes **only**

```
8*firstParam p v + 4 ≤ k v,     2*(q p v)^4 < c p v,
firstParam p v = X p v * (Y p v * Y p v).
```

The proof obtains one `n` from the earlier first-Pell theorem, passes its actual ordinate equality to the universal `first_index_ge_two` theorem for that same `n`, and uses monotonicity to bound `2*ycoord n` from below by the second ordinate. It then uses positive coordinates, `X=w*q`, `Y=q³*s`, and `c=k*Y+eta` to derive the radix bound. This packet does not prove an odd-main-index lower bound, index alignment, halt equivalence, trace74 guard, iPRA theorem or external JSON/payload binding.

`check.py` rehashes accepted source/copies, runner, Lean binary, recorded inputs, object and logs, and resolves the direct and selected inherited providers. Direct `Trace75Index` matches the independently reviewed object `6cc75eb28726516d4901542f26f083ecceeb682d459ff4a71022f3d88b1a3a34`; selected trace75 and generic Pell objects match recorded pins. `ArithmeticPellFirstNorm` is not directly pinned by this runner; its post-hoc first-resolved hash matches the earlier accepted `Trace75Pell` producer's direct pin. Exact paths, hashes and this boundary are in `check-output.txt`; no complete transitive/producer-time or package/dynamic ancestry audit was performed.

The accepted object is `2a536f3a3eb2129213dd4b30df564cff717068221c8e7b9b5e864475c29cf058`; inner Lean exit is 0, stderr is empty and its named report is exactly `[propext, Classical.choice, Quot.sound]`. The runner rejects coded errors/warnings and `sorryAx` but does not enforce a named axiom whitelist; the captured report was independently inspected. The terminal precedes final runner assertions, and no separately retained actual outer-exit receipt was found. No Lean replay was performed.
