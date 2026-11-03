# Concrete symbolic port projections

`CompactSymbolicPortProjections.portsInt K` is the integer-valued port vector obtained from `CompactSymbolicPorts.ports CompactFixedBeta.betaNat K lowNat highNat`. In every IΣ₁ model, the four pointwise theorems prove in its difference ring:

- `beta K N`: the first port times `rep 590069 N` equals the embedding of `2^(590069*N)−1`.
- `kernel K`: the second port is the embedding of `K`.
- `low K`: the third port is the embedding of the compact symbolic low mask.
- `high K`: the fourth port is the embedding of the compact symbolic high mask plus `2^590069−1`; the shift is applied once.

The proof rewrites the port vector using the generic projection lemmas before specializing its values, so it does not normalize the large finite masks or beta numeral. These are symbolic port identities; they do not identify the symbolic constants with retained equation bytes or by themselves establish an iPRA theorem.

The checked source SHA-256 is `9680ad7c1f3113828170af63b8de3c29ff223683af0de07400f00bcb4ff2639e`. The bounded single-author check `observations/attempt02` exited 0, printed `[propext, Classical.choice, Quot.sound]` for each named theorem, preserved direct dependency and companion guards, and produced `/tmp/compact44-symbolic-port-projections-author-mb0n5o8o/CompactSymbolicPortProjections.olean` with SHA-256 `2406be5d31e04b0677b9f31f4a9ccd3f71cb8f48d9f0b590958bc7686df98616`. The receipt SHA-256 is `6576cae6f827daa4cec18228ffdb4488a5b53bf3a1c6a613bdd4342a0d55ade1`. The first attempt exceeded the 3 GB interpreter cap before the generic rewrite; its failed source and log are retained. This author-side check inherits provider/package ancestry and is not a full transitive/dynamic audit or paired replay.
