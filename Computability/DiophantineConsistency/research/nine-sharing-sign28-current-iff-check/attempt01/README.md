# Sign28 current-port iff: author-observed run

The runner reported `PASS sign28 current seed iff diagnostic`; author-observed outer session 59009 exited 0. Retained state SHA-256 is `5069e81055514352e39b50d2bf4aff5ce57aee038213b11ac9cef6a000b742b9` and author receipt SHA-256 is `867cef5cc386b0860b3a755d04bc73dc2b32e92af8e15019450bc78355535233`. This is an author-observed exit, not an independent replay.

The beta cast, pointwise iff and same-input existential iff each report `[propext, Classical.choice, Quot.sound]`; no warnings were emitted. The conclusions concern current-port symbolic seeds in IΣ₁ models; they do not yet establish source equivalence, an endpoint, a Lean degree bound, or external JSON/coefficient binding. The run uses the successful port-base observations from a producer whose overall run failed and retains inherited ancestry limitations.
