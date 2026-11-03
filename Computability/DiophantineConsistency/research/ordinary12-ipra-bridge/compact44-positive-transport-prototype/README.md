# Positive shifted compact transport

For any IΣ₁ model and Σ₁-definable compact `X`, `CompactPositiveTransport.positive_shifted_transport` takes the symbolic compact `PackingInput`, a rank-like value `R` with `2*(590069*N)<R`, and the explicit rotation congruence

`2^(R−590069*N) mod (2^(590069*N)−1) = 2^(590069*s) mod (2^(590069*N)−1)`.

Writing `q=2^(590069*N)`, `w=2^(R−590069*N)`, `C=Cw 590069 N X` and `F=Fw 590069 K N s X`, it constructs `z>0` with `q*w=2^R` and `(K+w)*C = F + z*(q−1)`. The proof uses the quotient before the `+1` in the generic `zq` definition; this is the shifted convention used by the free-J carrier. Positivity follows from `w>q`, `C>0` and `F<q`. The calibration/congruence is an explicit hypothesis here and is not claimed as a consequence of this theorem alone.

The checked source SHA-256 is `6083435542f7bd89197e1af425937c22ce4ae5cca93740a3e9c20c495b79d9c5`. The bounded author check in `observations/attempt03` exited 0, printed `[propext, Classical.choice, Quot.sound]`, preserved direct dependency and companion guards, and produced `/tmp/compact44-positive-transport-author-0wa9eqmk/CompactPositiveTransport.olean` with SHA-256 `c80d2dc111f9cdc7415c64128726d616f09cfffac83a3959177876e04f80b8c1`. The earlier failed elaboration attempts and source snapshots are retained. This check inherits the compact rank provider ancestry, does not authenticate its transitive or dynamic closure, and is not a paired replay. It is not a graph-zero or iPRA theorem.
