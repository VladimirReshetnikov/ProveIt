# First-carrier seed from positive compact transport

`CompactFirstTransportSeed.first_from_transport` takes a symbolic compact `PackingInput`, positive `sY,z`, the outer `SeedRelations` for its exact compact rank `R`, and the shifted transport equations `q*w=2^R` and `(K+w)*C=F+z*(q−1)`. Here `q=2^(590069*N)` and `C,F` are the represented sums of that same packing. It derives

`(q*K+2^R)*C = q*F+(q−1)*(q*z)`

and a positive first-carrier coordinate `r`, with the additive scaled-root identity of `CompactFirstSeed.positive_first_of_seed` instantiated at `b=q*z`. Both the required rank phase and the lower bound on `q−1` follow from the packing. The theorem does not assume a separate bound on `b`; it uses `z>0` and `q>0`. It does not itself construct the input transport, prove the literal graph zero, identify retained bytes, or prove an iPRA equivalence.

The checked source SHA-256 is `66dcb2b82e43b62f63ce315118a675e8853f8734d8d23924404b386606ab9a7c`. The bounded author check `observations/attempt02` exited 0, printed `[propext, Classical.choice, Quot.sound]`, left direct import and companion guards unchanged, and produced `/tmp/compact44-first-transport-seed-author-j55bnpa7/CompactFirstTransportSeed.olean` with SHA-256 `0361b27d675a978705be3e5a4ecda7191acf249e4e4625d7db3cff3182040ca5`. The first failed elaboration and exact source snapshot are retained. This single-author check inherits the prior compact/seed provider ancestry and does not authenticate the full transitive or dynamic closure; it is not a paired replay.
