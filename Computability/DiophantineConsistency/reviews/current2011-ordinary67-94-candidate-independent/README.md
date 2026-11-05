# Independent review: current-port ordinary 67/94 candidate

The read-only checker exited 0. It matched the exact pinned 51-row prefix, complete 16-row tail and four port metadata records to the frozen inputs; checked topological order, all 67 live operations (37 multiplications, 17 additions and 13 subtractions), and all 14 witness and four port inputs; and verified all four compressed and uncompressed fixed-port payload hashes.

The checker establishes degree at most 94 independently of the pinned degree certificate by propagating syntactic degree bounds after the explicit main-norm cancellation `N1 = X² + 2*X*a*c + 2*gamma*H*(X+a*c) + gamma²*H² − H*c²` (degree at most 18). For the lower bound it evaluates the complete graph with every witness equal to `t` and the recorded fixed port integers reduced modulo 1,000,000,007; the coefficient of `t^94` is 495,675,807, nonzero. Thus the candidate with those fixed coefficient bytes has exact degree 94. This is external arithmetic evidence, not a Lean `totalDegree` theorem or a formal serialized-byte-to-Lean-port binding.

For the proposed forward map `i_new=Delta*i_old`, the prefix is unchanged because none of its 51 rows consumes `i`. The checker independently verifies, in a universal integer polynomial ring, `I_new²−Aaux=Delta*(1−S_old)` and `Na_new−U_old=Delta*(S_old−1)*(V²−y²)`. Thus under the **additional** condition `S_old=1` the new strong factor is one and the auxiliary values coincide. With positive original witnesses and beta, `Delta>0`, so the mapped `i` stays positive. The existing strong-norm fact and its model/provider provenance are separate; this packet is not a Lean forward-map theorem.

The reverse existence direction is unresolved in this packet: the candidate's equation does not by itself authorize dividing its `i` by Delta. Consequently the graph remains a candidate; no full same-zero equivalence, iPRA derivability or consistency claim follows from this audit. The maintained PDF is not bound or changed. No Lean process was run.

SHA-256: `check.py` `827789a306816bcd95a430d365bf05a5b96ca4a376ffc59cebfb1fd8b14d3206`; `result.json` `0d184fb14cb154499b669e822e9a7709d73e5d6e0d2191baa4bec2ea32d77cbd`.
