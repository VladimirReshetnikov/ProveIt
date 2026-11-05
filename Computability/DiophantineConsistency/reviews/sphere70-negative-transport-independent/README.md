# Independent review: proposed sphere's negative transport branch

The pinned 71-row graph has `b=beta*J`, `q=b+1`, `C=q−F−alpha`, and `W=(K+w)*C+(q−F)−z*b`; its final rows implement `(P*Q)²+(U*W−1)²+Z²−2`. With `b≥2`, choose `F=2`, `alpha=b−1`, and `z=1`. Then `q−F=b−1=alpha`, so `C=0` and `W=(b−1)−b=−1`, independent of K and w. Positive beta, J, K and w make all these selected inputs positive; the checker also verifies the graph's recorded beta byte payload is at least 2, making `J=1` a concrete transport-only choice for that byte value.

At the **abstract** tuple `P=Q=U=Z=1`, `W=−1`, the existing 71 expression equals 4 while the proposed expression with `(U*W)²` in place of `(U*W−1)²` equals 0. The independent checker verified the pinned graph rows, affine identities, the tuple arithmetic and all 3,087 finite positive transport cases, and reran the author's checker with byte-identical output.

This does not show that the abstract tuple is simultaneously realizable by the complete graph at positive inputs. It proves neither a full positive zero nor failure of existential equivalence at the fixed Lean ports. The transport construction does not verify the other graph constraints; the fixed-byte observation is not a new Lean proof of serialized-port identity. No Lean process was run.

SHA-256: `check.py` `06d7a3c5ee2bf9179bede2a6d58ea7a2bfbe26eca3ff42bc4bf38472ab438cf9`; `result.json` `a2b2e21c0dc784bcc733424466991852b380866feeab41a06729844ccdca4781`.
