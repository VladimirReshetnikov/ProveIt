# Independent direct-formula check of the free-index zero

The [author packet](../../research/p64-free-strong-index-full-zero/README.md)
specifies a positive zero of the 75-operation graph obtained by replacing the
76Y gate `I=i*c²` with an independent positive `I`. The calculation below
independently confirms that claim at the packet's explicitly defined natural
ports. Here `I=36480<c²`, so the direct inverse `i=I/c²` fails for this
particular zero.

[`check.py`](check.py) reconstructs all three Pell pairs by a norm-one
bitwise doubling algorithm, separately computes the modular inverse by the
extended Euclidean algorithm, and evaluates the residuals using direct
closed formulas rather than the author's gate interpreter. It obtains

```
A1=Na=1,   M=W=Lt=0,   output=0.
```

It then independently evaluates the 75 retained rows of the pinned graph
and checks those results agree with the closed formulas. All witness and port
signs, exact divisions, and the digest of the large port `MC` and selected
witnesses match the author's frozen result. The port `MC` is 165,184 bits;
its exact formula and digest are in the author packet and no large decimal
expansion is needed. Pell operands are bounded at 400,000 bits in this check.

This is an external exact integer verification of a **full zero of the
modified graph at the specified ports**. It does not show that the original
76Y graph has no different zero at those ports, does not establish anything
about the fixed compact44 port tuple, and is not a Lean theorem or iPRA
proof. No Lean process was run.

The [review result](result.json) pins the author script, author result and
76Y graph and records the verified residuals. Reproduce it with:

```sh
nice -n 19 ionice -c 3 timeout 60s python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-free-strong-index-full-zero-independent/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `0990d54fb52129989080cffdb9120b9d5388afb40ee7f86e6f0a648c89821ac0` |
| `result.json` | `944e6d08d53ef037443689f437c86c370f605279e15190edf742e6f2b753ad0b` |
