# A full zero after freeing the strong index

The 76-operation q-cube graph has the gate `I := i*c²`, with `i` a positive witness. Consider the 75-operation graph obtained by deleting that gate and taking `I` as an independent positive witness. The exact calculation here gives a **full positive zero of that modified graph at explicitly defined natural ports**, with `c² ∤ I`. Therefore the simple pointwise inverse `i := I/c²` cannot work for all zeros, even when every other graph equation is satisfied.

This does **not** show that the original graph has no zero at these ports. It does not rule out a different original witness, a different proof of existence equivalence, or an equivalence restricted to the compact44 ports. It is an external exact integer calculation, not a Lean theorem or an internal iPRA proof.

## Exact finite specification

For an integer `d`, write `(x,y)^e_d = (X,Y)` for exponentiation using `(x,y)(u,v) = (xu+d yv, xv+yu)` and identity `(1,0)`. All definitions below are exact integers; no floating-point approximations are used. Put

```
P = 4374; U = 729; H = 759; a = 189; n = 191; D = 36480
(t,k)   = (8749, 2)^11720_(P(P+1))
(g,c)   = (191, 1)^19259_D
(x,y)   = (D, 1)^561_(D²−1)
I = D; V = x / D; L = (c+V) / n²
A = U(g−6−a c) / H; B = k−1+A
gamma = least nonnegative residue of (B+L) U⁻¹ modulo c
R = B−U gamma; T = (R+L)/c
```

The divisions are exact, the modular inverse exists, and `gamma > 0`; the checker verifies these claims before interpreting the graph. The four ports in their graph order are **`(beta, K0, MC, MF) = (2, 3, R−40, 0)`**. The modified graph's fourteen positive witness inputs are

```
(J,F,alpha,z,f,I,T,s,w,t,eta,zeta,y,gamma)
= (1,1,1,2,191,D,T,1,2,t,c−27k,28k−c,y,gamma).
```

In particular, `R−40` is a 165184-bit natural number, specified exactly by the formulas above; its unsigned big-endian SHA-256 is recorded in `result.json`. The checker finds `T=1`, `I=36480`, and `c²>I`.

The script interprets every retained gate from the pinned `p64-qcube76-independent-y-candidate/graph.json`, omitting exactly `['I', '*', 'i', 'c2']` and supplying `I` as a positive input. It independently checks all port and witness signs, exact divisions, and the resulting values `A0=Na=1` and `M=W=Lt=polynomial=0`. The largest input or gate value has 330403 bits; no decimal expansion is required.

Run from any directory:

```
python3 -I -S -B path/to/p64-free-strong-index-full-zero/check.py
```

The output is frozen in `result.json`, including the pinned graph and script hashes. The calculation is deterministic and is guarded against Python optimization and graph changes.
