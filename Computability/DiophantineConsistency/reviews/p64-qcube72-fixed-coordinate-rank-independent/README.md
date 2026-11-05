# Independent review of the fixed-coordinate rank obstruction

The corrected [rank-obstruction packet](../../research/p64-qcube72-fixed-coordinate-rank-obstruction/README.md) was reviewed over standard integers. Its main claim fixes the ports and three values `J`, `k=eta+zeta`, and the mapped carrier gap `h`; it permits other old-witness coordinates to change. It is a necessary condition on that particular normalization, not a proof that the old graph has no zero or that the graphs have different existence behavior.

For a positive zero, transport gives `C=q−F−alpha>0`; positive `F,alpha` give `C≤q−2`, so in particular `q≥3`. Reducing the actual rank expression modulo `q` gives `R≡C+MC*J`. An old carrier satisfying the fixed-gap requirement has `U' gamma'=h+k−R'−1`, and `q | U'`, so its `C'` must be the unique representative

```
C' = (h+k−1−MC*J) mod q,     1≤C'≤q−2.
```

The extra `q | h` claim is also correct for standard integer 72 zeros. The main square equality gives `U | Dstar`, hence `q⁶ | Hh` because `q⁶ | U`. Since `a` is a multiple of `q³`, all common prime factors of `q` and `H=4a+3` are 3. If `3 | q`, then `H≡3 (mod 27)`, so `gcd(q⁶,H)=3`; otherwise that gcd is 1. Cancelling gives `q | h`. This reasoning uses integer prime divisibility and is not presented as a Lean or nonstandard-model theorem.

For the previously independently reviewed symbolic zero, the resulting required residue is 0, so no old zero at those same changed natural ports can reproduce its fixed `J,k,h`. Other `J`, `k`, or mapped `h` remain possible. The compact44 specialization only excludes two residue classes as a necessary condition; no claim establishes whether a compact44 zero violates or satisfies it.

The initial draft's narrower fixed-`C` rigidity omitted the need to fix `w`: transport gives `F'−F≡(w'−w)C (mod q−1)`. The corrected packet fixes both `C` and `w`, after which the claimed rigidity follows. Our checker includes the transport-only control `q=5`, `K0=1`, `C=1`, with `(F,alpha,w,z)=(1,3,4,1)` and `(2,2,5,1)`: both satisfy transport despite different F. This is not a full graph zero.

The read-only [checker](check.py) pins the corrected author packet, graph and compact-port sources; reproduces the author's finite result; and runs separate gcd, rank and changed-w transport controls. These finite checks support the audit but do not replace the universal divisibility argument above or prove a Lean theorem.

```
python3 -I -S -B path/to/p64-qcube72-fixed-coordinate-rank-independent/check.py
```

The deterministic result is frozen in `result.json`.
