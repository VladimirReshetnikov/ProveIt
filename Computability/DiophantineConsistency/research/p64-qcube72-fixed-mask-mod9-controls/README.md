# Two fixed-port 72-graph solutions modulo 9

The complete 72-gate graph has solutions **modulo 9** both when `3|q` and
when `3∤q`, using the actual fixed compact beta and mask port residues. These
are congruence solutions only: neither is asserted to be an integer graph zero,
and neither establishes the existence or absence of an actual zero with
`3|q`. They show that the graph equations reduced modulo 9 alone cannot decide
that condition.

The pinned fixed-port definitions give

```
beta mod 9 = 4,     lowNat mod 9 = 1,
highNat mod 9 = 3,  (beta+highNat) mod 9 = 7.
```

The checker reconstructs the exact low/high digit definitions modulo 9: it
uses the 985-position low support, the 8,807 high digits, and base
`2^67≡2 (mod 9)`. It does not expand the large natural constants. The fixed
mask reconstruction and its source definitions were also independently
checked in the [fixed-mask gcd review](../../reviews/p64-qcube72-fixed-mask-gcd-independent/README.md).

For both rows take positive coordinate representatives

```
F=z=w=t=f=i=T=y=h=1, eta=3, zeta=1.
```

The remaining parameters are

| Case | K | J | alpha | s | q mod 9 |
| --- | --- | --- | --- | --- | --- |
| `3|q` | 8 | 2 | 7 | 1 | 0 |
| `3∤q` | 4 | 1 | 3 | 9 | 5 |

The two rows use `MC≡1` and `MF≡7` from the actual masks. In each case
`Y≡U≡0` and `H≡Delta≡3 (mod 9)`. Direct evaluation of all 72 graph
operations yields

```
A0≡1, Na≡1, M≡W≡Lt≡0, output≡0 (mod 9).
```

The same residual values hold for **every** pair of mask residues modulo 9;
the checker verifies all 162 combinations. In the first row `q≡0`; in the
second `q≡5`. Even though the displayed coordinate representatives are
positive, lifting a modular solution to a full integer zero is a separate,
unsolved problem. The fixed-port `3|q` condition remains an explicit
hypothesis in the checked [same-witness no-gamma theorem](../p64-qcube72-divisible-q-no-old-gamma-draft/README.md).

Run `python3 -I -S -B check.py`; [result.json](result.json) retains the
output and pinned source hashes. This is an external finite computation,
not a Lean theorem or a reverse-equivalence counterexample.
