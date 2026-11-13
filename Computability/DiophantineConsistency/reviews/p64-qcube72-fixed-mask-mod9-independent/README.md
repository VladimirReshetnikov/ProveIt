# Independent review of fixed-mask graph controls modulo 9

**PASS as a finite modular statement.** The no-Lean `check.py` pins the
72-row graph and current fixed radix/mask source definitions, independently
reconstructs the actual large integer beta, low mask and high mask, and
reduces them modulo 9. It reproduces `(beta,MC,high,MF)=(4,1,3,7)` modulo 9.
The reconstruction uses the finite little-endian radix recipes; it does not
independently rebuild the Lean provider ancestry.

The independent evaluator runs every graph row for both listed input
tuples and all 81 pairs of mask residues modulo 9. It reproduces 162 cases
with `A0=Na=1` and `M=W=Lt=output=0` modulo 9. With the actual fixed mask
residues, the first tuple has `q=0 (mod 9)` and the second `q=5 (mod 9)`.
In both cases `Y=U=0` and `H=Delta=3` modulo 9. The chosen coordinate
representatives are positive integers, but that fact alone does not lift the
modular solutions to positive integer graph zeros.

Thus the reduced graph equations modulo 9 admit both `3|q` and `3∤q` at
the actual fixed port residues. This does not establish that either type of
actual integer zero exists, prove the no-old-gamma hypothesis occurs, or
settle a reverse-existence implication or iPRA endpoint. No Lean theorem is
asserted and no Lean replay was performed.

Run:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-fixed-mask-mod9-independent/check.py
```
