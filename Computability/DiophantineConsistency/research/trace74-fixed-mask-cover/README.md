# Fixed-mask cover for the trace74 guard investigation

Write `HP = MF - beta` for the positive high mask. For the retained fixed
coefficient payload, the exact integer checker establishes
`MC + HP > beta`. In fact, `HP >= 2^589953` while
`beta - MC < 2^220833`. It checks the candidate JSON hash and both the
compressed parent and raw hashes for all three payloads. The output records
only bit lengths and the comparison, not the enormous integers.

This inequality suggests a route from the *second* saturation no-carry
condition to the missing comparison `F <= MC*J`: if `q=beta*J+1`, `J>=1`,
`H=HP*J-1`, `F,H<q`, and `NoCarry(F,H)`, then the existing no-carry bound gives
`F+H<q`; mask cover gives `MC*J+H>=q-1`; hence `F<=MC*J`. These are
conditional arithmetic steps. They do not derive the no-carry condition, the
other saturation premises, or the guard from a 74 graph zero.

The payload check is external integer computation, not a Lean theorem or a
formal binding to symbolic BFS ports. It does not establish a graph zero or
an iPRA equivalence for trace74. An [independent review](../../reviews/trace74-fixed-mask-cover-independent/README.md)
rechecked the hashes and inequality. Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-fixed-mask-cover/check.py
```
