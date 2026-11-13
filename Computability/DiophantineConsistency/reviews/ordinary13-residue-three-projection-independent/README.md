# Independent source review: q divides 3X projection

The signed divisibility certificates have the correct signs. Substitute `k=R+1+4XY²w` and `Y²=U*q*s` into the explicit oriented main balance. The free-ring identity in the draft gives `H*X*(Y*q)=U*witness`, with the displayed possibly signed witness. Since `U=(Y*q)*q`, and q>0, s>0 and `Y=q³s` make `Y*q>0`, cancellation gives signed `q | H*X`.

After substituting `H=3+4Y(X+1)` and `Y=q³s`, the second exact witness subtracts `4q²s(X+1)X` from the signed quotient and gives signed `q | 3X`. The pinned `natural_dvd_of_signed` interface then reflects that result to model naturals. The positive cancellation and both free-ring certificates were independently checked. Neither Bézout nor coprimality is assumed; the conclusion is `q | 3X`, not `q | X`.

The exact-index decomposition, oriented residue-adjusted main balance, q/s positivity, q³ scale, graph/port bindings and their providers remain explicit premises or separate source obligations. The client is not a power-recovery or iPRA endpoint. Its receipt reproduces; no Lean proof or axiom report was executed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue-three-projection-independent/check.py | cmp - reviews/ordinary13-residue-three-projection-independent/result.json
python3 -I -S -B research/ordinary13-residue-three-projection-model-draft/check.py | cmp - research/ordinary13-residue-three-projection-model-draft/receipt.json
```
