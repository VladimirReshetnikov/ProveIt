# Independent review of the 13/88 exact eta fold

The 88-operation graph has exactly the same output polynomial as the pinned 89-operation natural parent for every input and every port tuple. The parent computes `k=shift_eta+(n_zeta+1)` and `r0=(k-R)-1`; the child computes `kbase=shift_eta+n_zeta`, `k=kbase+1` and `r0=kbase-R`. Both values agree over every commutative ring. The deleted intermediate nodes are used only at these respective locations, all other named nodes have identical operations and operands, and the child graph is topological and fully live. Induction through the DAG establishes pointwise output equality, not merely a zero-set equivalence.

The compact-port degree 56 and all standard-zero/model provenance limitations are inherited from the independently reviewed parent. In particular gamma forcing and parent calibration are standard-integer arguments; the model transfer, port casts, Lean identity and iPRA endpoint are unelaborated. The compact tuple is not the current-2011 PDF tuple. The author's receipt reproduces; no Lean was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-natural-residue-eta-fold88-independent/check.py | cmp - reviews/ordinary13-natural-residue-eta-fold88-independent/result.json
python3 -I -S -B research/ordinary13-natural-residue-eta-fold88-degree56/check.py | cmp - research/ordinary13-natural-residue-eta-fold88-degree56/receipt.json
```
