# Independent review: forced-positive natural 82-operation graph

The external zero-existence reduction in the [candidate packet](../../research/ordinary14-root74-natural-forced82/README.md) is sound under its stated assumptions, conditional on the reviewed 85- and 75-operation parent arguments. This review does not establish a Lean or iPRA theorem, formal port or PDF binding, or minimality.

The receipt independently compares every surviving graph row to the 85 graph after deleting precisely the three `x=n_x+1` nodes and substituting `n_x` for `x`. This is an exact structural argument for the claimed affine polynomial identity, over arbitrary integer ports and inputs. It also checks the particular graph rows used for the factors, exhausts the relevant residues modulo four, and runs a small negative-Pell control. The last control is not a proof of the unbounded negative-Pell lemma.

For the unbounded zero transfer, the other shifts and `beta>0` give `q>=2`, `X>=2`, `Y>=8`, and `k>0`, so the same negative-Pell lemma excludes `F0=-1` even when `r` can be zero. The modulo-four exclusions for `F1`, `Fa`, and `Fs` hold for arbitrary integer `f`, `y`, and `r`. A zero of the product-minus-one expression consequently forces those four factors to be `+1`. In the ordered integers, `F0=1` then forces `r>0`; `Fs=1` rules out `f=0` because `Delta>1` and `I²=Delta*(f²-1)`; and `Fa=1` rules out `y=0` because it would require `Delta` to divide 1. These arguments use decidable integer cases and explicit natural predecessor maps, but their formalization in iPRA is not supplied here. The reverse map increments the three coordinates. The stated `K0>=0` hypothesis is inherited from the earlier guard equivalence; the local zero transfer itself does not depend on it.

The 82-row graph count and degree 107 are supported by the candidate's separate checker and its authenticated fixed-port ray, conditional on the parent degree bound. This independent review did not independently rederive the port bytes or upper bound.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-root74-natural-forced82-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-root74-natural-forced82-independent/result.json
```
