# Independent source review: J positivity for a natural-79 zero with w=0

The [source draft](../../research/ordinary14-natural79-zero-w-jpos-draft/README.md) proposes the correct conditional J-positivity argument under its displayed assumptions, relying on the still-unelaborated five-unit client. The source and its imports, casts, tactics and axiom reports have not been checked in Lean; this is not an iPRA theorem or physical equation binding.

At `J=w=0`, the receipt computes the entire guard dependency cone from the pinned 79 graph as an exact sparse integer polynomial, with arbitrary values in all other input and port slots. It obtains

```
guard = -(n_F+n_alpha+1)*K0-n_F.
```

Under the theorem's represented natural-model `K0` and natural-model inputs, every displayed factor is nonnegative, so the guard is at most zero. The cited proposed unit client puts the guard in the fourth position of its five-unit conjunction and would make its difference-ring evaluation one. Thus the hypotheses `J=0`, `w=0`, a graph zero and that representation contradict each other, without assuming beta or gamma positive and without assuming `K0>0`.

The `K0=0` boundary is essential: when additionally `n_F=0`, the guard is exactly zero. A strict-negative claim would be false, but nonpositivity still contradicts guard `=1`. The receipt exhausts 343 small nonnegative guard instances including this boundary; the exact graph cut, rather than those finite controls, supports the general argument.

The review checks the displayed source assumptions, representation and guard-unit conjunction position. It does not establish that `Natural79ConcreteUnits` elaborates or that the source's signed-pair-to-ring conversion, model order and cast tactics succeed. Establishing the main-norm divisibility contradiction, `w>0`, an iPRA endpoint, provider/axiom closure and physical-file/PDF association remains separate work. Both original and independent receipts reproduce.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-jpos-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-jpos-independent/result.json
```
