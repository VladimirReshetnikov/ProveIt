# Independent source review: natural-79 main norm and signed quotient

The [source proposal](../../research/ordinary14-natural79-zero-w-main-norm-draft/README.md) states a mathematically appropriate route from the proposed main-factor unit at `w=0` to a signed quotient. Its assumptions, literal atom cuts and both root signs have been checked at source level; the statements and their imported unit/model lemmas are unelaborated and do not establish an iPRA theorem.

The independent receipt computes exact sparse-polynomial cuts from the pinned 79 DAG with `w=0`: the literal atoms have `a=Y`, `c=(n_eta+1)+Y*((n_eta+1)+(n_zeta+1))`, `U=Y*q²`, and `Delta=Y²+4Y+3`, with `q=1+J*beta` and `Y=q³*(n_s+1)`. The formal source expresses the beta port through an explicit model embedding; K0, MC and MF do not appear in those atom cuts. The main-unit conclusion is the second conjunct of the proposed five-unit theorem and its pattern has the correct form `1+Dstar²-U²*(1+Delta*c²)`. It follows algebraically that `Dstar²=U²*N`, conditional on the unelaborated unit and evaluation rewrites.

The cited `ReducedNormSigned.natural_magnitude_square` source supplies a model-natural magnitude `z` and either `Dstar=ι z` or `Dstar=-ι z`; the cited model `scaled_quotient` source requires `U>0` and `z²=U²*N`, and yields `z=U*t`, `t²=N`. Taking `d=ι t` in the first case and `d=-ι t` in the second gives the proposed signed quotient without assuming a positive root or using standard-natural prime factorization. The source's displayed quotient theorem additionally assumes represented beta, `beta>0`, `J>0`, the graph zero and `w=0`; the preceding norm theorem does not assume beta or J positive. Its proof of positive scale, embedding injectivity, casts, source-pattern rewrites and both branches still need Lean elaboration.

This review checks mathematical/source signatures and exact atom cuts; it does not prove that the proposed calls or tactics type-check. The literal main-root divisibility cut, positive-divisor contradiction, positive-w zero transfer, provider and axiom closure, iPRA endpoint and physical-file/PDF association remain separate. Both original and independent receipts reproduce.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-main-norm-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-main-norm-independent/result.json
```
