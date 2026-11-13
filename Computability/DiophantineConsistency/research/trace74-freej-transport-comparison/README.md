# FreeJ transport versus the 74 C chart

`Compact44.FreeJFirstTransport.freej_first_factor_transport` uses a first scaled norm and its root magnitude to prove `Bn<Bp`, with

```
A = w+K0·q,  Bp = qA,  Bn = (F+alpha)A+Fq.
```

The positive FreeJ input `alpha` then implies `F+alpha<q`. Its root binding represents the signed transport register as `Bfree=(q−F−alpha)(w+K0q)−Fq`.

In the 74 chart the input C is independent and positive, while the synthetic old alpha is `q−F−C`; this synthetic value is not known to be positive. The actual 74 transport register is `B74=(K0+w)C−F`. Substituting `alpha=q−F−C` into the FreeJ expression gives

```
Bfree = C(w+K0q)−Fq,
Bfree−B74 = (q−1)(K0C−F).
```

Consequently the signed register and root-magnitude equations are different. Moreover, asserting positivity of the synthetic alpha is exactly asserting the sought strict 74 guard `F+C<q`. Thus the FreeJ theorem cannot be directly instantiated at that synthetic valuation without the missing guard, and its transport sign is not the sign of B74. The separately checked 74 carrier proof establishes `B74≥0`; in isolation that inequality does not imply the guard. For example q=32,F=1,C=32,K0=w=1 gives B74=63 and F+C=33>q. This scalar example does not satisfy or claim the full graph equations, scaled norm, root-magnitude premises, or fixed BFS ports. A different 74-specific use of the magnitude identity is not excluded.

The source-pinned `check.py` verifies the two source shapes and identity as a polynomial over the integers, with the five symbols q,F,C,K0,w treated as independent, and checks the scalar example. Run `python3 -I -S -B research/trace74-freej-transport-comparison/check.py` from `Computability/DiophantineConsistency`. Author exit 0; checker SHA-256 `d9d51644ec8d0dc92d5ccfba917c5d1a30b3be117fc95b91599298886efb9035`, stdout SHA-256 `9e97a29d6314b1ed7aea839328e292ac9b72bc46f72bdfe0d6156ed39e3fccef`, stderr empty. This is an external exact ring/source comparison, not a Lean binding between the two formalized charts or a proof about all graph zeros.

Independent [result audit](../../reviews/trace74-freej-transport-comparison-independent/README.md) passed, SHA-256 `5bfbf35f1426e2d742210ee495bbd6ec52da7f292903ef565e14e4c5c1e0fef3`; its rerun reproduced the output. Its scope remains a source-snippet and external arithmetic comparison, not a Lean chart binding.
