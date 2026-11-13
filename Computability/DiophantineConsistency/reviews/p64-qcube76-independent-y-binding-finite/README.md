# Finite review of independent-`y` binding interfaces

[`check.py`](check.py) pins both graph JSON files and the unchecked Lean
binding draft. It independently evaluates the graphs over exact integers on
600 deterministic positive parent valuations. For each it compares the
explicit `oldV` formula with the 77 graph's internal `V` gate, then evaluates
the 76Y graph with coordinate `y=V+e` and again with its negative. All five
residuals and the output agree in both comparisons. Of the 600 old signed
roots, 38 were negative and 562 positive; none was zero.

The file also checks a small transport-zero example. Give **every** witness
in the 77 graph the value 1 and set the four ports to

```
beta=2, K0=2, MC=1, MF=1.
```

Then `q=3`, `C=1` and the transport residual `Lt=0`, but `V=−44` and
`V+e=−43`. The strong residual `W` is nonzero. Therefore this is **not a
graph zero**, and it does not establish a negative root at any graph zero;
it only demonstrates that positive witnesses and transport alone cannot
justify treating `V+e` as a positive natural witness.

These are finite checks of the graph data and a manually transcribed carrier
formula, not Lean elaboration of the draft or a proof of the quantified
ring equalities, nonzero-at-zero guard, positive-zero equivalence, or iPRA
endpoint. Signed substitutions in the test are ring-valued; the candidate's
actual witness must be positive. The current-source rebuild retained the only
Lean slot, so no additional Lean was run for this audit.

Reproduce with:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube76-independent-y-binding-finite/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `7c530596069e7458983811f30928e1d9c43b93f9b8843f79eb9e12ca06488343` |
| `result.json` | `375ccad5d420be6efb29db232fce42a383858c0a846d6355a13eb3d542a6d146` |
