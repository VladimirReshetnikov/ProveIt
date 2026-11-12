# Independent source review: natural-80 gamma client

The [gamma client](../../research/ordinary14-natural80-gamma-client-draft/README.md) proposes a mathematically coherent composition from an 80 own zero to `0<v 12`, conditional on its cited source lemmas and the explicit port representations and inequalities. The original and independent receipts reproduce. This review does **not** run Lean, verify the source proofs or provider closure, or establish an internal iPRA theorem.

The proposed theorem assumes representations of beta, K0, MC and MF in the model's difference ring; `0<beta`, `0<K0`, `MC<beta`, `MF<2*beta`; and an 80 `InternalZero`. It does **not** assume gamma positive. The source also does not require beta at least 46 or strict MC/MF positivity in this client: the cited scalar rank-window theorem has the weaker displayed hypotheses in a natural-arithmetic model. This source statement would therefore be stronger than the sufficient fixed-port conditions recorded for the external candidate, if the full chain elaborates.

The partially shifted valuation keeps J and gamma at slots 0 and 12 and increments F, alpha, w, s, eta and zeta. Subject to the imported J-positivity and own-zero drafts, their stated hypotheses yield positive J, F, alpha, w, s, eta and zeta; `q>=2`, `X>=q`, `Y>=q³>=8`, and `U>0`; the first Pell norm; the main signed-magnitude norm; and `F+alpha<q`. The source's local beta/K0 requirements occur only where needed by the cited own-zero and gap clients. In particular, the gamma-zero branch does not assume its own conclusion.

The independent checker pins 19 sources, inspects the signatures and selected application sites of the norm, rank, Pell and gamma-zero interfaces, and verifies these algebraic identifications by sparse integer-polynomial arithmetic:

```
(m*k)*(m*k+k)+1 = 1+m*(m+1)*k²,
(3+4*a)+a² = (a+1)*(a+3),
R_graph = R_rank_window when q = 1+J*beta.
```

The last equality relies on the natural-model fact `q-1=J*beta`; the gap from the guard justifies the separate `q-F` truncated subtraction in the main-pair binding. The intended quotient from `direct_main_orientation` supplies the main Pell norm. `large_ordinate_of_two_norms` then proposes `k>=8*m+4`, including an index-one exclusion with the explicitly selected `Direct80IndexOne.impossible` parameters; the rank window and radix bounds feed `narrow_inequalities` to obtain `R+1<k` and `X<eta+Y*k`. Setting `v 12=0` also sets the unchanged partial coordinate `u 12=0`, so the proposed `gamma_zero_impossible` applies and gives the desired contradiction.

The independent receipt additionally runs bounded radix/rank examples, recurrence checks for the first Pell norm, and 11,340 fact-level gamma-zero controls. These are finite controls, not proofs of the unbounded source lemmas. In particular, the proposed direct-main orientation, two-norm/Pell classification, rank window and graph-to-main-pair bindings are taken as the cited **source declarations**, not newly machine-checked results in this review.

No definite error was found in the inspected assumptions or application directions. Lean still has to check all types, coercions and instances, the `simpa` normalization of the local `let` values and signed-pair norm, the natural-subtraction simplification `q-1=J*beta`, the `ring` rearrangements and power monotonicity, and all imported source proofs. The two `#print axioms` commands have not run. Physical port bytes, the separate Carrier65 PDF, and conversion to an iPRA derivation remain open.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-client-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-client-independent/result.json
```
