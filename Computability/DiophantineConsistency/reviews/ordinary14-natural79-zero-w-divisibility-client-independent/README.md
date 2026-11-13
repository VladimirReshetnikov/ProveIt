# Independent source review: natural-79 positive w via divisibility

The [source client](../../research/ordinary14-natural79-zero-w-divisibility-client-draft/README.md) states a mathematically sound conditional route from its imported signed divisibility and zero-w J-positivity drafts to `w>0`. The displayed theorem assumes represented model-natural beta and K0, `beta>0`, and a 79 graph zero; it does not assume `K0>0`, positive gamma or w, or any MC/MF representation or bound. The actual source, imported lemmas and complete endpoint remain unelaborated in Lean.

The inspected `TenPositive80NaturalProjection.natural_dvd_of_signed` source states that a difference-ring divisor relation between embeddings of model-natural values reflects to natural-model divisibility. Applied to the root-cut proposal, this is the required conversion from `(4*ιY+3) | 3*(ιq)²` to `(4Y+3) | 3q²`, subject to the proposed casts and `simp` steps elaborating. The repository also uses `Arithmetic.le_of_dvd` in the intended direction from positive dividend to divisor upper bound; this review does not independently check its actual Lean resolution or prove its source dependencies.

The size contradiction is valid: `q>=2` gives `3q²>0` and `q²<=q³`; with `q³<=Y` it follows that `3q² < 4q²+3 <= 4q³+3 <= 4Y+3`. An exact polynomial identity and 495 finite boundary controls independently check the size calculation; finite controls do not substitute for model arithmetic proof checking. If positive `3q²` is divisible by `4Y+3`, the cited divisor bound contradicts the strict inequality.

For a hypothetical zero with `w=0`, the proposed J-positive source uses the represented natural K0, allowing K0=0; positive beta and J then give `q>=2`, while the retained `s=n_s+1` shift gives `Y>=q³`. The root-cut source proposes the signed divisor under these assumptions. The final `w_pos_of_zero` client feeds that contradiction into the conditional [79-to-80 shift](../../research/ordinary14-natural79-wshift-model-draft/README.md) only after an additional client is written. This review does not check that the `simp`, `nlinarith`, order, instance and casting steps elaborate, or that the imported zero-w units and quotient source theorems are valid in the selected provider environment.

Both original and independent receipts reproduce. The three source axiom-report commands are unexecuted. Symbolic-port specialization, a checked semantic-to-iPRA endpoint, full provider/axiom closure, and physical coefficient/PDF association remain separate obligations.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-divisibility-client-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-divisibility-client-independent/result.json
```
