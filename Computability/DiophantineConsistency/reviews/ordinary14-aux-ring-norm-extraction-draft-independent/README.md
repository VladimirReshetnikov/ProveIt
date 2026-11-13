# Independent source review: auxiliary ring-norm extraction

**Source review passes; not elaborated.** The proposed scaled-root lemma
uses `ModelDifferenceRing.nonneg_or_nonpos` to write any signed ring carrier
as `ι z` or `−ι z` for a natural z. Squaring and injectivity give a natural
equation `z²=U² n`; with the explicit `U>0` premise,
`ArithmeticAdaptiveQuotients2011.scaled_quotient` supplies the natural root.
No orientation of the signed carrier is assumed.

The direct first residual is exactly the natural first Pell norm after
`ell=(XY)(Yk)` and k=eta+zeta. The strong ring residual becomes
`(ic²)²+Delta=Delta f²` by ring arithmetic and injectivity, without replacing
ring subtraction by truncated natural subtraction. The natural Delta
identity follows from the explicitly supplied polynomial definition. These
facts and the explicit natural positivity and signed Q/z bindings match the
separately drafted norms-to-bounds composition. The draft does not extract
any of these hypotheses from an actual graph.

The checker pins the source interfaces, verifies the first Pell and strong
identities in a sparse integer polynomial ring, checks positive, zero and
negative finite carrier cases and a zero-scale boundary, and replays the
author inventory and independent composition review. These checks do not
elaborate Lean. Coercions, case rewrites, `ring`, provider ancestry, literal
graph field extraction, witness updates and the iPRA endpoint remain open.
No Lean process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-aux-ring-norm-extraction-draft-independent/check.py
```

Compare stdout with `result.json`.
