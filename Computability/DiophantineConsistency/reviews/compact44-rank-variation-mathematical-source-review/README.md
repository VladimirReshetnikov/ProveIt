# Independent source review: conditional compact44 rank variation

Reviewed commit `f08bb1ad13`, in particular
`ArithmeticConstructionVariationCompact44.lean`,
`CompactRankVariation.lean`, the `PackingInput` and `packing_alpha`
statements, the compact `Gamma` definition, and the controller's `calibrated`
lemma. No mathematical defect was found in the inspected source argument or
in the stated hypotheses. This is a focused source review, not a new Lean
replay or an audit of every transitive dependency.

With `B = 2^590069`, `q = B^N`, `ρ = 2^(67*1063)` and
`P = bsum 590069 δ N`, the generic variation lemma proves
`C1 = C0 + ρP` and `F1 = F0 + (K+B^s)ρP`. Its proof uses the specified
no-wrap support to keep both quotient wrap terms unchanged. Since each full
packing supplies `C + F + α = q`, the rank identity yields

```
R1 + ρ (q^2-1) (1+q(K+B^s)) P = R0.
```

The multiplier is exactly the imported `Gamma K N s`, with the same model
`K`, `N` and `s`; the compact client is a specialization of the generic
argument, not a substitution of the 2011 kernel constants. The calibration
lemma cancels that same multiplier-times-`P` modulo `590069*N`, whose
positivity follows from the original `PackingInput`'s `N > 1`.

Both the original **and** the changed word must independently satisfy the
entire `PackingInput` for the same coefficient, masks, length and stride.
The cell perturbation is required exactly at every `j<N`; the dummy function
must be Σ₁-definable and globally Boolean, and every nonzero dummy must obey
both `j+1<N` and `j+s<N`. The calibration result additionally assumes its
congruence for this **same** dummy function. These are substantial premises:
the reviewed theorem does not build the changed word, establish either
packing or physical dummy safety, connect controller choice to a word, bind
the arbitrary `K` to retained bytes, or prove a graph-zero/iPRA result.

The no-Lean `audit.py` independently checks the complete textual adaptation of
the generic variation source, and confirms that the substituted
`one_lt_exp`, `bsum_zero_fn` and `calibrated` declarations have the same
source text as the original helper declarations. It compares the final
client's frozen/source/object/log hashes with the author retry receipt and
checks both named final axiom reports. It also checks the two earlier output
objects against their reported hashes. A run exited 0 and a repeat was
byte-for-byte identical to [CHECK.json](CHECK.json); optimized Python was
rejected. These sampled artifact checks do not independently authenticate the
compiler's complete direct/transitive inputs, intermediate states, package
or dynamic ancestry. The recorded initial client failure remains separate
from the successful retry.
