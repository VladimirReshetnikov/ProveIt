# Independent source review: compact symbolic model ports

The [source draft](../../research/ordinary14-natural80-compact-model-ports-draft/README.md) proposes the correct symbolic tuple and mathematically plausible model-bound derivation for the natural-80 route. Both source receipts reproduce. The draft and some cited port-bound clients remain unelaborated; no Lean model theorem, iPRA proof or physical-byte equality is established.

The source tuple is `[betaNat, paramKernel rho, lowNat, betaNat+highNat]`; the fourth value is already shifted. The proposed representation statement identifies the cast of each signed symbolic port in `DiffRing V` with the embedding of the corresponding model natural cast. The `change` and cast simplifications still need Lean checking. The slim bound source proposes beta positive, beta at least 46, `lowNat<beta`, and `beta+highNat<2*beta`, given beta's exponential identity and the two fixed-mask identities; the client specializes those identities. The separate unelaborated strict-K0 source proposes positivity from the kernel's positive top term.

The MC positivity argument is sound under the cited model declarations. `lowNat` is definitionally the same closed mask used by `CompactConcreteMask.model_origin`, whose zero-index digit is `Exp.exp 67−2`. The standard exponential cast gives `Exp.exp 2=4`, and exponential monotonicity gives `Exp.exp 67>=4`, so that natural-model digit is positive. If the cast of `lowNat` were zero, the cited digit definition `X / Exp.exp(w*k) % Exp.exp w` would give zero; contradiction. Nonzero natural-model values are positive. The MF positivity argument then follows from positive beta and nonnegative `highNat` after casting their sum. These are mathematical implications; the exact `change`, `norm_num`, `simp`, order and subtraction steps and their instances have not been elaborated.

The inspected rank-window signature directly needs represented positive beta, `MC<beta`, `MF<2*beta`, and additional positive J/F/alpha, q-definition and gap hypotheses. The proposed seven port facts cover the named port bounds but do not by themselves supply those other inputs or a graph-to-norm theorem. The independent receipt pins 13 source files and inspects the tuple, actual low-mask definition and origin statement, digit/cast operations, K0 split, slim bounds, rank signature and three requested axiom reports. The reports are unexecuted; providers, iPRA derivability and symbolic-to-file/JSON/PDF associations remain open.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-compact-model-ports-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-compact-model-ports-independent/result.json
```
