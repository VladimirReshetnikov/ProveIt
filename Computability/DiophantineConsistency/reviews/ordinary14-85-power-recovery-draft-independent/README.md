# Independent source review: direct 85 power recovery

The proposed own-zero proof retains the classified main d and old carrier
balance. Its positive qY cancellation gives `qL=qB+H*X`; using `H=3+qD`
produces the stated three-multiplier cross-balance. The Pell projection of the
same main coordinate gives the second remainder, and `mod_cancel` removes the
common `3*a*c` term. The direct growth draft gives `2^R<Y≤a`, while `X<a`;
both `3X` and `3*2^R` are then strictly below H. Only after these bounds does
the source remove remainders and cancel the positive factor 3.

The checker pins source interfaces, replays the author and independent growth
receipts, and independently exercises finite cross-balance and strict-remainder
arithmetic, including q not dividing X and a counterexample without the
remainder bound. These are not graph-zero examples. This is source review
only: Lean elaboration, provider compatibility, concrete beta instantiation,
Mersenne cancellation, external-file binding and iPRA remain open. The imported
FreeJ module is not invoked as a graph theorem by this draft.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-power-recovery-draft-independent/check.py > /tmp/power-recovery85-independent.json
cmp /tmp/power-recovery85-independent.json reviews/ordinary14-85-power-recovery-draft-independent/result.json
```
