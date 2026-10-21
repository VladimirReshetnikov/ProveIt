# Use AX's private parameter as the generalization binder

This is a calibrated change to the command interface, independent of constructor orientation and of the falsity-guard variants.

Keep every AX parameter, every logical row, the full gate, the saved top, and the reset behavior unchanged. Replace only its ninth stack head

```
Q_U(oldH)  by  Q_C(oldH),
```

where U is incoming D and C is the independently read private AX parameter. The output still has exactly ten heads: eight implication-coded logical rows, one tag2 generalization, and the saved incoming top. The seventh/eighth logical rows retain their original parameters; only the ninth generated head changes.

## Soundness

The incoming cache oldH is a native theorem on safe runs. The theorem-only generalization rule permits every numerical binder, so `Q_C(oldH)` is also a theorem. Every other soundness step is unchanged. The conservative protected-tail balance remains ten heads per returning AX, so the same credit proof applies.

## Exact completeness block

Use the transfer contract `S(t,w,d,h)=(h,tail(w),d,head(w))` on returning branches. This includes the accepted cache-guard transfer, the top-guard transfer, and a total transfer with the guard moved to AX or MP.

For the new AX command, H and PUSH have their same normal-return contracts. Their proofs use only the ninth head's tag2 and its position, not its particular binder. Truth/reset, row selection, dominated-row selection, full-bundle selection, and MP therefore use the same command blocks as before.

Generalization becomes shorter. Given the strong block B_X, use

```
B_(Q_i X) = B_X;PUSH;S;AX(i;0,0);S^10.
```

If an allowed guard halts earlier, the strong contract is satisfied. Otherwise B_X returns `(X,w,0,0)`, PUSH gives `(0,[X;w],0,0)`, and S gives `(0,w,0,X)`. The next AX has C=i, so its ninth head is exactly `Q_i(X)`, and its tenth is saved0. The ten shifts return `(Q_i(X),w,0,0)` as required. No J(i) block or positive counter offset is needed, including i=0.

The gate of `AX(i;0,0)` need not be zero: here A=0 and B=X. It may be enabled when i differs from0 and X. This does not affect the calculation. The full enabled gate is implication-coded, hence not1; the first shift safely overwrites it. This qualification is necessary for the top-guard transfer version.

The refutation suffix, wire packing, cofinal candidate construction, and proof-pointer drain argument are unchanged. Thus the new command calculus halts on a safe scheduled run exactly when the accepted native calculus derives1. Through the inherited calibration this is equivalent to ZFC inconsistency.

This note proves the all-natural logical interface. A source implementation must separately establish that only the ninth head changes, with the old cache used before adding the y field, and that all ten-head counts, scratch restoration and field decoding remain exact. No physical state count is asserted here.
