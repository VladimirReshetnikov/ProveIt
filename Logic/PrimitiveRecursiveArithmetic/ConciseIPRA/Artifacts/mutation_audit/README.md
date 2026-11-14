# Mutation audit of the stream checker

This directory is the repository's own audit, not a delivered package.

- `harness.py` applies every single-step reduction of the abstract syntax tree of a checker
  (dropping an operand, an argument, a comparison, a statement, a conditional branch, ...) and
  compares each variant with the control, in process, on the stream fixtures under a directory
  and on random perturbations of them. A variant that never differs is printed with its size.
  `WHOLE=1` reads whole-document `.json` certificates instead of `.jsonl` streams; `NMUT` sets
  the number of perturbed streams.
- `attack.py` builds `discharge_at_zero.jsonl` and runs it on the control and on the variant
  of the 239-token stream checker in which the disjunct `s` of the floor image is deleted.
- `discharge_at_zero.jsonl` is a certificate of 19 packets for the false public goal
  `D_{x,y} (I(y, 0; u.S 0) = I(y, 0; u.0))`. The 239-token stream checker
  (`prefix_conditional/code/checker_tokens239.py`) rejects it; the variant accepts it.

```
py -I -B harness.py ../prefix_conditional/code/checker_tokens239.py ..
py -I -B attack.py ../prefix_conditional/code/checker_tokens239.py discharge_at_zero.jsonl
```

Result of 2026-11-13 on the 239-token stream checker: 158 single-step reductions; on the 509
stream files of `Artifacts/` and 20,000 perturbations of them (4,641 accepted by the control),
156 reductions differ from the control. The two that do not are the truth-valued floor image
`(... ) and k`, which is the delivered program of 549 bytes, and the deletion of the disjunct
`s`, which is unsound by the certificate above. The article records this in the chapter
"Certificates and checkers".
