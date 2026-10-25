# A staged square recovery companion in ten positive variables

The single literal equation is `equation78_degree454.json`. It has ten
strictly positive integer unknowns, 78 live arithmetic operations and exact
total degree 454. Its whole fixed coefficient tuple is supplied under
`coefficients/` and reconstructed by the finite 436-character seed in the
retained coefficient recipe. The ports are constants, not unknowns.

The new ordinary proof in `PROOF.md` delays the first Pell square until
after folding the main index. It removes polynomial doubling of the strong
pair. The result trades two extra operations for ten fewer degrees relative
to the matched 76-operation degree-464 parent. The incoming 77/460 and
80/382 forms remain distinct tradeoffs. No global optimality or literature
priority is claimed.

The proof composes with the explicitly retained native/refutation
calibration to show, by ordinary mathematics formalizable in ZFC, that the
absence of positive zeros is equivalent to Con(ZFC). It does not prove
consistency and supplies no new complete end-to-end Lean/Rocq derivation.

Run from any working directory with Python 3 and its standard library:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B rebuild_coefficients.py
python3 -B build.py --check
```

The verifier covers all 78 actual gates through 31 exact free-polynomial
cuts, every coefficient byte, graph liveness, the entire 39-term leading
homogeneous part, and deliberately changed reachable circuits. The local
Pell control is synthetic arithmetic data, not a zero of the calibrated
consistency equation. No finite check is substituted for an unbounded proof.
Receipts from the performed ordinary and optimized runs are included.

`section.tex` is a report-ready explanation with all polynomial definitions
and the new proof. `PROVENANCE.json` records immutable input identities;
inherited licenses and notices are retained. New work was prepared with AI
assistance and follows ProveIt's MIT No Attribution license.
