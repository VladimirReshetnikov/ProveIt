# Two direct natural quartics for Con(ZFC)

Prepared for Vladimir Reshetnikov and ProveIt, 24 October 2026, with AI assistance.

| Equation | Domain | Variables | Residuals | Degree | Monomials | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| `equations/natural235/` | nonnegative integers | 235 | 184 | 4 | 22,185 | 90,911,633 |
| `equations/natural236_sparse/` | nonnegative integers | 236 | 185 | 4 | 15,645 | 88,233,865 |

Each polynomial is the sum of the squares of every supplied quadratic residual. Every collected coefficient is included in `expanded_polynomial.json`; no unspecified Diophantine predicate, variable exponent or enormous fixed coefficient port remains. Read `proofs/PROOF.md` for the full new ordinary argument and its inherited mathematical interfaces.

The principal equation improves package 133's matched dense minimum from 237 variables, 185 rows, 69,710 monomials and height 133,499,131. The sparse companion is a separate size tradeoff. Neither claim is a global optimum. Both equations use the direct C222 numerical proof calculus; this branch uses neither K215 simulation nor a Jones coefficient tuple.

The main further simplification of the arithmetic is the linear cofinal beta modulus y=V-1, where V=(F²+1)^t and F=t!. A tighter bound on the actual pending products makes the older quadratic V(V-1) unnecessary. The principal equation also composes package 128's one-row indexed-Pell cap with package 133's smaller shared denominator. The sparse alternative keeps the two-stage proof order.

## Verification

Python 3.10+ and the standard library suffice. No network, original checkout, symbolic algebra package or proof assistant is needed.

```sh
python3 -B verify.py --rebuild
python3 -B -O verify.py --rebuild
```

These commands check all inherited source hashes; independently audit every changed and unchanged raw row; verify every exact nonnegative restoration and monic substitution; collect every quartic coefficient; reject deliberately corrupted frame, cap, cofinal and certificate data; and rebuild all twelve normative JSON artifacts byte for byte in an isolated directory. `REPLAY.json` and `REPLAY_OPTIMIZED.json` record successful runs. The producer's checks also remain active in optimized Python.

To rebuild into a new destination:

```sh
python3 -B build.py --output /path/to/new-output-directory
```

To evaluate either equation at an explicit JSON array of nonnegative integers:

```sh
python3 -B evaluate.py equations/natural235/equation.json point.json
```

The evaluator is not a solver or consistency procedure.

## Mathematical boundary

The result is an ordinary proof, formalizable in ZFC, that existence of a zero is equivalent to existence of a finite ZFC refutation. The consistency interpretation composes with the named inherited C222/ZF/ZFC calibration, whose scope is identified in the proof. This component does not supply a newly compiled end-to-end Lean/Rocq proof or an encoded object-language ZFC derivation. Finite artifact checks do not prove unbounded Pell, CRT, factorial, Horn-flow or consistency statements by sampling.

`SOURCE_LEDGER.json` pins each retained input to repository commit `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`. The selected source proofs and license notices are retained. `proofs/COMPACT_PEER_REVIEW.md` is a separate scoped review of the compact companion branch developed in this iteration; it is not used to prove these natural quartics.
