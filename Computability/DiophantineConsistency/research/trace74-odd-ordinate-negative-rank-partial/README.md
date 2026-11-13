# Odd ordinate with negative signed rank: a partial fixed-payload assignment

This external exact-arithmetic calculation tests a candidate assignment against several separately established graph consequences. For the fixed coefficient payload put `q=beta+1`, `X=q`, `Y=q³`, and `A=Y(X+1)`. Let `c=y₅(A−1)` in the Pell recurrence and choose

```
k = 4 + q⁴ floor((c − 1 − 4q³)/q⁷),
eta = c − kq³,    zeta = k − eta,
C = q³+q+3−MC.
```

A modular construction in `check.py` chooses `q³≤F<2q³` so the signed rank `R` and offset `e=k−R−1` obey `R<0`, `q⁴|e`, and `k≡4 mod q⁴`. It checks positive `eta,zeta`, `k>8XY²+4`, `c>2q⁴`, positive scalar `B=(K0+1)C−F`, and the source-cone formulas with pinned fixed payloads. The odd ordinate is actual index 5, not an independently chosen residue. The congruence `k≡4 mod q⁴` matches a hypothetical first-index residue for `n=2`; it does not establish the first Pell equation or the existence of that witness.

The calculation also verifies `8q⁷+4 < k < 32q¹⁴+32q⁷+6`. Here `XY²=q⁷`, so the checked first-Pell recurrence gives the left and right expressions as its `k` values at indices 2 and 3. Strict growth of Pell ordinates rules out every positive first-Pell index for this particular tuple. Thus the first-Pell recurrence excludes this candidate from a positive 74 graph zero, even though the other tested consequences above hold. No conclusion about arbitrary negative-rank candidates or general F/C bounds follows.

The author command `nice -n 15 python3 -I -S -B research/trace74-odd-ordinate-negative-rank-partial/check.py` was run in actual tool session 34075, outer exit 0. Checker SHA-256 `c30529f1862ddc65d8ea6f023cbbe7da5a2ff04d2e2da74f3d4324a2acdea33d`; captured `observations/attempt02/stdout.json` SHA-256 `7276713d38fb79d6c4271eff7edda634ef2674a6715839b10d57f88513edfedd`; stderr empty. A prior incomplete author session 55262 was interrupted on resource-coordination instruction and reaped with exit 130; its partial output is not evidence.

This is an external calculation using pinned source bytes and raw payload hashes, not a Lean theorem identifying the payload with symbolic ports. It does not establish the scaled second-Pell, adjacent, carrier, or full graph equations. The full-graph exclusion is a mathematical application of the separately checked recurrence, subject to that interpretation and the inherited proof-provider limits.

Independent [result audit](../../reviews/trace74-odd-ordinate-negative-rank-partial-result-independent/README.md) passed, SHA-256 `7aa70c72c8165c198dcae723feeb0e8f479d9870bb3a0483441b12129c186dc5`; its complete rerun exited 0 and reproduced the recorded stdout byte-for-byte.
