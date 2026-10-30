# Positive main correction from the first Pell seed

`positive_main_correction` proves, in every model of the stated `IΣ₁` assumptions, that the explicit first-Pell seed index and ordinate identities, index at least two, `Y=sY*q^3`, `X=q*w`, and positive `q`, `X`, `Y`, `sY` and `gammaOld` yield witnesses `t` and `gamma` with

```text
0 < gamma,
k = R + 1 + (Y*q^2)*t,
gamma + w = gammaOld + t.
```

The proof first shows the Pell ordinate exceeds its index when the index is at least two. This forces the residue quotient to be positive, so the resulting explicit correction `t = 4*X*(sY*q)*s` dominates `w`; `gammaOld+t-w` is therefore strictly positive and its addition with `w` is exact. The separate `time_lt_ordinate` theorem is also checked. Both report `[propext, Classical.choice, Quot.sound]` in Lean.

All seed identities and positivity hypotheses remain explicit; this does not yet extract them from the actual Assembly, establish the first-carrier coordinate or produce a thirteen-variable zero. It is an all-model semantic theorem, not an HA proof-existence theorem.

The author build passed at `/tmp/adaptive-construction-correction-positive-5erv131k` against `/tmp/adaptive-construction-correction-5b08scd8`, itself built on the authenticated composition. The [26-file evidence manifest](adaptive-construction-correction-positive2011-author-evidence/FILES.json) has SHA256 `f1b2158be99bff64192d6ae5938df3b231697a2423b751fdfba82b8dbe1ecb35`. It preserves two unsuccessful source builds (unavailable tactic and a commuted-addition mismatch), the successful build, snapshots, logs, timings, providers and guard inputs. A prior driver preflight typo failed before any build directory was created. To replay, set `ADAPTIVE_ASSEMBLY_BASE` to the independently replayed correction provider and run `success/driver.py`; the underlying canonical composition and package boundaries remain inherited.
