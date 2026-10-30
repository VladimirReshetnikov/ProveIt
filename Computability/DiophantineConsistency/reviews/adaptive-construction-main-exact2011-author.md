# Exact main carrier and scaled norm

`main_shift_exact` proves that the exact additive quotient `k=R+1+(Y*q²)*t`, the multiplier `X=q*w`, and the correction `gamma+w=gammaOld+t` imply

```text
(Y*q²)*gamma + q*(X*Y) - (k-R-1) = (Y*q²)*gammaOld.
```

The proof justifies each truncated subtraction using the additive identities. `main_norm_exact` uses this shift and the old main norm to obtain the complete scaled main norm. Both are valid in every model of the stated `IΣ₁` assumptions and report `[propext, Classical.choice, Quot.sound]` in Lean. Their premises are explicit; this packet does not connect them to Assembly or establish a complete adaptive zero or HA proof-existence theorem.

The author build passed at `/tmp/adaptive-construction-main-exact-zy2iaad4` against `/tmp/adaptive13-assembly-recomposed-q9s50zdl`. The [18-file evidence manifest](adaptive-construction-main-exact2011-author-evidence/FILES.json) has SHA256 `ace371f6e6af80e3fccf8fdfb4c1b8f6b37944e8403721338e87014750085bf9`. It preserves the initial failed square-versus-product calc attempt, the corrected build, source snapshots, full logs and timings, driver, provider metadata, canonical state and guards. To replay, set `ADAPTIVE_ASSEMBLY_BASE` to the authenticated composition and run `success/driver.py`; the canonical and package boundaries remain inherited.
