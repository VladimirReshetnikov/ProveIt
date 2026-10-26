# Round 21: strict-horizon pooled quartics

For unrestricted integers x_0,...,x_(n-1), each equation is the sum of the squares of the literal quadratic residuals in its `equation.json`. Every collected coefficient is supplied separately.

| Endpoint | Variables | Rows | Degree | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| principal217 | 217 | 154 | 4 | 7,396 | 8,880 |
| low217 | 217 | 154 | 4 | 14,793 | 3,200 |
| dimension216 | 216 | 153 | 4 | 25,602 | 5,632 |

`PROOF.md` gives the full ordinary proof of the new changes. Together with the retained ordinary calibration, ZFC proves that each equation has no integer zero if and only if Con(ZFC). This is an equivalence, not a proof of consistency, global minimality or a new end-to-end proof-assistant build.

The final source lineage is Strict Horizons (239-coordinate pre-endpoint source) → the retained Factorial Free Binomial CRT source → the direct square-shell/C222/ZF/ZFC calibration. The Pooled Powers225 input supplies the reusable two-equation lemma, private-wire method and Pell-difference coordinate method, but its 245-coordinate factorial source is NOT the calibration ancestor of these new equations. The source_commit field inherited from that producer has been explicitly renamed pooling_module_origin_commit in newly generated stages. Historical comments in imported modules retain their original scope; the new entrypoints below select and authenticate the actual strict-source instances.

## Reproduce offline

Python 3.10+ standard library only, from this directory:

```
python3 -B verify.py --rebuild
PYTHONOPTIMIZE=1 python3 -B -O verify.py --rebuild
python3 -B build.py --check
```

The second command propagates optimization into every child interpreter. `verify.py` imports independent checkers, not construction modules. It checks all 173 forward and 176 reverse private-wire identities, the exact 34-atom square frame, both pooling groups (11 and 3), every retained Pell gate, all coordinate inverses, odd-beta and wider-norm source deltas, 76 shears/43 row operations/four monic projections, two further common-Hessian projections, the optional affine consequence, every final row operation and every collected coefficient. Negative corruption controls and exact degree/domain/liveness checks remain active under `-O`.

The source pass authenticates the literal raw strict-source edit, all seventeen power interfaces, inherited factorial-free source checks, the raw factorization/monic projection/coordinate translation, and byte-identical reconstruction of ten strict-source JSON files. The new builder reconstructs and compares eighteen retained JSON stage/endpoint files. The affine intermediate is compared as an exact JSON object because the originating affine exporter used whitespace formatting; all final equations and expansions rebuild byte-for-byte.

`build.py --output /tmp/new-signed-build` reconstructs into a separate directory. Do not run the main blocks of imported helper libraries as standalone releases; their original source comments are preserved. Use the three entrypoint commands above. `--skip-sources` is available only for a faster new-delta audit, not as a replacement for the complete check.

## Files and proof boundary

- `principal217/`, `low217/`, `dimension216/`: complete equations, expansions, metrics and integral row certificates.
- `stages/`, `certificates/`: exact intermediate source systems and reversible/projection certificates.
- `code/`: construction and independent checking helpers.
- `inherited_strict/`: selected full arithmetic/calibration source closure, original notices and complete ordinary proof sources, not the unrelated compact-family release or duplicate PDFs.
- `proofs/`: unchanged incoming method notes, read with the applicability distinctions in `PROOF.md`.
- `SOURCE_PINS.json`: immutable source payload identities.
- `WHITELIST.json`: allowed portable payload list; no local paths or dependency on sibling research directories.

Sparse polynomial format: a term `[c,[i,j,...]]` means the integer coefficient c times the indicated coordinate product; `[]` is the constant monomial. Terms use sorted indices, and duplicate monomials are collected. Residuals have degree at most two; the final polynomial is their sum of squares. The `variables` array is the complete quantified tuple, not a list of additional abbreviations. All declared variables occur.

The computer checks authenticate finite artifacts and identities. The unbounded Pell/CRT/prime-power arguments and inherited syntactic calibration remain ordinary mathematical proofs provided as sources. Existing historical formal sources are retained; no claim is made that their entire imported closure was newly compiled in this round.
