# Paid complementarity factoring for the numeric signal packet

A single algebraic rescheduling saves **80,482 operations** in the complete one-step schedule for either version of the corrected 18-particle signal packet. The original full packet falls from **25,392,522 to 25,312,040** operations. The independently reviewed guard-projected packet falls from **17,903,098 to 17,822,616** operations. This stage preserves the full polynomial on every integer tuple and removes no witness, guard or residual.

The [portable helper](signal_complementarity_factoring.py) and [receipt](signal_complementarity_factoring.json) bind this result to the actual numeric compiler and the separately reviewed projection census. They reconstruct every actual branch's literal matrix and guards for the schedule census, verify the full schema digest against that review, and check exact expanded polynomials for bounded complete packets. They do not emit a multi-million-gate file or repeat the original author suites.

## Exact polynomial identity and paid sharing

There are `B=80,501` branches and `d=18` copy coordinates per branch. Write `e_r` for selectors, `X_ri` for branch copies, and

```
E = Σ_r e_r,
C_i = Σ_r X_ri,
A_r = Σ_i X_ri.
```

The original complementarity contribution is

```
Σ_r (E−e_r) A_r.
```

Its exact factorization is

```
E (Σ_i C_i) − Σ_r e_r A_r.
```

Distribution and the identity `Σ_r A_r=Σ_i C_i` prove equality in the integer polynomial ring, without assuming a residual vanishes. In particular E is **not** replaced by 1, and `C_i` is **not** replaced by the supplied input `x_i`. Every affine residual and its square is otherwise unchanged. Adding these unchanged squares proves equality of the **complete** old and new packet polynomials on all signed assignments as well as natural ones.

The copy-column sums must be made available explicitly. The old input row may have been evaluated as successive subtractions

```
x_i − X_0i − X_1i − ... − X_(B−1)i.
```

That costs B additions/subtractions. Computing `C_i` first costs B−1 additions; computing `x_i−C_i` then costs one subtraction. Thus exposing each `C_i` costs exactly the same B operations. The one-hot row similarly computes E in B−1 additions and E−1 in one subtraction, retaining E for the complementarity block. No register is presumed to exist merely because its algebraic form occurs inside a residual.

All these quantities are derived arithmetic registers, not new existential witnesses. Signed intermediates are permitted. The original complementarity polynomial remains nonnegative on natural tuples because it still equals the original sum of nonnegative terms. Its natural zero-set theorem and external-horizon convention are unchanged. The larger signed scope here concerns polynomial equality, not a new signed halting theorem.

This factoring can be applied separately to the original packet or to the already guard-projected packet. It does not identify their un-restored polynomials or replace the earlier natural graph-bijection proof. The guard projection remains a separate coordinate/row transformation.

## Complete paid schedule

Let R be the number of squared affine residuals, N their variable-coefficient incidence count, and U the count of nonunit affine coefficients. Each row begins with a positive term, charges multiplication for every coefficient of absolute value greater than one, and combines its signed terms by binary additions/subtractions. There is one affine constant, the `−1` in the selector row. Constants and input wires are free; every emitted binary `+`, `−` and `*` costs one. In particular the large exact mode-code coefficients are not treated as free multiplications.

The unchanged affine computation costs `U` multiplications and `N−R+1` additions, and its R squares cost R multiplications. Exposing E and the eighteen columns is included in those affine costs.

The original complementarity block costs B products and `17B+B=18B` additions: seventeen to form each row sum and one for each `E−e_r`. The final sum has **R+B terms**, costing `R+B−1` additions. Therefore its complete schedule is

```
M_old = U+R+B,
A_old = N+19B.
```

The factored block pays:

- `17B` additions for the same B row sums;
- 17 additions for the sum of the eighteen available columns;
- B products and B−1 additions for the diagonal sum;
- one product for `E·Σ_i C_i` and one subtraction of the diagonal sum.

Its complementarity costs are consequently `B+1` multiplications and `18B+17` additions. The final sum now has **R+1 terms**, costing R additions. The complete new schedule is

```
M_new = U+R+B+1,
A_new = N+18B+18.
```

The new routing computation uses 17 more additions, but the final summation saves B−1; the net saving is **B−18 additions at the cost of one extra multiplication**. Hence the total saving is `B−19=80,482`. Counting only the locally factored expression, or forgetting the changed final summation, would give the wrong comparison.

The exact full-packet census gives:

| Packet | R | N | U |
|---|---:|---:|---:|
| Original | 2,762,961 | 15,323,489 | 5,696,052 |
| Already guard-projected | 1,313,943 | 9,553,307 | 5,425,828 |

| Complete schedule | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Original, before | 8,539,514 | 16,853,008 | 25,392,522 |
| Original, factored | 8,539,515 | 16,772,525 | **25,312,040** |
| Guard-projected, before | 6,820,272 | 11,082,826 | 17,903,098 |
| Guard-projected, factored | 6,820,273 | 11,002,343 | **17,822,616** |

The original and projected auxiliary counts remain respectively 4,196,998 and 2,747,980. Both have the same 18 supplied input and 18 output coordinates as before; their degree remains two. No additional endpoint, loader, horizon or universality obligation is suppressed by the schedule change. This is not a fixed-arity unbounded-history equation or an improvement of the separate 87-operation universal benchmark.

## Source binding, verification and replay

The helper pins `numeric/compile_packet.py` at

```
2df8a5b96630a9b343266ded0b26b6489be601acdee6f50d2a06dad4563e5f57
```

and its `MORITA_18_SIGNAL_MACHINE.json` at

```
3f45f8aa2fbf5756cd1e4cf22fa3e55582abc9ba8275fe246652ceb94eb08e05
```

It also authenticates the exact independent projection checker and receipt by full hashes before using their results. The helper does not import or re-execute that checker, so it does not repeat its entire review. The numeric module is executed from the authenticated source bytes, bypassing any stale or forged bytecode cache. All module entries are restored afterward. Executable checks reject `python -O`.

The helper reconstructs the actual 49,700-mode, 80,501-branch closure, streams the literal guard/matrix schema through the same deterministic digest, and independently totals every affine coefficient, row and slack for each packet. The complete schema digest matches the prior review, and the independently reconstructed original complete schedules match its saved receipt exactly. It then charges each phase of the newly factored complete schedule and verifies the 80,482 difference.

For selected actual branch subsets of sizes 1, 2, 3 and 5, the helper emits every binary operation for both complete packets, including all global rows and all local guard squares. Independent sparse polynomial expansion verifies full output equality, equality of every affine residual, and unchanged literal row lists. Signed and natural numerical fixtures supplement those exact symbolic checks. Thirty additional tiny complete packets exhaust B=1..6 and d=1..5, checking the generic saving `B−d−1`, the exact operation deltas, and the finalizer with R+1 terms. Small B can make this particular rescheduling cost more; no claim of universal optimality is made.

Run from any directory, supplying a restored original numeric package layout:

```
python signal_complementarity_factoring.py \
  --root /path/to/conservative-signal-release \
  --projection-checker /path/to/review_signal_guard_projection_independent.py \
  --projection-receipt /path/to/review_signal_guard_projection_independent.json \
  --output new_signal_complementarity_factoring.json \
  --expect signal_complementarity_factoring.json
```

The completed run passes **1,064 checks**. The receipt includes complete phase ledgers, source/schema pins, bounded fixture output hashes and exact check counts. No supplied source file or archive is written. This is a narrow scheduling prototype and replay helper, not a newly exposed untrusted-input compiler API.
