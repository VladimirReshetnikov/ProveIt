# Structured low-mask recipe for the maintained equation

`LowMaskDisplay.lean` proves, for an arbitrary natural radix `r`, that the
actual finite support `lowSupport` has power sum
`G_951(r) + r^960 * G_26(r) + r^1004`, where `G_m(r)` is the finite
geometric sum in the displayed recipe. It then proves

```
CurrentMasks2011.lowPort = beta - G_951(radix)
  - radix^960 * G_26(radix) - radix^1004
```

in the natural numbers, with natural truncated subtraction. This proves a
structured correspondence for the printed low-mask formula, not the exact
integer-subtraction interpretation unless the subtractions' bounds are also
supplied. It does not parse TeX, establish PDF semantics, connect the other
three fixed constants, or recheck the iPRA endpoint.

The fourth bounded author attempt exited 0 with both axiom reports exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx` or warnings, and
unchanged guarded direct input hashes. The machine-readable receipt is
[`observations/author04/observation.json`](observations/author04/observation.json).
The three earlier retained attempts show the missing import and algebraic
simplification corrections; attempt 03's Lean process exited 0 but its runner
incorrectly required an empty axiom list and reported failure. The final
runner checks the actual expected axiom report. The source, runner, Lean
binary and three direct objects were hashed before and after; transitive,
package and dynamic ancestry are inherited and not independently audited.

From the repository root, while the captured providers exist, use a fresh
attempt name:

```sh
python3 Computability/DiophantineConsistency/research/current14-lowmask-display-binding/run.py --attempt fresh-name
```
