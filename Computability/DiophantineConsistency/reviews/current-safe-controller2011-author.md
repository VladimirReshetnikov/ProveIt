# Actual safe controller: author verification

This is an author receipt, not an independent review. I read both complete
new sources before their first compilation and read the entire frozen
`CurrentControllerUnits2011` main/checks before composing its unit theorem.
I authored the separate Subsets and Positions dependencies; the Units
packet was authored by `controller_certificate` and independently reviewed
by `circuit_reduction`.

The generic power-sum lemmas work over any commutative semiring. They
first reindex the finite natural support through the injective literal
position function, and then reindex its cyclic image through the proved
injection on that support. Canonical cyclic values equal the natural
positions because every position is strictly below N. The optional cell3
is absent from the orbit image, so insertion adds precisely one term b³
when ε=1. There is no multiplicity or wrap assumption in this identity.

The actual endpoint `exists_safe_power_sum` takes only natural k,rw with
`rw<k`, `d*auxiliary<auxiliary^k`, and a target in
`ZMod (d*auxiliary^(k+1))`. It constructs a finite set S of physical cells
in `ZMod (auxiliary^(k+1))` and proves

```
0 < S.card, S.card <= d*auxiliary,
forall j in S, 0 < j.val and j.val+1 < N and j.val+auxiliary^rw < N,
sum (j in S) B^j.val = target.
```

The upper cardinality includes the optional3: the orbit cardinality a is
strictly below d*auxiliary, and ε≤1. No orbit, selected subset, safe-set
property, or desired sum is a premise. `exists_safe_gamma_sum` retains the
same conclusions and replaces the sum equality by

```
(Gamma rw (k+1)) * sum (j in S) B^j.val = target.
```

It applies the safe-power theorem to an inverse-normalized target using
the actual proved `isUnit_Gamma_width_cells` theorem at the full modulus.
The Gamma unit is not a caller hypothesis. The huge literal B, K, and
Gamma definitions remain opaque during composition; no alternate ports
or residue-defined coefficients are introduced.

This packet does not yet mutate an actual word, iterate ordinary C/F
increments, establish a final rank congruence for such a word, or prove
the converse polynomial endpoint. Those remain separate compositions.

Frozen sources and fresh objects:

| File | Lines | SHA-256 |
|---|---:|---|
| `CurrentSafeController2011.lean` |89| `561f7bdaf81a6973fbe713b7710ef9258eafeff35d82e55e9e75ed643f2a3d2f` |
| `CurrentSafeController2011Checks.lean` |53| `05055e464050cb2319b4b8a942c5990c3b2e36f9ff4c3a8af671a0e19a016e2c` |
| main `.olean` |—| `ed2676b1626ae9c9400dab6f19b77d4fdb06f43ac89602445c19327ebb26fffe` |
| checks `.olean` |—| `24de3cce702ae434ac616068449a296de0b5143b0c029f1318823df590bc9ffc` |

Direct dependency source hashes:

| Dependency | SHA-256 |
|---|---|
| `CurrentControllerSubsets2011` | `6870e735e1134fcd7a240e3a306db595ae23c9ba62eeaeaeb031adcea889292a` |
| `CurrentControllerPositions2011` | `aab00b74d13e24bb78dda62c5c5a5fa55990f414821fef7b56d02c8fee675acf` |
| `CurrentControllerUnits2011` | `1c3bdb8af6c4113589b92b76aa895fbee3ecad4ca4d32f8e6290b382bf2f004f` |

Fresh main/check builds used `lake env lean -M6000 -j1 -o` with sources
under `Computability/DiophantineConsistency/Lean/DiophantineConsistency`
and matching objects under `.lake/build/lib/lean/DiophantineConsistency`.
Both sources set `Elab.async false`. Main passed in12.41seconds, peak RSS
3,865,412KiB, empty log; checks passed in3.57seconds, peak RSS3,245,632KiB,
without warnings. All four axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. No new axiom, `sorry`,
`native_decide`, external certificate premise, or incoming execution occurs.

The first main attempt needed an explicit type annotation identifying
`d*dimension(k+1)` with `d*auxiliary^(k+1)` before multiplying the inverse
by the target. That elaboration correction changed no theorem premise or
mathematical result. Checks cover both optional-bit values, the two
distinct positions2 and3, a concrete admissible exponent pair at target0,
and the arbitrary-target Gamma endpoint. Final logs are
`/tmp/current-safe-controller-main-final.log` and
`/tmp/current-safe-controller-checks.log`, with corresponding timing logs.
No accepted source, central document, or Git state was changed.
