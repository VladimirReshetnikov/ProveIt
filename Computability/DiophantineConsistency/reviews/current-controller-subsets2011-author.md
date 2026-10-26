# Actual controller subsets: author verification

This is an author receipt, not an independent review. The entire new main
module and focused checks were read before their first, successful Lean
replays. The mathematical reference is §11 of
`research/padding-staircase-independent/PROOF.md`, SHA-256
`69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`.

The only import of the main module is the frozen
`CurrentPowerCoordinates2011`, source SHA-256
`53853c593225c4a616b0701bdbcd6773846e3a4add7cc5f653a9c7609bf96497`.
It supplies the actual complete-modulus order and derived coordinate
equivalence. The imported `ControllerResidueLift` constructs the optional
Boolean choice, positive small cardinality, and finite subset using
`ControllerAuxiliaryChoice` and `ControllerOrbitTransport`; none of these
objects is an unproved premise of the new endpoints.

For every natural k with `d*auxiliary < auxiliary^k`, and every target t
in `ZMod (d*auxiliary^(k+1))`, `exists_shifted_subset` proves that there
are natural ε,a and a finite subset s of `ZMod (auxiliary^k)` such that

```
ε ≤ 1, 0 < a, a < d*auxiliary, s.card = a,
sum (j in s) B^(2+(auxiliary-1)*j.val) + ε*B^3 = t.
```

The index subset is an actual Finset, so it has no repeated indices. The
base B is proved to be a unit from the positive finite order of
`B^(auxiliary-1)`; the proof introduces no new unit assumption. The
normalized subset is applied to the target multiplied by a constructed
inverse of B², and the result is multiplied by B². A generic opaque
modulus transport changes the factored modulus `(d*auxiliary)*auxiliary^k`
to the complete modulus without evaluating the enormous natural B.

The focused checks cover the base-unit theorem at k=0, failure of the
strict size condition at k=0 and k=1, its success at k=2, the zero target
with positive subset cardinality, and the unrestricted target endpoint.
All four axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, new axiom, `native_decide`, external certificate
assumption, or incoming program was used.

This packet does not place the subset in physical cells, prove those
positions safe, prove Γ invertible, or compose a final rank congruence.
It also does not claim a complete equation-converse theorem. Cardinality
coprimality is used inside the imported construction but is not exported
by the new existential endpoint; its exported quantitative bounds are
the positivity and strict upper bound displayed above.

Frozen files and fresh objects:

| File | Lines | SHA-256 |
|---|---:|---|
| `CurrentControllerSubsets2011.lean` | 102 | `6870e735e1134fcd7a240e3a306db595ae23c9ba62eeaeaeb031adcea889292a` |
| `CurrentControllerSubsets2011Checks.lean` | 39 | `68be80d347e9744be71abfcdbbe4328b3c244c41c1a0369395dc92438991f235` |
| `CurrentControllerSubsets2011.olean` | — | `ae459af83268faaf733e67bfdd9f3fb6b83accdbe97414a421448e76858bb78f` |
| `CurrentControllerSubsets2011Checks.olean` | — | `eed1e4443f8cf090455279e4772213bf4b2af7e85a79fd5201c8626be5a20f3f` |

Commands, run serially from the repository root:

```
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentControllerSubsets2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerSubsets2011.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentControllerSubsets2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerSubsets2011Checks.lean
```

Both first attempts exited zero. Main: 4.11 seconds, peak RSS 3,248,496
KiB, empty log. Checks: 3.27 seconds, peak RSS 3,235,532 KiB. Logs are
`/tmp/current-controller-subsets-main.log` and
`/tmp/current-controller-subsets-checks.log`, with corresponding
`*-time.log` files. Existing accepted sources were not edited, and no
Git operations were performed.
