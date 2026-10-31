# Negative pi shift-rule branch on a provisional parent

`actualShiftBranch_eq` checks by definitional equality that the branch is the
literal eighth disjunct of Foundation's `(Derivation.blueprint T).core.pi`,
for an arbitrary set theory with its `Δ₁` instance. `wb_neg_actualShiftBranch`
proves the negation of that branch has monotone witness bounds in all
candidate-PRA models. The proof handles both bounded rule parameters, the
rule graph, the `fstIdx` witness and the setShift output. It does not establish
the whole derivation core or the final HA equivalence. The three axiom checks
report only `propext`, `Classical.choice`, and `Quot.sound`.

Run from the repository root:

```
python3 Computability/DiophantineConsistency/reviews/pra-shiftrule-branch-provisional-replay/replay.py
```

The script rebuilds the theorem and checks, guarding 221 declared project
sources and 219 inherited project objects. The parent
`/tmp/pra-setshift-coherent/lib` has an independently replayed 102-source
set-term history parent plus a freshly compiled witness chain, while other
inherited project source/object correspondence and Foundation, ZFCinPA and
package ancestry remain unauthenticated. The witness parent emitted an
unused-section-instance linter warning in `PRAWitnessSetTerms`; this is not a
strict warning-free rebuild of the entire closure.

Independent same-parent replay `/tmp/pra-shiftrule-branch-independent-nkbjw4da`
passed with both source/object/full-log hashes matching the author. State and
logs are frozen in `independent-evidence/`; the inherited-provider scope is
unchanged.
