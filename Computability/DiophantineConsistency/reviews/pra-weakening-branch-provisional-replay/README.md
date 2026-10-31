# Negative pi weakening branch on a provisional parent

`actualWeakeningBranch_eq` checks by definitional equality that the formula is
the literal seventh disjunct of Foundation's `(Derivation.blueprint T).core.pi`
for arbitrary set theories with a `Δ₁` instance. The candidate-PRA model
witness-bound theorem proves its negation has monotone witness bounds. This is
one rule disjunct, not the whole derivation core. Both axiom checks report only
`propext`, `Classical.choice`, and `Quot.sound`.

Run from the repository root:

```
python3 Computability/DiophantineConsistency/reviews/pra-weakening-branch-provisional-replay/replay.py
```

The script guards 191 declared current project sources and 189 inherited
project objects. The parent `/tmp/pra-setshift-coherent/lib` is partially
inherited; source/object correspondence for the inherited project closure and
Foundation, ZFCinPA and package ancestry are not fully authenticated.

Independent same-parent replay `/tmp/pra-weakening-branch-independent-ps19572y`
passed with both source/object/full-log hashes matching the author. State and
logs are frozen in `independent-evidence/`; the inherited-provider scope is
unchanged.
