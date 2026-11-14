# Primitive-recursive search for the PA194 list compiler

`PA194SearchPR.lean` proves that the exact `List.find?` search used by
`PA194SourceListPreimage.findPreimage` is primitive recursive whenever its
input type has a `Primcodable` instance and its transformation is primitive
recursive. `search_eq_preimage` connects that search to the actual selected
formula, including the successful membership hypothesis. `shift_search_primrec`
identifies the transformation used by the universal rule, conditional on a
`Primcodable` instance for current Foundation propositions and a proof that
`Semiformula.shift` is primitive recursive for that instance.

The module was checked against a fresh ordered local dependency overlay;
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for the two
primitive-recursiveness theorems and `[propext, Quot.sound]` for the exact
search equality, with no `sorryAx`. The full nested standalone script has not
yet been replayed.

The formula `Primcodable` instance and the primitive-recursive shift theorem
are **not supplied here**. In particular, this result does not establish that
the whole proof compiler is primitive recursive, that its correctness is
provable in arithmetic, or any nonstandard-model or PA194 machine reduction.

To rebuild the entire prerequisite chain from the repository root, set
`IPRA_FOUNDATION_OVERLAY` to the audited current Foundation overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-lk-search-primrec/check.sh`.
The script uses a temporary tmpfs directory by default.
