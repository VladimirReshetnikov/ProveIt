# Independent review of the proposed normalized-quote composition

The [source draft](../../research/ordinary14-natural79-carrier65-quoted-composition-draft/README.md)
has the intended source-level statements and constructive implication
directions. The author's checker and this independent checker reproduce. This
is not Lean elaboration, provider authentication, an axiom audit or an iPRA
proof certificate.

Write `A` for natural-79 no-zero, `B` for the historical quote sentence, `R`
for `∼mappedNativeRefutation embedding`, and `C` for the mapped native
translation of Foundation's chosen ZFC consistency sentence. The historical
prefix source states that some `B` satisfies `quoteSentence = some B` and
standard-theory derivability of `B ↔ R`. Its exact definition takes the
normalized `quotedExpr linePorts`, applies `positiveShift`, and encodes its
native no-zero formula. The historical translated source states the same
option equality with derivability of `B ↔ C`. Both source proofs explicitly
choose `displayedNoZero` and the same `quoteSentence_eq`; independently, the
`Option` equality makes any two witnesses equal. The direct and translated
client theorems each carry forward the very witness and equality they obtain;
no comparison of unrelated existential witnesses is needed.

The direct helper composes `A → R → B` and `B → R → A`. The translated helper
uses `A ↔ R`, `C ↔ R`, and `B ↔ C` to compose `A → R → C → B` and
`B → C → R → A`. The inspected Foundation definitions make biconditional a
conjunction of implications; the cited projections and transitivity have the
expected directions. No double-negation elimination or classical inference
appears in these source compositions. The `C ↔ R` bridge is transferred from
the native theory using the `.2` direction of `standardTheory ⊢ φ ↔
nativeTheory ⊢ φ`.

The reference draft keeps the same witness and quote equality. It transfers
the standard derivation to native theory via `.1` and invokes
`nativeToReference`, which concludes derivability of the **erased whole
formula**. The inspected erasure source preserves conjunction and implication;
the draft relies on Lean recognizing the corresponding reduction for
biconditional. Actual reduction, name/instance resolution and all proof bodies
remain unchecked here.

The historical terminal-review records concern normalized Lean token data and
selected providers. They do not make a Lean theorem interpreting TeX/PDF bytes,
and this new comparison does not establish coefficient identity with
natural-79. In particular, the two earlier Carrier65 direct-BFS and displayed
2011 port choices are distinct. The natural-79 endpoint and joint provider
environment are unelaborated, and all five `#print axioms` commands in the new
draft are unexecuted. Thus neither route establishes the intended equation
comparison or a proof of consistency until its separate obligations are met.

From the repository root with the retained guarded Foundation source present:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-carrier65-quoted-composition-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-carrier65-quoted-composition-draft/result.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-carrier65-quoted-composition-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-carrier65-quoted-composition-independent/result.json
```
