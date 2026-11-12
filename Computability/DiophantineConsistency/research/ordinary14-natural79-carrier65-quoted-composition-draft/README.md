# Natural-79 and the historical normalized Carrier65 quote

This inert `.lean.src` proposes a direct formal composition with the historical
**normalized quoted-sentence** endpoint. It does not use the distinct
Carrier65 expression at the direct BFS943 ports. No Lean elaboration or joint
provider build has been run; the source draft is not a proved result.

Write `S` for `IPRAStandardTheory.standardTheory`, `N79` for the natural-79
native no-zero sentence, `Q` for the value of the historical `quoteSentence`,
and `R` for `mappedNativeRefutation embedding`. The selected unelaborated
natural-79 endpoint states `S ⊢ N79 ↔ ∼R`. The historically staged prefix
source states `∃ Q, quoteSentence = some Q ∧ S ⊢ Q ↔ ∼R`. Its staged terminal
[review](../../reviews/current14-seed-readable-prefix-staged-terminal-independent/README.md)
reports the historical run passed, subject to its retained provider evidence.
The proposed `standard_common_target` composes these two biconditionals in
both directions, and `quoted_standard_equivalence` applies it. This would
establish existence of an internal iPRA derivation of `N79 ↔ Q`, not a proof of
either side. The exact shared target is the selected Foundation proof
predicate; no independently specified Con(ZFC) code is silently substituted.

A second proposed theorem uses the later historically checked
[translated endpoint](../current14-quoted-translated-endpoint-check/README.md)
`Q ↔ C`, with `C = (Semiformula.lMap embedding sourceSentence)ᴺ`.
`sourceSentence` is Foundation's ZFC-with-choice consistency sentence;
`IPRABoundedRhoZFC.zfcEquiv` supplies `C ↔ ∼R` in the native presentation,
and `IPRAStandardTheory.provable_iff` transfers that derivability to `S`.
Both paths are intuitionistic biconditional composition and require no
unjustified elimination of double negation. The optional reference theorem
uses the existing order-erasure conversion for both formulas.

The historical quote is normalized Lean token data externally compared with
the maintained page; the historic theorem does not parse raw `equation.tex`
or PDF bytes and does not establish a formal interpretation of their
rendering. The 79 source uses compact symbolic ports, and no syntactic or
coefficient identity with the quote is asserted. Composition would also need
a coherent checked environment combining the 79 overlay with the historical
quote provider; source names and historical result records alone do not prove
provider compatibility. The 79 endpoint, this client, axiom reports and the
joint composition remain unelaborated. Nothing here proves the external
consistency of ZFC or the iPRA theorem for either displayed equation.

`check_source.py` pins the exact source statements and draft, and checks the
relevant textual forms only. It does not parse, typecheck, execute `#print
axioms`, authenticate compiled objects or establish the proposed proof. From
the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-carrier65-quoted-composition-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-carrier65-quoted-composition-draft/result.json
```

An [independent source review](../../reviews/ordinary14-natural79-carrier65-quoted-composition-independent/README.md)
checks both proposed proof directions and the quote witness, without
elaborating the client or binding the raw TeX/PDF.
