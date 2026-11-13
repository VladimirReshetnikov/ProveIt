# Source-only boundary between page bytes and the historical iPRA endpoint

The original 14-variable/65-operation equation has a historically checked endpoint for a **normalized prefix-token transcription**, connected to the mapped Gödel–Gentzen translation of Foundation's ZFC consistency sentence. Its historical source and terminal evidence are described in [the translated endpoint record](../current14-quoted-translated-endpoint-check/README.md). The quoted theorem proves the existence of an internal standard-iPRA derivation of the biconditional; it does not prove either side. The record retains separate source/provider ancestry qualifications.

The precise additional source obligation isolated here is a **faithful page-to-token binding**. The existing `quoteSentence` consumes the hard-coded list `quoted`, not bytes read from `equation.tex` or `equation.pdf`. Historical independent comparison checked the transcription externally, but no retained Lean theorem says that a specified faithful interpretation of those physical files yields that token list. This is a document-association gap; it must not be confused with a missing theorem of ZFC consistency or with the already checked abstract normalized-quote endpoint.

`Current14TexTokenBoundary.lean.src` is an unelaborated proposal for the narrow client interface:

* `sentenceFromTokens lines` uses the same existing `compile`, `initial linePorts`, `lookup`, positive shift and sentence constructor as the historical quote.
* `sentenceFromTokens_quoted` proposes their definitional equality at the existing fixed token list.
* `endpoint_if_quoted_tokens` assumes **explicitly** that a supplied byte extractor applied to supplied bytes returns exactly `quoted`, then proposes the translated-consistency endpoint for its constructed sentence.

The extractor is an arbitrary parameter. In particular, a constant function returning `quoted` satisfies the conditional premise without reading its argument. Therefore this client alone does **not** show any parser is faithful, that the bytes are the workspace TeX/PDF, or that the rendered document has the desired mathematical meaning. A substantive completion needs a specified restricted TeX grammar and faithful extraction/semantics theorem, an exact byte association for the chosen input, and a checked proof that extraction produces the 23 named token lines. Standard TeX is an extensible programming language; a restricted accepted fragment must specify how macros, grouping, exponents, subtraction and implicit multiplication are interpreted. The PDF, if included in scope, additionally needs an explicit PDF/rendering interpretation or a separately disclosed external rendering check.

There is a **second independent page boundary**: the new constructor supplies the already defined `linePorts` and does not parse the page's decimal/floor/finite-set recipes or prove their semantics. The historical `linePorts_recipes` theorem relates those ports to formal recipe definitions, while the connection of those definitions to the external page remains a separate proof or external source audit. The 14 strictly positive variables are handled by the historical `positiveShift` in the constructed sentence; preservation of their printed ordering must likewise be part of any faithful extraction argument.

The draft's source checker pins the normalized quote, its compiler, both historical endpoint source files, the line-port endpoint source, the present TeX/PDF, and the proposed client. It compares the sentence-constructor text and checks the named source interfaces. It does not parse or interpret the page, execute Lean, check the draft, rerun historical objects, reauthenticate provider closure, or run `#print axioms`. The referenced proof environment, file identity at a future invocation, proof-source/compiled-object compatibility, and the disk-guarded coherent rebuild remain separate.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/current14-tex-token-boundary-client-draft/check.py | cmp - research/current14-tex-token-boundary-client-draft/receipt.json
```
