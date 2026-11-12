# Independent review: physical bindings for natural-82 and natural-86

The [physical-binding audit](../../research/ordinary14-natural82-86-physical-binding-audit/README.md) accurately distinguishes the compact symbolic tuple used by the new endpoint drafts from the canonical Carrier65 display, within its stated source and byte scope. Both its receipt and the independent receipt below reproduce. Neither is a Lean theorem about files, a PDF interpretation, or an equivalence proof.

The current TeX says `rho=2^47`, `B=rho^2011`, `beta=B-1`, so its beta is `2^94517-1`. The compact Lean definition says `betaNat=2^(67*8807)-1`, or `2^590069-1`. The two numerals are unequal. The current metadata identifies the displayed artifact as the 14-positive-input, 65-operation, degree-150 Carrier65 equation; the two proposed natural-input graphs instead use the compact tuple. The metadata's TeX/PDF digests were rechecked, but a digest does not verify a rendering or establish a formula's semantics. The graph and numeral distinction alone does **not** imply that the separate no-zero sentences are inequivalent.

The cited Lean sources do state that `decode_ports` decodes four closed lists to `[betaNat, paramKernel rho, lowNat, betaNat+highNat]`, and that `byteP_eq` identifies the integer cast of those decoded lists with the symbolic tuple. The natural86 adapter proposes rewriting its expression with that equality. These are source declarations, and the adapter and endpoint have not been elaborated together. None states that Lean has read or authenticated the filesystem's compressed bytes.

The independent checker extracts the two exponents from the TeX and Lean sources, checks the metadata hashes, examines the stated source declarations and endpoint graph references, and separately decompresses all four physical payloads using zlib's gzip mode. It verifies their lengths and raw/gzip SHA-256 values against the two recorded bindings and checks that the compact beta bytes decode as `2^590069-1` in minimal unsigned little-endian encoding. It confirms that the recorded MF payload is already shifted; that convention is not a proof that any arbitrary file agrees with the closed Lean recipe. This check does not independently evaluate the three other Lean byte recipes.

To connect the new expressions to the displayed Carrier65 equation, both expression-to-data/file associations and a checked comparison of the corresponding encoded no-zero statements are needed. If their endpoint theorems use the same precisely matched iPRA consistency sentence, they could be composed there; if their sentences or theories differ, a translation is also needed. Nothing in this review establishes such a chain, provider compatibility, iPRA derivability, or PDF fidelity.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural82-86-physical-binding-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural82-86-physical-binding-independent/result.json
```
