# Positive-shift syntax, free-J graph and displayed-file boundary

This is a source/file inspection and one external finite checker run. It is
not a Lean replay, byte-to-expression theorem, PDF parser verification,
coefficient binding or an iPRA proof.

Subsequent work established a [Lean equality for all four symbolic byte
recipes](../compact44-four-port-byte-assembly2/README.md) and a separate
[model equivalence using those recipes](../compact44-byte-ports-model-iff-prototype/README.md).
The supplement's missing binding, payloads and other manifest-pinned files
have also been [restored and externally checked](../supplement-pinned-restoration/README.md)
against the retained parent package. These later results do not formalize
JSON, gzip or filesystem bytes in Lean and do not identify a displayed PDF.

The all-model result uses `Ordinary12FreeJ.literal p`, an **unshifted**
`Expr (Fin 12)` for the 95-operation free-J graph, with strictly positive
model coordinates. Its exact symbolic tuple is `p = ![betaNat,
paramKernel rho, lowNat, betaNat+highNat]`, pointwise cast to integer
expression constants. The source SHA-256 is
`542bb6913f5b7e6d1ef3cd9e430fcbee20ee727966d3bfc9f2b6d71c566ef96a`.
The external `free-j-prototype/check_graph.py`, SHA-256
`80a76a8fc392f470a56cc00ea45108f15f9b82b882c8356068fc22030ea3e5c0`,
compares its 95 source rows, 12 variable positions and four port positions
against `con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json`,
whose SHA-256 is
`2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22`.
The actual command `python3 -I -B .../free-j-prototype/check_graph.py`
exited 0 with `PASS_FREE_J_GRAPH 95 rows 12 free variables 4 ports 4
mutations rejected`. This confirms that particular external source/JSON
comparison; it is not a theorem in Lean about JSON, its coefficient payloads,
or a rendered PDF.

The generic adapter uses the **qualified**
`DiophantineConsistency.AdaptiveEquationSyntax2011.positiveShift`, defined
by substituting `var i + 1` for every variable of the unshifted expression.
Its theorem `internalZero_positiveShift` proves, over a commutative
semiring, that evaluation at a natural model vector `x` gives an internal
zero exactly when the original expression has an internal zero at `x+1`.
That is why the adapter's unrestricted natural-domain no-zero sentence
corresponds to the original graph's strictly positive domain. The source
`AdaptiveEquationSyntax2011.lean` has SHA-256
`f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6`.
This is a syntactic substitution, not evidence that a printed document uses
the substituted expression verbatim. The generic adapter source has SHA-256
`4faabe0a42f1adabe102e58c4355ddbdf03f9c0ccb29498c48c99241066356ea`.

There is also a **different** function named
`DiophantineConsistency.Expr.positiveShift` in `PositiveDomain.lean`: it
substitutes `var i - 1` to convert a natural-domain expression to a
positive-integer-domain expression. Its direction is opposite to the
adapter's function. The source has SHA-256
`8e57faa7047f8493cb73f228aee6122856647d86efe749d436017a9718b83ae7`.
A proof or printed formula must specify which qualified definition is meant.

At this workspace snapshot `equation12.tex` is not the 12-variable free-J
candidate: its first page explicitly displays **26 positive variables**,
degree 12 and a 124-operation circuit with radix `2^47` and period 2011.
The first page extracted by `pdftotext` from `equation12.pdf` has the same
26-variable heading. The TeX and PDF hashes are respectively
`b65a5665ceffab2fdeaf1f69180f1422fe56c6492d8f6919000c57e48816b0b3` and
`07eee9f4ed61cf2f7ceaf0cfc9e79b49620f71ed85e7b2b15796bee4e4a3e647`.
This is an external inspection, not a formal TeX/PDF equality proof.
`equation.tex` and `equation.pdf` instead currently display the separate
14-positive-variable, 65-operation, degree-150 equation. Their respective
hashes are `94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635`
and `23a52933980352f83a19c21a0d6f349594be5f85edc85a462e25ffc83c7fd5d6`.
Neither displayed equation is thereby identified with the 95-row graph.

The 95-row graph's JSON lists domain “strictly positive integers”, the same
12 witnesses, four port names, and a coefficient-binding file. The older
`candidates/free-j-polarized-positive/equation.json` is instead the
96-operation parent; its SHA-256
`2a8da9ac141de5078fbdca96acccab5a7c44f6b39f4bc6063261b29179cb68be`
matches the 95-row JSON's recorded parent hash. This is an external graph
ancestry observation. The later restoration re-establishes, by the frozen
supplement manifest and repeated external checks, that the child's restored
binding and compressed files are byte-identical to the retained parent
package. The checked Lean port theorem is about closed recipes, and the
recipe-to-file/transcription relationship remains external. A separately
specified checked TeX/PDF transcription or an explicit external provenance
boundary is still needed before attributing the model result or a future
iPRA theorem to a particular delivered PDF.
