# Source and artifact review of the byte-port model equivalence

The successful source defines each integer port by **first decoding its Lean
byte recipe in `ℕ`, then casting to `ℤ`**. Its `byteP_eq` theorem uses the
four-port natural decoding equality pointwise under that cast. The tuple order
is beta, K, MC, MF; the fourth symbolic component is `betaNat + highNat`,
with the beta shift applied once. Rewriting by this equality transfers the
previous retained-expression model theorem to the exact byte-recipe tuple.

The resulting `shifted_model_iff` is quantified over a type with an
`ORingStructure` instance satisfying `IΣ₁`. It equates a model-natural zero of the
generated 12-variable Lean expression after the adaptive `x ↦ x + 1`
substitution with a machine halt **inside that model**. It is a two-way
model-level statement, including nonstandard models; it is not itself a
Lean proof of an iPRA derivation or an assertion that the machine actually
halts or does not halt.

The first Lean join attempt used `(Nat.ofDigits ... : ℤ)`. Because
`Nat.ofDigits` is semiring-polymorphic, that decoded directly in `ℤ` rather
than casting a natural decode, and the compiler rejected the proposed cast
equality. The reviewer initially missed this elaboration distinction. The
failed source and log are retained by the author under `attempt02`; their
error-recovery `sorryAx` reports are not proof evidence. The successful
`attempt03` source explicitly writes `((Nat.ofDigits ... : ℕ) : ℤ)`.

This review checks the successful source, log and live output object, its two
named Lean metatheory reports, and the two predecessor sources, objects,
receipts, logs and direct guards. It independently re-inventories the 109
model-provider roots (10,751 recorded files), rechecks the byte provider and
prior recorded producer guards, and reconstructs the selected union. The
1,286 selected files and 9,981 overlap events match the manifest; no
conflicting shared file or suppressed foreign companion was found. These are
point-in-time checks of the selected providers, not a fresh Lean replay or a
complete authentication of inherited project, package or dynamic ancestry.

The four lists are closed **Lean recipes**. Their transcription from retained
parent files, filesystem contents, gzip decompression, the parent/supplement
relationship, and any PDF transcription remain external provenance
boundaries. The generic adapter to iPRA still requires a coherent provider
join; the result reviewed here does not establish that endpoint.

[`audit.py`](audit.py) performs the read-only source and artifact checks;
[`capture.py`](capture.py) records their output and terminal receipt in
[`observations`](observations/). Repeating the review requires the live `/tmp`
providers. No further mismatch was found within the stated scope.
