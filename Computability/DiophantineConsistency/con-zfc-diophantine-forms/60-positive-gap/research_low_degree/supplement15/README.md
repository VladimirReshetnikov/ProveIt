# A one-operation refinement of the fifteen-positive degree-24 equation

This supplement changes the source-58 polynomial from **90 to 89 live binary
arithmetic operations**, retaining **15 strictly positive integer unknowns**,
**exact total degree 24**, and an **unconditional affine bijection of its
positive zero set with the parent positive zero set**. The saving is one
operation, or about 1.11%; it is a small supplementary improvement, not a
new variable-count or degree result.

**Internal ZFC boundary:** the consistency corollary is conditional on
internalizing the inherited source calibration and arithmetic/compiler
correctness. The pinned repository's [OBJECT_ZFC.md](upstream/OBJECT_ZFC.md)
leaves both steps open. This supplement does not supply the requested
internal ZFC equivalence derivation.

The change is the positive coordinate shift `z_old = z + 1` and a factored
transport residual. The other five residuals are unchanged. The positivity
of the inverse shift follows from the inherited ordinary kernel and is
proved in [PROOF.md](PROOF.md). A polynomial identity alone would not justify
the change on the strictly positive domain.
The shift already appears in that inherited kernel; the present contribution
applies it to source 58's integral-root evaluator and certifies the saving.

| Quantity | Pinned source 58 | This supplement |
| --- | ---: | ---: |
| Strictly positive unknowns | 15 | 15 |
| Exact total degree | 24 | 24 |
| Shared residual evaluator | 79 operations | 78 operations |
| Single sum-of-squares evaluator | 90 operations | 89 operations |

Every binary addition, subtraction, and multiplication costs one operation,
including multiplication by a fixed scalar. Fixed integer leaves and
references to earlier gates are free. The revised evaluator uses 47
multiplications, 27 additions, and 15 subtractions. This metric does not
measure bit complexity or the storage cost of integer coefficients.

## Reproduce offline

Use Python 3.10 or later with its standard library:

```sh
python3 reproduce.py
```

This checks imported-source digests, rebuilds the four circuit packets,
requires byte-identical circuit regeneration, rebuilds the complete native
coefficient tuple, independently audits that tuple, and runs the exact
local checker both normally and with `python3 -O`. Receipts are in
`certificates/` and `native/INDEPENDENT_AUDIT.json`.

The local audit can also be run directly:

```sh
python3 verify.py
python3 -O verify.py
```

It imports no builder. It proves the transport and norm-cancellation
identities by exact polynomial arithmetic in free integer polynomial rings,
checks the literal circuit wiring and operation counts, and computes the
exact degree-24 leading form. Signed and actual-coefficient modular
evaluations provide additional transcription checks. Those finite
evaluations do not prove the unbounded existence equivalence.

At the all-one positive tuple the strong residual is 81, so the polynomial
is at least 6561. The all-one tuple is therefore **not a zero**, independently
of the fixed coefficient values.

## Complete fixed coefficient tuple

The primary equation is bound to the **whole compact source-44 tuple**,
exactly as source 58 is. Its ports are:

| Circuit port | Native payload | Bit length |
| --- | --- | ---: |
| `beta` | `native/coefficients/beta.bin.gz` | 590069 |
| `K0` | `native/coefficients/K.bin.gz` | 592884 |
| `MC` | `native/coefficients/MC.bin.gz` | 590069 |
| `MF` | `native/coefficients/MF_source.bin.gz` | 590070 |

Each gzip payload decompresses to an unsigned little-endian integer.
Here `beta = 2^590069 - 1` and `MF_source` is the already shifted source
port, not the unshifted native high mask. The four raw payloads total
295388 bytes; their compressed total is 9445 bytes in this distribution.
The binding, raw digests, literal K215 transition data, deterministic
builder, independent auditor, native proof, source files, and notices are
all included under `native/`. No port is borrowed from another tuple.

## Files and proof boundary

- [PROOF.md](PROOF.md) gives the full equation, the local two-way existence
  proof, exact degree and operation count, and inherited proof interface.
- [section.tex](section.tex) is a self-contained LaTeX section for inclusion
  in the main report; it requires the usual `amsmath` and `amssymb` packages.
- `circuits/p15_degree24_transport89.json` is the counted primary evaluator.
  Its 101-operation cancellation-expanded companion is solely a degree
  certificate and is not used in the 89-operation claim.
- `upstream/source58_report.tex` and `upstream/source58_p90.json` preserve
  the parent theorem and the exact original 90-operation evaluator.
  Historical report sources are provenance records, not standalone build
  targets for this supplement.
- `upstream/ORDINARY_KERNEL.md` supplies the transport positivity and
  ordinary Pell-kernel proof; `upstream/PELL_LEMMAS.md` supplies the
  inherited Pell lemmas. The compact native adapter is in `native/PROOF.md`.
- `upstream/OBJECT_ZFC.md` preserves the pinned repository's current
  object-language status, including the open internal source calibration
  and arithmetic/compiler correctness obligations.
- `PROVENANCE.json` fixes the retrieval snapshot and digests of the imported
  files. Historical source pins inside inherited files are preserved.

The new local reduction is elementary algebra and positive-domain reasoning.
It preserves any internally established consistency calibration of the
parent equation. Establishing that calibration requires the inherited
source and compiler arguments for the internal natural numbers of every
ZFC model, or corresponding object-language derivations. External
equivalences and numeral agreement do not discharge those obligations.
Historical claims in the preserved parent documents are not treated as
evidence that this internal derivation has been completed. The scripts do
not decide consistency, search for a refutation, or certify a global minimum.

