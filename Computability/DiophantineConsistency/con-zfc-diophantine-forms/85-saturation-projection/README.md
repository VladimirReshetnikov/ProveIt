# Smaller Diophantine consistency equations

Prepared for Vladimir Reshetnikov, 23 October 2026.

**Start with `report.pdf` or `report.tex`.** This package contains completed
ordinary polynomial constructions, mathematical proofs, literal coefficient
data, exact arithmetic circuits, and reproducible checks.

Reviewed ProveIt commit: `c1a102936aca437e9999530a0111e6ddab56dc6d`.
The comparison includes all five ZIP archives present in `docs/incoming` at
that snapshot. Their immutable hashes are recorded in `provenance/BASELINE.json`.

## Completed equations

| Packet | Domain | Variables | Exact degree | Live binary operations |
|---|---|---:|---:|---:|
| `integer/transport18_degree88.json` | Unrestricted integers | **18** | **88** | **105** |
| `integer/transport19_degree32.json` | Unrestricted integers | **19** | **32** | **108** |
| `integer/transport20_degree20.json` | Unrestricted integers | **20** | **20** | **111** |
| `integer/transport21_degree16.json` | Unrestricted integers | **21** | **16** | **114** |
| `nine/saturated_positive.json` | Positive integers | **9** | **1,628,768** | **434** |
| `nine/saturated_natural.json` | Naturals, including zero | **9** | **1,628,768** | **441** |
| `nine/saturated_radical_positive.json` | Positive integers | **9** | **1,103,950** | **1,074** |
| `nine/saturated_radical_natural.json` | Naturals, including zero | **9** | **1,103,950** | **1,081** |

All intermediate registers are polynomial abbreviations, not hidden
existential variables. Every exponent in a witness polynomial is fixed.
Every live binary addition, subtraction and multiplication is charged,
including squaring and fixed-scalar multiplication; fixed integer leaves
and register reuse are free. These counts are not bit complexity.

The first four endpoints each save one unrestricted variable and four
operations at unchanged degree compared with their immediate incoming
predecessors. The short nine-positive endpoint improves the frozen
440-operation, degree-1,845,940 construction in both measures. The radical
endpoint improves the incoming 1,753-operation, degree-1,158,228 point in
both measures, using a different complete coherent coefficient tuple.

## Main mathematics

1. **Apply a known transport elimination to the new joint-sign family.**
   Replace alpha by C=q-F-alpha and solve the now-monic transport equation
   for F. This is a bijection of integer zero sets with polynomial inverse.
   Source 73 already contains the local method and is credited explicitly;
   the new contribution is the improved complete endpoint family.
2. **Saturate one Pell factor.** Replace
   `1+(A^2-1)D^2(iJC^2)^2` by `1+(A^2-1)D(iJC^2)^2`.
   The surrounding certificate already forces D to be a square. A new
   unbounded proof retains all rank congruences, and a finite-matrix-period
   argument supplies the reverse witnesses. This is not an unrestricted
   polynomial identity or an unjustified division of an integer witness.
3. **Bound the entire saturated radical.** A 333-term polynomial and its
   correction give a strict bound certified by 36,309 positive coefficients
   after a fixed translation. The uncorrected formal square-root truncation
   fails and is retained as a negative control.
4. **Separate direct-source research.** `alternative/` proves a coprime
   Fermat-label Horn-flow theorem, with a four-parameter, one-loop bounded
   source. Its full Diophantine closure is not compiled or counted. It is
   not included among the completed equations above.

## The exact consistency claim and its boundary

For each listed equation P and its declared domain D, the ordinary proof
composes the new transformations with the precisely named inherited
Pell/native/compiler and syntactic-refutation calibration proofs to give

    ZFC proves: (no x in D has P(x)=0) iff Con(ZFC).

The new projection, saturation theorem, majorants, and witness constructions
are supplied in full. The inherited semantic calibration is identified and
retained, rather than reproved in its entirety. This delivery does not add
an end-to-end Lean/Rocq certificate or finish the repository's encoded
object-language ZFC derivation. Exact arithmetic replay is not a proof of
those unbounded interfaces or a decision of consistency.

No global minimum or worldwide priority is claimed. The integer and positive
domains must not be conflated. The complete coefficient tuples used by
`integer/` and `nine/` differ and must be kept separate; MF is already shifted
in both.

## Reproduce

Only Python 3.10+ and its standard library are needed for release checks:

```sh
python3 verify.py
```

This authenticates retained sources, runs independent component algebra
checks normally and with Python optimization, reconstructs the complete
fixed coefficients, checks domains, exact-degree certificates, operation
counts and corruption controls, and runs the direct-source diagnostics.
The deterministic summary is `verification/RELEASE_CHECKS.json`.

Compile the report with a standard PDFLaTeX installation:

```sh
make pdf
```

After successful verification and PDF reconstruction, rebuild the complete
archive and its checksum manifest with:

```sh
python3 make_archive.py
```

The commands do not download dependencies or contact a remote repository.
Optional discovery and local component regeneration commands are documented
in the component READMEs. Exact and modular evaluation of the integer forms
is provided by `integer/evaluate.py`; all nine-variable graphs use the same
fully declared input and fixed-leaf convention.

## Package map

| Location | Contents |
|---|---|
| `report.tex`, `report.pdf`, `metrics.tex` | Complete integrated article and editable sources |
| `integer/` | Four equations, exact projections, six coefficient ports, finite recipes, independent verification |
| `nine/` | Four domain-specific graphs, saturation proof, full radical certificates, 1,294-digit native seed and fixed-leaf reconstruction |
| `alternative/` | Fermat-label proof source, full theorem, adversarial finite checks |
| `verification/` | Integrated receipts and separate mathematical review |
| `provenance/` | Reviewed snapshot, incoming archive pins, current formal-status documents |
| `MANIFEST.sha256` | Complete release file hashes |

The separate mathematical review was performed by another AI-assisted
research worker within this session, not an external human referee.

## Integration

Place this folder as a new research contribution alongside the existing
numbered reports. No directory number is reserved. Keep the fixed tuple
bindings, source hashes, and original notices intact. The archive does not
change the remote repository, remove earlier candidates, or imply that its
ordinary proofs have already been accepted into the formal development.

New material is offered under the accompanying MIT No Attribution license;
inherited material retains the notices and licenses supplied in the component
provenance folders.
