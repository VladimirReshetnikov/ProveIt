# Rebase the first Pell index at its available modulus

Four explicit ordinary integer polynomials for syntactic ZFC inconsistency,
prepared with AI assistance for Vladimir Reshetnikov / ProveIt, 25 October
2026. Start with `PROOF.md`; `report_section.tex` is a manuscript inclusion.

| Complete circuit | Domain | Unknowns | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| `integer14_degree82.json` | unrestricted integers | 14 | 82 | 113 |
| `integer14_degree90.json` | unrestricted integers | 14 | 90 | 111 |
| `integer13_degree152.json` | unrestricted integers | 13 | 152 | 126 |
| `integer11_degree298.json` | unrestricted integers | 11 | 298 | 150 |

Every intermediate node is a polynomial abbreviation. Only the ordered
`variables` field supplies unknowns. Every coefficient leaf is bound to
complete fixed bytes and a finite reconstruction in `coefficients/`.
All arithmetic gates are binary addition, subtraction or multiplication;
squaring and fixed scalar multiplication count. Circuit length is not a
claim about bit complexity or a lower bound on intrinsic complexity.

The ordinary theorem is that ZFC proves absence of integer zeros equivalent
to Con(ZFC), composing the new proof with the explicit inherited
native/compiler/refutation calibration. The new unbounded lemma uses
`XY^2` as the first-index modulus, permitting a magnitude budget with `q^6`
in place of `q^8`. The eleven-variable circuit adds a further integral
center term to exploit the decreased budget degree.

The matched incoming degree/operation pairs were 86/112, 94/110, 156/125
and 300/148. The results lower degree at small extra operation cost. No
global minimum, proof of consistency, independent human review, or new
end-to-end Lean/Rocq/object-ZFC certificate is claimed.

## Reproduce without a network

Python 3.10+ and the standard library suffice:

```sh
python3 -B build.py --check
python3 -B check.py
python3 -B -O check.py
```

All three commands are read-only by default. To retain a fresh verification
receipt, add `--receipt /path/out.json` to a checker command. `CHECK.json`
and `CHECK_OPTIMIZED.json` contain the performed release checks.

The checker does not import the producer. It reconstructs all six fixed
coefficients, authenticates inherited source bytes, binds every arithmetic
gate against independent polynomial register definitions, proves exact
degrees at the authentic fixed coefficients, and rejects changed index,
budget and center formulas. `center_remainder.json` records every
coefficient of the degree298 cancellation calculation. These are finite
artifact checks; the unbounded arithmetic proof remains `PROOF.md`.

## Files and provenance

The comparison snapshot is ProveIt commit
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`. Immediate mathematical parents
are the `roots/` part of
`docs/incoming/ConZFC_Residual_Bases_Denominator_Engineering_2026-10-25.zip`
and the `scalar/` part of
`docs/incoming/ConZFC_Shared_Certificates_Round18_2026-10-25.zip`.

`SOURCE_PINS.json` authenticates the copied source proof, coefficient, and
parent-equation closure. The inherited copies preserve their own licenses
and notices. The two proof chains remain explicit: the changed guard is
not asserted to imply the old stronger guard at arbitrary zeros; soundness
rejoins the earlier B0-only source after recovering the cubic scale.

No upstream repository file, branch, issue, pull request or remote state was
changed. This component is intended for integration with the accompanying
research report.
